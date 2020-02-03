export NLDS, updatemaxncuts!

# π, σ and ρ do not really make sense alone so only
# their product will T, h, d, e is stored
mutable struct Solution <: SOI.AbstractSolution
    status::Symbol
    objval
    objvalx
    objvalxuray
    x
    xuray # unbouded ray
    θ
    θuray # unbouded ray
    πT
    πh
    σd
    ρe
    function Solution(status::Symbol, objval)
        new(status, objval, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing, nothing)
    end
end

# Feasibility cut
# D = π T
# d = π h + σ d
function SOI.feasibility_cut(sol::Solution)
    (sol.πT, sol.πh + sol.σd)
end

# Optimality cut
# E = π T
# e = π h + ρ e + σ d
function SOI.optimality_cut(sol::Solution)
    (sol.πT, sol.πh + sol.σd + sol.ρe)
end

SOI.getstatus(sol::Solution) = sol.status

SOI.getobjectivevalue(sol::Solution) = sol.objval

SOI.getnodeobjectivevalue(sol::Solution) = sol.objvalx

SOI.getnodevalue(sol::Solution) = sol.x

function SOI.getbellmanvalue(sol::Solution, i)
    sol.θ[i]
end

# Nested L-Shaped Decomposition Subproblem (NLDS)

# Primal
# min c x
#     + θ                         -> AvgCutGenerator
#     + sum θ_i                   -> MultiCutGenerator
#     + λ c_a x_a                 -> parent unbounded
#     h -   Tx_a - Wx ∈ K         -> parent bounded
#     h - λ Tx_a - Wx ∈ K         -> parent unbounded
#     Dx >= d                     (feasibility cuts)
#     Ex + θ   >= e               -> AvgCutGenerator
#     Ex + θ_i >= e               -> MultiCutGenerator
#     x in C
#     λ >= 0

# Note that we do not have θ >= 0

# Dual
# max π h + σ d + ρ e
#     - π Tx_a                    -> parent bounded
#     c - (π W + σ D + ρ E) ∈ C^* -> x dual
#     c_a x_a - π Tx_a >= 0       -> parent unbounded
#     π in K^*
#     1'ρ = 1 (or <= 1 if θ >= 0)
#     σ >= 0
#     ρ >= 0
mutable struct NLDS{S}
    model::ParametrizedModel

    # parent solution
    x_a::AbstractVector{S}
    xuray_a::Union{Nothing, AbstractVector{S}}
    objvalxuray_a::Union{Nothing, S}

    childFC::Vector{CutStore{S}}
    childOC::Vector{CutStore{S}}
    localFC::CutStore{S}
    localOC::CutStore{S}
    proba::Vector{Float64}
    θfree::BitSet
    θlb::Vector{Float64}
    childT::Union{Nothing, Vector{AbstractMatrix{S}}}
    cutgen::AbstractOptimalityCutGenerator

    nx::Int
    nθ::Int
    nπ::Int
    πs::Vector{Int}
    # Number of feasibility cuts
    nσ::Int
    # Location of each feasibility cut in the constraint matrix
    σs::Vector{Int}
    # Number of Optimality Cuts for each θ_i
    nρ::Vector{Int}
    # Location of each optimality cut in the constraint matrix
    ρs::Vector{Vector{Int}}

    model
    loaded
    solved
    prevsol::Union{Nothing, Solution}

    newcut::Symbol
    pruningalgo::AbstractCutPruningAlgo
    FCpruner::AbstractCutPruner
    OCpruners::Vector

    function NLDS{S}(param_model::StructJuMP.ParametrizedModel, solver, pruningalgo::AbstractCutPruningAlgo, newcut::Symbol=:AddImmediately) where S
        nx = length(param_model.variable_map)
        nθ = 0
        localFC = CutStore{S}(nx)
        localOC = CutStore{S}(nx)
        FCpruner = CutPruner{nx, S}(pruningalgo, :≥)
        OCpruners = typeof(FCpruner)[]
        if false
            model = MathProgBase.ConicModel(solver)
        else
            model = MathProgBase.LinearQuadraticModel(solver)
        end
        nlds = new{S}(param_model, S[], nothing, nothing, CutStore{S}[], CutStore{S}[], localFC, localOC, Float64[], BitSet(), Float64[], nothing, AvgCutGenerator(), nx, nθ, 1:nπ, 0, Int[], Int[], Vector{Int}[], model, false, false, nothing, newcut, pruningalgo, FCpruner, OCpruners)
        addfollower(localFC, (nlds, (:Feasibility, 0)))
        addfollower(localOC, (nlds, (:Optimality, 1)))
       nlds
    end
end

function add_childT!(nlds, childT)
    if childT === nothing
        @assert nlds.childT === nothing
    else
        # If there isn't any child yet, node.childT is null
        if nlds.childT === nothing
            nlds.childT = [childT]
        else
            push!(nlds.childT, childT)
        end
    end
end

function add_scenario_transition!(nlds::NLDS{S}, childFC, childOC, proba, childT) where {S}
    push!(nlds.proba, proba)
    oldnθ = nlds.nθ
    nlds.nθ = nθ(nlds.cutgen, nlds.proba)
    Δθ = nlds.nθ - oldnθ
    push!(nlds.θlb, 0)
    push!(nlds.θfree, length(nlds.θlb))
    if !iszero(Δθ)
        @assert Δθ == 1
        push!(nlds.nρ, 0)
        push!(nlds.ρs, Int[])
        # θ ≧ max β - ⟨a, x⟩
        # so we give :Max and set lazy_minus to true because it is "- ⟨a, x⟩" and not "+ ⟨a, x⟩"
        push!(nlds.OCpruners, CutPruner{nlds.nx, S}(nlds.pruningalgo, :Max, true))
    end
    @assert length(childFC.b) == 0
    addfollower(childFC, (nlds, (:Feasibility, length(nlds.childFC)+1)))
    push!(nlds.childFC, childFC)
    @assert length(childOC.b) == 0
    addfollower(childOC, (nlds, (:Optimality, length(nlds.childOC)+1)))
    push!(nlds.childOC, childOC)
    add_childT!(nlds, childT)
end

function setprobability!(nlds::NLDS, i, proba)
    nlds.proba[i] = proba
end

function getobjectivebound(nlds::NLDS)
    if !isempty(nlds.θfree)
        return -Inf
    end
    for (cone, idxs) in nlds.C
        for i in idxs
            if (cone == :NonNeg && nlds.c[i]  < 0) ||
               (cone == :NonPos && nlds.c[i]  > 0) ||
               (cone == :Free   && nlds.c[i] != 0)
               return -Inf
           end
        end
    end
    return Eθlb(nlds)
end
function setθbound!(nlds::NLDS, i, θlb)
    if isfinite(θlb)
        delete!(nlds.θfree, i)
        nlds.θlb[i] = θlb
    end
end
# Returns the lower bounds and cones for θ
function θC(nlds::NLDS)
    if nlds.nθ == length(nlds.θlb)
        # Multi cut
        θlb = nlds.θlb
        if length(nlds.θfree) < nlds.nθ
            bounded = collect(setdiff(BitSet(1:nlds.nθ), nlds.θfree))
            θC = [(:NonNeg, collect(nlds.nx .+ bounded))]
            if !isempty(nlds.θfree)
                free = collect(nlds.θfree)
                push!(nlds.θC, (:Free, collect(nlds.nx .+ free)))
            end
        else
            θC = [(:Free, collect(nlds.nx .+ (1:nlds.nθ)))]
        end
    elseif nlds.nθ == 1
        # Averaged cut
        if isempty(nlds.θfree)
            θlb = [dot(nlds.proba, nlds.θlb)]
            θC = [(:NonNeg, [nlds.nx + 1])]
        else
            θlb = [0.]
            θC = [(:Free, [nlds.nx + 1])]
        end
    else
        θlb = Float64[]
        θC = Tuple{Symbol, Vector{Int}}[]
    end
    θlb, θC
end

function updatemaxncuts!(nlds::NLDS, maxncuts, i)
    if i == 0
        nlds.FCpruner.maxncuts = maxncuts
    else
        nlds.OCpruners[i].maxncuts = maxncuts
    end
end

# .=== doesn't work :(
function veceqeqeq(v::Vector, x)
    map(el->el === x, v)
end

function padfcut(nlds::NLDS, D::AbstractMatrix{S}) where S
    if nlds.nθ > 0
        [D spzeros(size(D, 1), nlds.nθ)]
    else
        D
    end
end

function getfeasibilitycuts(nlds::NLDS)
    function f(i)
        D = nlds.childFC[i].A
        if nlds.childT !== nothing
            D = D * nlds.childT[i]
        end
        D
    end
    cuts_D = Compat.reduce(vcat, map(i -> f(i), 1:length(nlds.childFC)), init=nlds.localFC.A)
    cuts_d = Compat.reduce(vcat, map(x -> x.b, nlds.childFC), init=nlds.localFC.b)
    mycut = Compat.reduce(vcat, map(x -> veceqeqeq(x.authors, nlds), nlds.childFC), init=veceqeqeq(nlds.localFC.authors, nlds))
    (cuts_D, cuts_d, mycut)
end

# see https://github.com/JuliaLang/julia/issues/16661
function padmultiocutaux(nlds::NLDS, E::AbstractMatrix{S}, i, onesvec) where S
    nrows = size(E, 1)
    [E spzeros(S, nrows, i-1) onesvec spzeros(S, nrows, nlds.nθ-i)]
end
function padmultiocut(nlds::NLDS, E::AbstractMatrix{S}, i) where S
    nrows = size(E, 1)
    padmultiocutaux(nlds, E, i, ones(S, nrows, 1))
end
function padmultiocut(nlds::NLDS, E::AbstractSparseMatrix{S}, i) where S
    nrows = size(E, 1)
    padmultiocutaux(nlds, E, i, sparse(ones(S, nrows, 1)))
end

function padavgocut(nlds::NLDS, E::AbstractMatrix{S}) where S
    nrows = size(E, 1)
    [E ones(S, nrows)]
end
function padavgocut(nlds::NLDS, E::AbstractSparseMatrix{S}) where S
    nrows = size(E, 1)
    [E sparse(ones(S, nrows))]
end

function getoptimalitycuts(nlds::NLDS{S}) where S
    function f(i)
        E = nlds.childOC[i].A
        if nlds.childT !== nothing
            E = E * nlds.childT[i]
        end
        padmultiocut(nlds, E, i)
    end
    if nlds.nθ == 1
        cuts_E = padavgocut(nlds, nlds.localOC.A)
    else
        cuts_E = spzeros(S, 0, nlds.nx + nlds.nθ)
    end
    if nlds.nθ == length(nlds.childOC)
        cuts_E = Compat.reduce(vcat, map(f, 1:length(nlds.childOC)), init=cuts_E)
    end
    cuts_e = Compat.reduce(vcat, map(x -> x.b, nlds.childOC), init=nlds.localOC.b)
    mycut = Compat.reduce(vcat, map(x -> veceqeqeq(x.authors, nlds), nlds.childOC), init=veceqeqeq(nlds.localOC.authors, nlds))
    (cuts_E, cuts_e, mycut)
end


function notifynewcuts(nlds::NLDS{S}, A::AbstractMatrix{S}, b::AbstractVector{S}, attrs, authors::Vector{NLDS{S}}) where S
    @assert attrs[1] in [:Feasibility, :Optimality]
    isfc = attrs[1] == :Feasibility
    nnewcuts = size(A, 1)
    i = attrs[2]
    if i > 0 && nlds.childT !== nothing
        A = A * nlds.childT[i]
    end
    # No .=== :(
    mine = [authors[i] === nlds for i in 1:length(authors)]
    if isfc
        pruner = nlds.FCpruner
    else
        pruner = nlds.OCpruners[i]
    end
    ncur = ncuts(pruner)
    addstatus = addcuts!(pruner, A, b, mine)
    npushed = sum(addstatus .> ncur)
    @assert ncur + npushed == ncuts(pruner)
    cur = nlds.nσ + sum(nlds.nρ)
    if isfc
        nlds.nσ += npushed
        is = nlds.σs
    else
        nlds.nρ[i] += npushed
        is = nlds.ρs[i]
    end
    append!(is, zeros(Int, npushed))
    for j in 1:nnewcuts
        if addstatus[j] > ncur
            cur += 1
            is[addstatus[j]] = cur
        end
        if addstatus[j] > 0 && nlds.loaded
            if 1 <= addstatus[j] <= ncur || nlds.newcut == :InvalidateSolver
                # Need to update cut
                nlds.loaded = false
                nlds.solved = false
            elseif nlds.newcut == :AddImmediately
                idx = collect(1:nlds.nx)
                a = A[j,:]
                if !isfc
                    if i == 0
                        push!(idx, nlds.nx+1)
                    else
                        push!(idx, nlds.nx+i)
                    end
                    a = _veccat(a, one(S), true)
                end
                _addconstr!(nlds.model, idx, a, b[j], :NonPos)
                nlds.solved = false
            else
                error("Invalid newcut option $(nlds.newcut)")
            end
        end
    end
    @assert nlds.newcut == :InvalidateSolver || cur == nlds.nσ + sum(nlds.nρ)
    checkconsistency(nlds)
end

function checkconsistency(nlds)
    @assert length(nlds.πs) == nlds.nπ
    @assert length(nlds.σs) == nlds.nσ
    for i in 1:nlds.nθ
        @assert length(nlds.ρs[i]) == nlds.nρ[i]
    end
    ρs = Compat.reduce(append!, nlds.ρs, init=Int[])
    @assert sort([nlds.πs; nlds.nπ .+ nlds.σs; nlds.nπ .+ ρs]) == collect(1:(nlds.nπ + nlds.nσ + sum(nlds.nρ)))
end

function getrhs(nlds::NLDS{S}) where S
    checkconsistency(nlds)
    bs = [nlds.h - nlds.T * nlds.x_a]
    Ks = [nlds.K]
    Kcut = []
    cur = 0
    b = S[]
    if !isempty(nlds.FCpruner)
        append!(b, nlds.FCpruner.b)
        nlds.nσ = ncuts(nlds.FCpruner)
        nlds.σs = cur .+ (1:nlds.nσ)
        cur += ncuts(nlds.FCpruner)
        push!(Kcut, (:NonPos, nlds.σs))
    end
    for i in 1:nlds.nθ
        if !isempty(nlds.OCpruners[i])
            append!(b, nlds.OCpruners[i].b)
            nlds.nρ[i] = ncuts(nlds.OCpruners[i])
            nlds.ρs[i] = cur .+ (1:nlds.nρ[i])
            cur += ncuts(nlds.OCpruners[i])
            push!(Kcut, (:NonPos, nlds.ρs[i]))
        end
    end
    if !isempty(Kcut)
        push!(bs, b)
        push!(Ks, Kcut)
    end
    checkconsistency(nlds)
    bs, Ks
end

function setparentx(nlds::NLDS, x_a::AbstractVector, xuray_a, objvalxuray_a)
    nlds.x_a = x_a
    unbounded_a = xuray_a !== nothing
    if nlds.xuray_a !== nothing || unbounded_a
        # FIXME do better when delvars!, ... are available in MPB
        nlds.loaded = false
        nlds.solved = false
    end
    if unbounded_a
        nlds.xuray_a = xuray_a
        nlds.objvalxuray_a = objvalxuray_a
    elseif nlds.xuray_a !== nothing
        nlds.xuray_a = nothing
        nlds.objvalxuray_a = nothing
    end
    if nlds.loaded
        if unbounded_a
            nlds.loaded = false
        else
            bs, Ks = getrhs(nlds)
            _setconstrB!(nlds.model, bs, Ks)
        end
        nlds.solved = false
    end
end

function computecuts!(nlds::NLDS)
    nlds.nπ = length(nlds.h)
    nlds.πs = collect(1:nlds.nπ)
    cuts_D, cuts_d, mycut_d = getfeasibilitycuts(nlds)
    cuts_D = padfcut(nlds, cuts_D)
    cuts_E, cuts_e, mycut_e = getoptimalitycuts(nlds)
    # I will add the cuts in notifynewcuts! now
    noneedstored!(nlds.localFC, nlds)
    for store in nlds.childFC
        noneedstored!(store, nlds)
    end
    noneedstored!(nlds.localOC, nlds)
    for store in nlds.childOC
        noneedstored!(store, nlds)
    end
end

function getcutsDE(nlds::NLDS{S}) where S
    checkconsistency(nlds)
    nc = nlds.nσ + sum(nlds.nρ)
    A = spzeros(S, nc, nlds.nx + nlds.nθ)
    if !isempty(nlds.FCpruner)
        A[nlds.σs, 1:nlds.nx] = nlds.FCpruner.A
    end
    for i in 1:nlds.nθ
        if !isempty(nlds.OCpruners[i])
            A[nlds.ρs[i], 1:nlds.nx] = nlds.OCpruners[i].A
            A[nlds.ρs[i], nlds.nx .+ i] .= 1
        end
    end
    A
end

function load!(nlds::NLDS{S}) where S
    if !nlds.loaded
        bigA = nlds.W
        if nlds.nθ > 0
            bigA = [bigA spzeros(size(bigA, 1), nlds.nθ)]
        end
        if nlds.xuray_a !== nothing
            bigA = [bigA nlds.T * nlds.xuray_a]
        end

        # Needs to be done before getcutsDE
        bs, Ks = getrhs(nlds)

        computecuts!(nlds) # FIXME what is the use of this ?
        A = getcutsDE(nlds)
        if nlds.xuray_a !== nothing
            A = [A spzeros(size(A, 1), 1)]
        end
        bigA = [bigA; A]

        bigC = nlds.C
        bigc = nlds.c
        if nlds.nθ > 0
            bigC = [bigC; θC(nlds)[2]]
            if nlds.nθ == 1
                bigc = [bigc; 1]
            else
                bigc = [bigc; nlds.proba]
            end
        end
        if nlds.xuray_a !== nothing
            bigC = [bigC; (:NonNeg, [nlds.nx+nlds.nθ+1])]
            bigc = [bigc; nlds.objvalxuray_a]
        end

        _load!(nlds.model, bigc, bigA, bs, Ks, bigC)
        nlds.loaded = true
    end
end

function checkstatus(status::Symbol)
    if status == :Error
        error("The solver reported an error")
    elseif status == :UserLimit
        error("The solver reached iteration limit or timed out")
    end
end

function Eθlb(nlds::NLDS)
    if nlds.nθ == 0
        0.
    else
        if nlds.nθ == length(nlds.proba)
            dot(nlds.proba, nlds.θlb)
        else
            θlb, _ = θC(nlds)
            @assert length(θlb) == 1
            θlb[1]
        end
    end
end

function solve!(nlds::NLDS{S}) where S
    load!(nlds)
    if !nlds.solved
        MathProgBase.optimize!(nlds.model)
        status = MathProgBase.status(nlds.model)
        checkstatus(status)
        sol = Solution(status, _getobjval(nlds.model) + Eθlb(nlds))

        if status == :Unbounded
            uray = _getunboundedray(nlds.model)
            sol.xuray = uray[1:nlds.nx]
            sol.objvalxuray = dot(nlds.c, sol.xuray)
            sol.θuray = uray[nlds.nx .+ (1:nlds.nθ)]

            # See https://github.com/JuliaOpt/Gurobi.jl/issues/80
            c = MathProgBase.getobj(nlds.model)

            MathProgBase.setobj!(nlds.model, zero(c))
            MathProgBase.optimize!(nlds.model)
            newstatus = MathProgBase.status(nlds.model)
            @assert newstatus != :Unbounded # Now the objective is 0
            checkstatus(newstatus)
            if newstatus == :Infeasible
                # We discard unbounded ray, infeasibility is more important
                status = newstatus
                sol.xuray = nothing
                sol.objvalxuray = nothing
                sol.θuray = nothing
            else
                @assert newstatus == :Optimal
            end
            if newstatus == :Infeasible
                sol.status = :Infeasible
            end
        else
            newstatus = status
        end

        if newstatus == :Infeasible || status != :Unbounded
            # if infeasible dual + λ iray is dual feasible for any λ >= 0
            # here I just take iray to build the feasibility cut
            dual = _getdual(nlds.model)
            if isempty(dual)
                error("Dual vector returned by the solver is empty while the status is $status")
            end
            @assert length(dual) == nlds.nπ + nlds.nσ + sum(nlds.nρ)

            π = dual[nlds.πs]
            σρ = @view dual[nlds.nπ+1:end]

            σ = σρ[nlds.σs]
            addusage!(nlds.FCpruner, σ)
            sol.σd = dot(σ, nlds.FCpruner.b)

            sol.ρe = zero(S)
            for i in 1:nlds.nθ
                ρ = σρ[nlds.ρs[i]]
                addusage!(nlds.OCpruners[i], ρ)
                sol.ρe += dot(ρ, nlds.OCpruners[i].b)
            end

            sol.πT = vec(π' * nlds.T)
            sol.πh = dot(π, nlds.h)
        end

        # Needs to be done after since if status is unbounded I do a resolve
        if newstatus != :Infeasible
            primal = _getsolution(nlds.model)
            sol.x = primal[1:nlds.nx]
            addposition!(nlds.FCpruner, sol.x)
            for i in 1:nlds.nθ
                addposition!(nlds.OCpruners[i], sol.x)
            end
            sol.objvalx = dot(nlds.c, sol.x)
            sol.θ = θC(nlds)[1] .+ primal[nlds.nx .+ (1:nlds.nθ)]
        end

        if status == :Unbounded
            # It needs to be done *after* getsolution for some solver (e.g. CPLEX)
            MathProgBase.setobj!(nlds.model, c)
        end

        nlds.prevsol = sol
    end
end

function getsolution(nlds::NLDS)
    solve!(nlds)
    nlds.prevsol
end
