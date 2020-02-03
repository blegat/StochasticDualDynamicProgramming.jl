struct SDDPModelData
    nodes::Vector{Union{Nothing, Int}}
end

function createnode(sp::StochasticProgram, m::Model, t, num_stages, solver, parent, pruningalgo::AbstractCutPruningAlgo, cutgen::AbstractOptimalityCutGenerator, detectlb::Bool=true, newcut::Symbol=:InvalidateSolver)
    # For each model, we need to create a different node for each t.
    # We store all these node in a nodes array per model
    if !(:SDDP in keys(m.ext))
        nodes = Vector{Union{Nothing, Int}}(undef, num_stages)
        fill!(nodes, nothing)
        m.ext[:SDDP] = SDDPModelData(nodes)
    end
    nodes = m.ext[:SDDP].nodes
    if nodes[t] === nothing
        # The last argument contains the categories (e.g. :Cont, :Int, :Bool, ...) but it is currently unused
        param_model = StructJuMP.ParametrizedModel(m)
        newnodedata = NodeData(NLDS{Float64}(param_model, solver, pruningalgo, newcut), parent === nothing ? 0 : SOI.get(sp, SOI.Dimension(), parent))
        newnode = SOI.add_scenario_node!(sp, newnodedata)
        SOI.set!(sp, CutGenerator(), newnode, cutgen)
        nodes[t] = newnode
        struc = getStructure(m)
        if t < num_stages
            num_scen = length(struc.children)
            for id in keys(struc.children)
                child = createnode(sp, struc.children[id], t+1, num_stages, solver, newnode, pruningalgo, cutgen, detectlb, newcut)
                tr = SOI.add_scenario_transition!(sp, newnode, child, struc.probability[id])
                if detectlb
                    SOI.set!(sp, SOI.TransitionObjectiveValueBound(), tr, SOI.get(sp, SOI.NodeObjectiveValueBound(), child))
                end
            end
        end
    end
    nodes[t]
end

"""
    stochasticprogram(m::JuMP.Model, num_stages, solver,
                      pruningalgo::CutPruners.AbstractCutPruningAlgo,
                      cutgen::AbstractOptimalityCutGenerator=MultiCutGenerator(),
                      detectlb::Bool=true, newcut::Symbol=:InvalidateSolver)

Creates a `StochasticProgram` from a [StructJuMP](https://github.com/StructJuMP/StructJuMP.jl) model. The former can then be used by the SDDP algorithm.
The master problem is assumed to have model `m` and the scenarios are considered up to `num_stages` stages.
The `pruningalgo` is as defined in [CutPruners](https://github.com/JuliaPolyhedra/CutPruners.jl).
If `cutgen` is `MultiCutGenerator`, one variable `θ_i` is created for each scenario. Otherwise, if `cutgen` is `AvgCutGenerator`, only one variable `θ` is created and it represents the expected value of the objective value of the scenarios. If `cutgen` is `NoOptimalityCut` then no `θ` is created, only use this option if the objective of all models is zero except for the master model.
"""
function SOI.stochasticprogram(m::Model, num_stages, solver,
                               pruningalgo::AbstractCutPruningAlgo,
                               cutgen::AbstractOptimalityCutGenerator=MultiCutGenerator(),
                               detectlb::Bool=true, newcut::Symbol=:InvalidateSolver)
    sp = StochasticProgram{Float64}(num_stages)
    createnode(sp, m, 1, num_stages, solver, nothing, pruningalgo, cutgen, detectlb, newcut)
    sp
end

function clear(m::Model)
    if :SDDP in keys(m.ext)
        pop!(m.ext, :SDDP)
        for (id, child) in getStructure(m).children
            clear(child)
        end
    end
end
