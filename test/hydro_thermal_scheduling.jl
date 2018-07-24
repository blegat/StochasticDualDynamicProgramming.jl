# See https://web.stanford.edu/~lcambier/fast/tuto.php
@testset "Hydro Thermal Scheduling with $solver" for solver in lp_solvers
    num_stages = 5
    numScen = 2
    C = 5
    V = 8
    d = 6
    r = [2, 10]
    x = Matrix{JuMP.Variable}(num_stages, numScen)
    y = Matrix{JuMP.Variable}(num_stages, numScen)
    p = Matrix{JuMP.Variable}(num_stages, numScen)

    models = Vector{JuMP.Model}(num_stages)
	for s in 1:num_stages
        for ξ in 1:(s == 1 ? 1 : numScen)
			if s == 1
				model = StructuredModel(num_scenarios=numScen)
			else
				model = StructuredModel(parent=models[s-1], prob=1/2, same_children_as=(ξ == 1 ? nothing : models[s]), id=ξ, num_scenarios=(s == num_stages ? 0 : numScen))
			end
			x[s, ξ] = @variable(model, lowerbound=0, upperbound=V)
			y[s, ξ] = @variable(model, lowerbound=0)
			p[s, ξ] = @variable(model, lowerbound=0)
			if s > 1
				@constraint(model, x[s, ξ] <= x[s-1, 1] + r[ξ] - y[s, ξ])
			else
                @constraint(model, x[s, ξ] <= mean(r) - y[s, ξ])
			end
			@constraint(model, p[s, ξ] + y[s, ξ] >= d)
			@objective(model, Min, C * p[s, ξ])
			if ξ == 1
				models[s] = model
			end
		end
	end

    forwardcuts = true
    cutmode = StructProg.MultiCutGenerator()
    detectlb = false
    for forwardcuts in [false, true]
        for cutmode in [StructProg.MultiCutGenerator(), StructProg.AvgCutGenerator()]
            for detectlb in [false, true]
                sp = SOI.stochasticprogram(models[1], num_stages, solver, AvgCutPruningAlgo(-1), cutmode, detectlb)
                algo = SDDP.Algorithm(K = 16, forwardcuts = forwardcuts, backwardcuts = !forwardcuts)
                sol = SOI.optimize!(sp, algo, SOI.Pereira(2, 0.5) | SOI.IterLimit(10), 0)

                #@test sol.status == :Optimal
                if forwardcuts
                    @test SOI.niterations(sol) == (detectlb ? 3 : 5)
                    #@test sol.objval ≈ (detectlb ? 15 : 18.75)
                else
                    @test SOI.niterations(sol) == (!detectlb && isa(cutmode, StructProg.AvgCutGenerator) ? 5 : 2)
                    if isa(cutmode, StructProg.AvgCutGenerator)
                        if detectlb
                            #@test sol.objval ≈ 22.5 # Clp returns an approximate value
                        else
                            #@test sol.objval ≈ 23.75
                        end
                    else
                        if detectlb
                            #@test sol.objval ≈ 23.75
                        else
                            #@test sol.objval ≈ 18.75
                        end
                    end
                end

                StructProg.clear(models[1])
            end
        end
    end
end
