using Test
import AbstractAlgebra
using Groups

import KnuthBendix: Word

using GroupsCore
include(joinpath(pathof(GroupsCore), "..", "..", "test", "conformance_test.jl"))

@testset "Groups" begin

    @testset "wlmetric_ball" begin
        M = AbstractAlgebra.MatrixAlgebra(AbstractAlgebra.zz, 3)
        w = one(M); w[1,2] = 1;
        r = one(M); r[2,3] = -3;
        s = one(M); s[1,3] = 2; s[3,2] = -1;

        S = [w,r,s]; S = unique([S; inv.(S)]);
        _, sizes = Groups.wlmetric_ball(S, radius=4);
        @test sizes == [7, 33, 141, 561]
        _, sizes = Groups.wlmetric_ball_serial(S, radius=4);
        @test sizes == [7, 33, 141, 561]
    end

    include("free_groups.jl")
    include("fp_groups.jl")

    include("AutFn.jl")
    include("AutSigma_41.jl")

    # if !haskey(ENV, "CI")
    #    include("benchmarks.jl")
    # end
end
