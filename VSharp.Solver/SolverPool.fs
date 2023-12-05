namespace VSharp.Solver
open VSharp.Core.SolverInteraction
open VSharp.Solver.Z3Solver

type public SupportedSolvers =
    | Yices
    | Z3

module public SolverPool =

    let mutable private currentSolver = Z3

    let switchSolver (solver : SupportedSolvers) =
        currentSolver <- solver

    let mkSolver (timeoutMs : int, solver : SupportedSolvers) : ISolver =
        let timeoutOpt = if timeoutMs > 0 then Some(uint timeoutMs) else None
        match currentSolver with
        | Z3 -> Z3Solver timeoutOpt :> ISolver

    let reset() =
        Z3.reset()
