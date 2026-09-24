import Audit.Support.Statements
import Audit.Nontriviality.Solution
import Audit.CriticalLevels.Solution
import Audit.MeanGrowthLow.Solution
import Audit.BrownianScalingLimit.Solution
import Audit.MeanGrowthFour.Solution
import Audit.FourFirstOrder.Solution
import Audit.FourGaussian.Solution
import Audit.FourSobolev.Solution
import Audit.HighFirstOrder.Solution
import Audit.HighTail.Solution
import Audit.HighSobolevLimit.Solution
import Audit.HighNonconvergence.Solution

/-!
# Statement regression for the comparator solutions

For each audited theorem, checks that the type of the solution theorem is
exactly the proposition elaborated in the challenge environment
(`Audit/Support/Statements.lean`), and that it mentions no constant of the
repository namespace `Sandpile` or of the shared library namespace `LatticeProb`.
Building this module prints one line per theorem; any mismatch is an error.
This is a local proxy for the statement-identity part of
`leanprover/comparator`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (thm, stmt) in [
    (`SandpileAudit.percolation_below_criticality, `SandpileAudit.Statements.percolation_below_criticality),
    (`SandpileAudit.critical_level_percolation, `SandpileAudit.Statements.critical_level_percolation),
    (`SandpileAudit.mean_growth_le_three, `SandpileAudit.Statements.mean_growth_le_three),
    (`SandpileAudit.brownian_scaling_limit, `SandpileAudit.Statements.brownian_scaling_limit),
    (`SandpileAudit.mean_growth_four, `SandpileAudit.Statements.mean_growth_four),
    (`SandpileAudit.four_first_order, `SandpileAudit.Statements.four_first_order),
    (`SandpileAudit.four_gaussian, `SandpileAudit.Statements.four_gaussian),
    (`SandpileAudit.four_sobolev, `SandpileAudit.Statements.four_sobolev),
    (`SandpileAudit.high_first_order, `SandpileAudit.Statements.high_first_order),
    (`SandpileAudit.high_tail, `SandpileAudit.Statements.high_tail),
    (`SandpileAudit.high_sobolev_limit, `SandpileAudit.Statements.high_sobolev_limit),
    (`SandpileAudit.high_nonconvergence, `SandpileAudit.Statements.high_nonconvergence)] do
    let some ti := env.find? thm | throwError "missing theorem {thm}"
    let some si := env.find? stmt | throwError "missing statement {stmt}"
    let some v := si.value? | throwError "statement {stmt} has no value"
    unless ti.levelParams == si.levelParams do
      throwError "{thm}: universe parameters differ from the challenge statement"
    -- A `def` abstracts the proofs inside its value into auxiliary lemmas
    -- (`SandpileAudit.Statements.*._proof_i`, shared between declarations);
    -- put their proof terms back before comparing.
    let v := v.replace fun e => match e with
      | .const n ls =>
        if (`SandpileAudit.Statements).isPrefixOf n && n.isInternal then
          (env.find? n).bind fun ci => (ci.value? (allowOpaque := true)).map (·.instantiateLevelParams ci.levelParams ls)
        else none
      | _ => none
    let v ← liftCoreM (Core.betaReduce v)
    let ty ← liftCoreM (Core.betaReduce ti.type)
    unless ty == v do
      throwError "{thm}: the solution statement differs from the challenge statement"
    for c in ti.type.getUsedConstants do
      if (`Sandpile).isPrefixOf c || (`LatticeProb).isPrefixOf c then
        throwError "{thm} mentions the repository or library constant {c}"
    logInfo m!"{thm}: identical to the challenge statement; no repository or library constant"

#print axioms SandpileAudit.percolation_below_criticality
#print axioms SandpileAudit.critical_level_percolation
#print axioms SandpileAudit.mean_growth_le_three
#print axioms SandpileAudit.brownian_scaling_limit
#print axioms SandpileAudit.mean_growth_four
#print axioms SandpileAudit.four_first_order
#print axioms SandpileAudit.four_gaussian
#print axioms SandpileAudit.four_sobolev
#print axioms SandpileAudit.high_first_order
#print axioms SandpileAudit.high_tail
#print axioms SandpileAudit.high_sobolev_limit
#print axioms SandpileAudit.high_nonconvergence
