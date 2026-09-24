import Sandpile.MainTheorems

/-!
# Axioms audit

Building this module prints the axiom dependencies of the twelve main theorems of
`Sandpile/MainTheorems.lean`.  Each must report exactly the three standard foundational axioms
of Mathlib: `propext`, `Classical.choice`, `Quot.sound`.

The results the paper cites without proof are not axioms here: each is a `Prop` in
`Sandpile/External/` taken as an explicit hypothesis of the theorems that use it, so it
appears in the statement, not in this list.

This file is not imported by the library root; the report runs when it is built explicitly
(`lake build Sandpile.Meta.AxiomsAudit`), as continuous integration does on every push.
-/

#print axioms Sandpile.percolation_below_criticality
#print axioms Sandpile.critical_level_percolation
#print axioms Sandpile.mean_growth_le_three
#print axioms Sandpile.brownian_scaling_limit
#print axioms Sandpile.mean_growth_four
#print axioms Sandpile.four_first_order
#print axioms Sandpile.four_gaussian
#print axioms Sandpile.four_sobolev
#print axioms Sandpile.high_first_order
#print axioms Sandpile.high_tail
#print axioms Sandpile.high_sobolev_limit
#print axioms Sandpile.high_nonconvergence
