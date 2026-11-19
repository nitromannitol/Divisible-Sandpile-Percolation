import Sandpile.External.MVBE.PerimBand
import Sandpile.External.MVBE.PerimPsi

/-!
# Gaussian perimeter bound for rounded orthants

Adapted from Lattice-Probability, `LatticeProb/Prob/MvbeOrthantPerimeterProved.lean`,
commit `9d53f3aa`, following Raič, *Bernoulli* 25 (2019), Theorem 1.2.
-/

namespace Sandpile.External.MVBE

/-- The Gaussian perimeter of rounded orthants is bounded by a multiple of `m ^ (1 / 4)`. -/
theorem perimQuarter : PerimQuarterStmt :=
  perimB_quarter 1000 (fun m hm h t ht => perimP_psi_bound m hm h t ht)

end Sandpile.External.MVBE
