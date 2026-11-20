import Sandpile.External.MVBE.MvbeOrthantBerryEsseen
import Sandpile.External.MVBE.PerimQuarterProved
import Sandpile.External.MVBE.WhiteningBridge

/-!
# The multivariate Berry–Esseen comparison

Raič's multivariate comparison and the Gaussian perimeter bound for rounded orthants imply the
standardized orthant comparison.
-/

namespace Sandpile.External

/-- The multivariate Berry–Esseen comparison for orthants. -/
theorem multivariateBerryEsseen_holds : MultivariateBerryEsseen :=
  MVBE.frozenQuarter_iff_multivariateBerryEsseen.mp
    (MVBE.mvbe_frozenQuarter_of_perimeter MVBE.perimQuarter)

end Sandpile.External
