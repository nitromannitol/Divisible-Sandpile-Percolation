import Sandpile.External.BerryEsseen
import Sandpile.External.MVBE.MvbeWhitening

/-!
# The standardized Berry–Esseen statement

The whitened formulation uses the same covariance, coefficient norm and quadratic form as the
standardized comparison.
-/

namespace Sandpile.External.MVBE

/-- The frozen whitened formulation and the standardized comparison agree. -/
theorem frozenQuarter_iff_multivariateBerryEsseen :
    MvbeFrozenQuarter ↔ Sandpile.External.MultivariateBerryEsseen :=
  Iff.rfl

end Sandpile.External.MVBE
