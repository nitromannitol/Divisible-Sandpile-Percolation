import Sandpile.External.RSW.WiredArmDualCrossing
import Sandpile.External.RSW.DualTranslation
import Sandpile.External.RSW.DualSwap

/-!
# Coordinates of the wired dual crossing

The transpositions and translations in the planar duality theorem combine to
place the crossing in face coordinates relative to the original arm rectangle.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- The coordinate changes in wired duality reduce to a translation. -/
theorem wired_dual_reindex (m : ℕ) (ω : Sym2 (Site 2) → Bool) :
    (dualBondConfig ((wiredArmConfig m ω ∘ Sym2.map swapPlaneSite) ∘
      Sym2.map (fun z => z + (- ![((m + 1 : ℕ) : ℤ), ((m + m / 64 : ℕ) : ℤ)]))) ∘
      Sym2.map dualCrossingIso) =
    (dualBondConfig (wiredArmConfig m ω) ∘
      Sym2.map (fun z => z + ![-((m + m / 64 : ℕ) : ℤ) - 1, -((m + 1 : ℕ) : ℤ)])) := by
  rw [dualBondConfig_translate, dualBondConfig_swap]
  funext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Function.comp_apply, Sym2.map_mk]
    have hf (z : Site 2) : dualCrossingIso z = swapPlaneSite z + dualShift := by
      ext i
      fin_cases i <;> simp [dualCrossingIso, swapPlaneSite]
    have hg (z : Site 2) :
        swapPlaneSite (dualCrossingIso z +
          (- ![((m + 1 : ℕ) : ℤ), ((m + m / 64 : ℕ) : ℤ)])) =
        z + ![-((m + m / 64 : ℕ) : ℤ) - 1, -((m + 1 : ℕ) : ℤ)] := by
      rw [hf]
      ext i
      fin_cases i
      · simp [swapPlaneSite, dualShift, Pi.add_apply]
        ring
      · simp [swapPlaneSite, dualShift, Pi.add_apply]
    rw [hg x, hg y]

/-- An absent arm gives a dual horizontal crossing, indexed by the lower-left
corners of faces in the rectangle `[-M-1,M] × [-m-1,m]`, where `M=m+m/64`. -/
theorem translated_dual_crossing_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    (dualBondConfig (wiredArmConfig m ω) ∘
      Sym2.map (fun z => z + ![-((m + m / 64 : ℕ) : ℤ) - 1, -((m + 1 : ℕ) : ℤ)])) ∈
        bondCrossingEvent (2 * (m + m / 64) + 1) (2 * m + 1) := by
  rw [← wired_dual_reindex]
  exact dual_crossing_of_not_kstArmEvent m hm ω h

end Sandpile.External.RSW
