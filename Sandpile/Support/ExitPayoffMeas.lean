import Sandpile.Support.Localization
import Sandpile.Support.ExitAverage
import Sandpile.Support.OriginKilled

open MeasureTheory Filter Topology
open scoped Classical

namespace Sandpile

variable {d : ℕ}


open MeasureTheory Filter Topology
open scoped Classical

variable {d : ℕ}

/-- Joint measurability of the exit payoff in the scenery and the path: the
stopped localized odometer is a measurable function of the pair. -/
theorem measurable_uncurry_exit_payoff (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) :
    Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      if p.2 (stopBeforeExit D N (fun _ => N) p.2) ∈ D then 0
      else localizedOdometer (E (p.2 (stopBeforeExit D N (fun _ => N) p.2))) p.1 m
        (p.2 (stopBeforeExit D N (fun _ => N) p.2)) := by
  classical
  have hτ : Measurable (stopBeforeExit D N (fun _ : ℕ → Site d => N)) :=
    measurable_const.min (measurable_exitNat D N)
  have hpair : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      (p.2, stopBeforeExit D N (fun _ => N) p.2) :=
    measurable_snd.prodMk (hτ.comp measurable_snd)
  have hev : Measurable fun q : (ℕ → Site d) × ℕ => q.1 q.2 :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  have hw : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      p.2 (stopBeforeExit D N (fun _ => N) p.2) := hev.comp hpair
  have hcount : Measurable fun q : (Site d → ℝ) × Site d =>
      if q.2 ∈ D then 0 else localizedOdometer (E q.2) q.1 m q.2 := by
    refine measurable_from_prod_countable_left fun w => ?_
    by_cases hw' : w ∈ D
    · simp only [hw', if_pos]
      exact measurable_const
    · simp only [hw', if_neg, not_false_iff]
      exact measurable_localizedOdometer hd (E w) m w
  exact hcount.comp (measurable_fst.prodMk hw)
