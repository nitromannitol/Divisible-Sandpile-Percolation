import Sandpile.Support.Spectral
import Sandpile.Support.MembraneStopping
import Sandpile.Support.SceneryBridge

/-!
# The event bridge

The lower event of the odometer at time `t` is contained in the event that the
membrane field lies below the same threshold at every earlier time, and that
event reads only the finitely many sites of a box. Reading those sites carries
the i.i.d. law of the scenery to the finite product of the one-site law, which
is the measure the multivariate Berry-Esseen comparison is stated on.
`measurable_membrane` and the two `measurableSet_*` lemmas supply the measurability this
needs, and `measure_odometer_le_pi` is the bridge itself.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The membrane field `membrane ζ t x` is measurable in the scenery `ζ`, being a finite sum
of coordinate projections by `membrane_eq_sum_boxEnum`. -/
theorem measurable_membrane (t : ℕ) (x : Site d) :
    Measurable fun ζ : Site d → ℝ => membrane ζ t x := by
  have hrep : (fun ζ : Site d → ℝ => membrane ζ t x)
      = fun ζ : Site d → ℝ =>
        ∑ i : Fin (boxFinset x t).card,
          greenTime d t x (boxEnum x t i) * ζ (boxEnum x t i) := by
    funext ζ; exact membrane_eq_sum_boxEnum t x ζ
  rw [hrep]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).const_mul _

end Sandpile

namespace Sandpile

variable {d : ℕ}

/-- The event that the membrane field at the origin stays below `h` at each of finitely many
times `ns j` is measurable, as a finite intersection of measurable half-spaces. -/
theorem measurableSet_membrane_le {m : ℕ} (ns : Fin m → ℕ) (h : ℝ) :
    MeasurableSet {ζ : Site d → ℝ | ∀ j, membrane ζ (ns j) 0 ≤ h} := by
  have : {ζ : Site d → ℝ | ∀ j, membrane ζ (ns j) 0 ≤ h}
      = ⋂ j : Fin m, {ζ : Site d → ℝ | membrane ζ (ns j) 0 ≤ h} := by
    ext ζ; simp [Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le (measurable_membrane (ns j) 0) measurable_const

/-- The set of `ξ` satisfying finitely many linear inequalities `∑ i, a i j * ξ i ≤ c j` is
measurable, as a finite intersection of measurable half-spaces. -/
theorem measurableSet_linear_le {N m : ℕ} (a : Fin N → Fin m → ℝ) (c : Fin m → ℝ) :
    MeasurableSet {ξ : Fin N → ℝ | ∀ j, ∑ i, a i j * ξ i ≤ c j} := by
  have : {ξ : Fin N → ℝ | ∀ j, ∑ i, a i j * ξ i ≤ c j}
      = ⋂ j : Fin m, {ξ : Fin N → ℝ | ∑ i, a i j * ξ i ≤ c j} := by
    ext ξ; simp [Set.mem_iInter]
  rw [this]
  refine MeasurableSet.iInter fun j => measurableSet_le ?_ measurable_const
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

/-- **The event bridge**: the odometer's lower event at time `t` is carried into
the orthant of the standardized membrane fields on the finite product. -/
theorem measure_odometer_le_pi (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {s : Finset (Site d)} {m t : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hnt : ∀ j, ns j ≤ t) (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s)
    (h : ℝ) :
    centeredMassLaw d ν {σ | odometer σ t 0 ≤ h}
      ≤ (Measure.pi fun _ : Fin s.card => ν)
          {ξ | ∀ j, ∑ i, stdCoeff d ν s ns i j * ξ i ≤ h / membraneSd d ν (ns j)} := by
  classical
  set A : Set (Site d → ℝ) := {ζ | ∀ j, membrane ζ (ns j) 0 ≤ h} with hA
  set B : Set (Fin s.card → ℝ) :=
    {ξ | ∀ j, ∑ i, stdCoeff d ν s ns i j * ξ i ≤ h / membraneSd d ν (ns j)} with hB
  have hAB : A = (fun ζ : Site d → ℝ => fun i : Fin s.card => ζ (siteEnum s i)) ⁻¹' B := by
    ext ζ
    simp only [hA, hB, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro hζ j
      have hM : 0 < membraneSd d ν (ns j) := membraneSd_pos ν hvar (hns j)
      have hrep : ∑ i : Fin s.card, stdCoeff d ν s ns i j * ζ (siteEnum s i)
          = membrane ζ (ns j) 0 / membraneSd d ν (ns j) := by
        rw [membrane_eq_sum_siteEnum (hsub j) ζ, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by rw [stdCoeff]; ring
      rw [hrep]
      exact (div_le_div_iff_of_pos_right hM).mpr (hζ j)
    · intro hξ j
      have hM : 0 < membraneSd d ν (ns j) := membraneSd_pos ν hvar (hns j)
      have hrep : ∑ i : Fin s.card, stdCoeff d ν s ns i j * ζ (siteEnum s i)
          = membrane ζ (ns j) 0 / membraneSd d ν (ns j) := by
        rw [membrane_eq_sum_siteEnum (hsub j) ζ, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by rw [stdCoeff]; ring
      have := hξ j
      rw [hrep, div_le_div_iff_of_pos_right hM] at this
      exact this
  have hsubset : {σ : Site d → ℝ | odometer σ t 0 ≤ h} ⊆ scenery d ⁻¹' A := by
    intro σ hσ j
    have h1 : odometerOf (scenery d σ) t 0 ≤ h := by
      rw [← congrFun (odometer_eq_odometerOf σ t) 0]
      exact hσ
    exact le_trans (membrane_le_odometerOf hd _ (hnt j) 0) h1
  calc centeredMassLaw d ν {σ | odometer σ t 0 ≤ h}
      ≤ centeredMassLaw d ν (scenery d ⁻¹' A) := measure_mono hsubset
    _ = LatticeProb.iidLaw d ν A :=
        centeredMassLaw_scenery_preimage d ν hd (measurableSet_membrane_le ns h)
    _ = (Measure.pi fun _ : Fin s.card => ν) B := by
        rw [hAB]
        exact (LatticeProb.measurePreserving_pick _ ν (siteEnum s)
            (siteEnum_injective s)).measure_preimage
          (measurableSet_linear_le _ _).nullMeasurableSet

end Sandpile
