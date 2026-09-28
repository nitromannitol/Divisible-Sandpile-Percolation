import Sandpile.Law
import Sandpile.Support.Odometer
import LatticeProb.Walk.Markov

/-!
# Translation invariance of the i.i.d. mass law

The i.i.d. mass field `massLaw d μ` is invariant under translation (`massLaw_map_shiftField`),
and the odometer commutes with translation (`odometer_shiftField`). Together these give the mean
odometer `∫ odometer σ t y ∂(massLaw d μ)` no dependence on the site `y` (`integral_odometer_eq`),
and hence identify the mean of its neighbour average with the mean odometer itself
(`integral_avg_odometer`), which is the stationarity identity `E(ζ(0) + Pu_t(0)) = E u_t(0)`
written termwise.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The mass field seen from `y`. -/
def shiftField (y : Site d) (σ : Site d → ℝ) : Site d → ℝ := fun z => σ (z + y)

/-- `shiftField y` is measurable, as a coordinate relabelling of `Site d → ℝ`. -/
theorem measurable_shiftField (y : Site d) : Measurable (shiftField (d := d) y) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The odometer commutes with translation. -/
theorem odometer_shiftField (σ : Site d → ℝ) (y : Site d) :
    ∀ (t : ℕ) (z : Site d), odometer (shiftField y σ) t z = odometer σ t (z + y) := by
  intro t
  induction t with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      have hnb : nbrSum (odometer (shiftField y σ) n) z
          = nbrSum (odometer σ n) (z + y) := by
        unfold nbrSum
        refine Finset.sum_congr rfl fun i _ => ?_
        have e1 : z + unit i + y = z + y + unit i := by abel
        have e2 : z - unit i + y = z + y - unit i := by abel
        rw [ih (z + unit i), ih (z - unit i), e1, e2]
      show relax (shiftField y σ) (odometer (shiftField y σ) n) z
        = relax σ (odometer σ n) (z + y)
      unfold relax
      rw [hnb]
      rfl

/-- The i.i.d. mass law is invariant under translation. -/
theorem massLaw_map_shiftField (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (y : Site d) : (massLaw d μ).map (shiftField y) = massLaw d μ := by
  unfold massLaw LatticeProb.iidLaw shiftField
  exact Measure.map_infinitePi_infinitePi_of_inj (f := fun z : Site d => z + y)
    (fun a b hab => by simpa using hab)

/-- The mean odometer does not depend on the site. -/
theorem integral_odometer_eq (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℕ) (y : Site d)
    (hint : Integrable (fun σ => odometer σ t 0) (massLaw d μ)) :
    ∫ σ, odometer σ t y ∂(massLaw d μ) = ∫ σ, odometer σ t 0 ∂(massLaw d μ) := by
  have hmeas : AEStronglyMeasurable (fun σ : Site d → ℝ => odometer σ t 0)
      ((massLaw d μ).map (shiftField y)) := by
    rw [massLaw_map_shiftField]
    exact hint.aestronglyMeasurable
  have h1 : ∫ σ, odometer (shiftField y σ) t 0 ∂(massLaw d μ)
      = ∫ σ, odometer σ t 0 ∂(massLaw d μ) := by
    rw [← integral_map (measurable_shiftField y).aemeasurable hmeas, massLaw_map_shiftField]
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only []
  rw [odometer_shiftField σ y t 0, zero_add]

/-- Under the i.i.d. mass law, `σ ↦ odometer σ t y` is integrable at every site `y`, given that
it is integrable at the origin, by the translation invariance of `massLaw d μ`. -/
theorem integrable_odometer_shift (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℕ) (y : Site d)
    (hint : Integrable (fun σ => odometer σ t 0) (massLaw d μ)) :
    Integrable (fun σ => odometer σ t y) (massLaw d μ) := by
  have hmeas : AEStronglyMeasurable (fun σ : Site d → ℝ => odometer σ t 0)
      ((massLaw d μ).map (shiftField y)) := by
    rw [massLaw_map_shiftField]
    exact hint.aestronglyMeasurable
  have h : Integrable (fun σ : Site d → ℝ => odometer (shiftField y σ) t 0)
      (massLaw d μ) := by
    show Integrable ((fun σ : Site d → ℝ => odometer σ t 0) ∘ shiftField y) (massLaw d μ)
    rw [← integrable_map_measure hmeas (measurable_shiftField y).aemeasurable,
      massLaw_map_shiftField]
    exact hint
  refine h.congr (Filter.Eventually.of_forall fun σ => ?_)
  simp only []
  rw [odometer_shiftField σ y t 0, zero_add]

/-- Averaging over the neighbours does not change the mean odometer. -/
theorem integral_avg_odometer (d : ℕ) (hd : 1 ≤ d) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (t : ℕ)
    (hint : Integrable (fun σ => odometer σ t 0) (massLaw d μ)) :
    ∫ σ, avg (odometer σ t) 0 ∂(massLaw d μ) = ∫ σ, odometer σ t 0 ∂(massLaw d μ) := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  show ∫ σ, (∑ i : Fin d,
      (odometer σ t (0 + unit i) + odometer σ t (0 - unit i))) / (2 * (d : ℝ))
      ∂(massLaw d μ) = _
  simp only [zero_add, zero_sub]
  have hterm : ∀ i : Fin d, Integrable
      (fun σ : Site d → ℝ => odometer σ t (unit i) + odometer σ t (-unit i))
      (massLaw d μ) := fun i =>
    (integrable_odometer_shift d μ t (unit i) hint).add
      (integrable_odometer_shift d μ t (-unit i) hint)
  rw [integral_div, integral_finsetSum _ fun i _ => hterm i]
  have heach : ∀ i : Fin d,
      ∫ σ, (odometer σ t (unit i) + odometer σ t (-unit i)) ∂(massLaw d μ)
        = 2 * ∫ σ, odometer σ t 0 ∂(massLaw d μ) := by
    intro i
    rw [integral_add (integrable_odometer_shift d μ t (unit i) hint)
      (integrable_odometer_shift d μ t (-unit i) hint),
      integral_odometer_eq d μ t (unit i) hint,
      integral_odometer_eq d μ t (-unit i) hint]
    ring
  rw [Finset.sum_congr rfl fun i _ => heach i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, div_eq_iff hd0]
  ring

/-- Under the i.i.d. mass law, the neighbour average `σ ↦ avg (odometer σ t) 0` is integrable,
given that `σ ↦ odometer σ t 0` is, as a finite average of the integrable translates furnished
by `integrable_odometer_shift`. -/
theorem integrable_avg_odometer (d : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℕ)
    (hint : Integrable (fun σ => odometer σ t 0) (massLaw d μ)) :
    Integrable (fun σ => avg (odometer σ t) 0) (massLaw d μ) := by
  have h : Integrable (fun σ : Site d → ℝ =>
      (∑ i : Fin d, (odometer σ t (unit i) + odometer σ t (-unit i))) / (2 * (d : ℝ)))
      (massLaw d μ) := by
    refine Integrable.div_const ?_ _
    exact integrable_finsetSum _ fun i _ =>
      (integrable_odometer_shift d μ t (unit i) hint).add
        (integrable_odometer_shift d μ t (-unit i) hint)
  refine h.congr (Filter.Eventually.of_forall fun σ => ?_)
  show _ = avg (odometer σ t) 0
  unfold avg LatticeProb.walkOp nbrSum
  simp

/-- Under the centred mass law the scenery at a site is integrable with mean zero. -/
theorem scenery_integrable_and_mean (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hintν : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) :
    Integrable (fun σ => scenery d σ 0) (centeredMassLaw d ν) ∧
      ∫ σ, scenery d σ 0 ∂(centeredMassLaw d ν) = 0 := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  set g : ℝ → ℝ := fun z => 1 + 2 * (d : ℝ) * z with hg
  haveI : IsProbabilityMeasure (ν.map g) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hcoord : (centeredMassLaw d ν).map (fun σ : Site d → ℝ => σ 0) = ν.map g := by
    unfold centeredMassLaw massLaw LatticeProb.iidLaw
    exact Measure.infinitePi_map_eval _ 0
  have hcomp : ∀ z : ℝ, (g z - 1) / (2 * (d : ℝ)) = z := by
    intro z; rw [hg]; field_simp; ring
  have hkey : Integrable (fun s : ℝ => (s - 1) / (2 * (d : ℝ))) (ν.map g) ∧
      ∫ s : ℝ, (s - 1) / (2 * (d : ℝ)) ∂(ν.map g) = 0 := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    constructor
    · exact hintν.congr (Filter.Eventually.of_forall fun z => (hcomp z).symm)
    · rw [integral_congr_ae (Filter.Eventually.of_forall hcomp)]
      exact hmean
  have hasm : AEStronglyMeasurable (fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
      ((centeredMassLaw d ν).map (fun σ : Site d → ℝ => σ 0)) := by
    rw [hcoord]; exact hkey.1.aestronglyMeasurable
  constructor
  · show Integrable ((fun s : ℝ => (s - 1) / (2 * (d : ℝ))) ∘
      (fun σ : Site d → ℝ => σ 0)) (centeredMassLaw d ν)
    refine (integrable_map_measure hasm (measurable_pi_apply 0).aemeasurable).mp ?_
    rw [hcoord]; exact hkey.1
  · have hmap := integral_map (μ := centeredMassLaw d ν)
      (φ := fun σ : Site d → ℝ => σ 0) (f := fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
      (measurable_pi_apply 0).aemeasurable hasm
    rw [hcoord] at hmap
    show ∫ σ : Site d → ℝ, ((fun s : ℝ => (s - 1) / (2 * (d : ℝ)))
      ((fun σ : Site d → ℝ => σ 0) σ)) ∂(centeredMassLaw d ν) = 0
    rw [← hmap]
    exact hkey.2

/-- `max 0 a = a + max 0 (-a)`, splitting off the negative part of `a`. -/
theorem max_zero_eq (a : ℝ) : max 0 a = a + max 0 (-a) := by
  rcases le_or_gt 0 a with h | h
  · rw [max_eq_right h, max_eq_left (by linarith : -a ≤ (0 : ℝ))]
    ring
  · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith : (0 : ℝ) ≤ -a)]
    ring

/-- The neighbour average of the odometer is monotone in time: `avg (odometer σ t) z ≤
avg (odometer σ (t + 1)) z`, since the odometer itself increases termwise with `t`. -/
theorem avg_odometer_mono (σ : Site d → ℝ) (t : ℕ) (z : Site d) :
    avg (odometer σ t) z ≤ avg (odometer σ (t + 1)) z := by
  unfold avg LatticeProb.walkOp
  have h : nbrSum (odometer σ t) z ≤ nbrSum (odometer σ (t + 1)) z :=
    nbrSum_mono (fun y => odometer_le_succ σ t y) z
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hc : (0 : ℝ) < 2 * (d : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      linarith
    gcongr

end Sandpile
