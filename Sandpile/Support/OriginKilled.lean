import Sandpile.Support.LocalizationRecursion
import Sandpile.Support.MeanLocalization
import Sandpile.Support.HeightLower
import LatticeProb.Prob.Splice

/-!
# The origin-frozen odometer

The origin-frozen odometer `originOdometer` is the localized odometer for the domain
`{x ≠ 0}`, so the origin never topples. This module proves its monotonicity in time
(`localizedOdometer_le_succ`, `localizedOdometer_mono_time`), its agreement with the full
odometer `odometerOf` on all of space as long as the origin has not yet toppled
(`eq_originOdometer_of_origin_zero`), and the resulting reflection identities relating the
full and origin-frozen dynamics at the moment of first contact (`origin_contact_iff`,
`origin_reflection_eq`). Resampling the noise value at the origin does not change
`originOdometer` (`originOdometer_update`), and combined with atomlessness of the noise law
this gives almost-sure strict exclusion of the tie in the contact event
(`ae_origin_contact_iff`), which in turn yields the mean identity `origin_frozen_identities`
for the increment of the mean odometer.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The origin-frozen odometer: the localized odometer for the domain `{x ≠ 0}`, in which the
origin is never allowed to topple. -/
noncomputable abbrev originOdometer (ζ : Site d → ℝ) (n : ℕ) : Site d → ℝ :=
  localizedOdometer {x : Site d | x ≠ 0} ζ n

/-- The localized odometer vanishes identically outside the domain `D`, since a site outside
`D` is never allowed to topple. -/
theorem localizedOdometer_of_notMem (D : Set (Site d)) (ζ : Site d → ℝ) (n : ℕ)
    {x : Site d} (hx : x ∉ D) : localizedOdometer D ζ n x = 0 := by
  rw [localizedOdometer, Set.indicator_of_notMem hx]

/-- The localized odometer is monotone nondecreasing in the number of steps `n`, proved by
induction on `n` using that `avg` preserves the pointwise order. -/
theorem localizedOdometer_le_succ (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ) :
    ∀ n : ℕ, ∀ x : Site d, localizedOdometer D ζ n x ≤ localizedOdometer D ζ (n + 1) x := by
  intro n
  induction n with
  | zero =>
    intro x
    rw [localizedOdometer_zero hd]
    exact localizedOdometer_nonneg hd D ζ 1 x
  | succ n ih =>
    intro x
    by_cases hx : x ∈ D
    · rw [localizedOdometer_succ' hd D ζ (n + 1) x hx, localizedOdometer_succ' hd D ζ n x hx]
      exact max_le_max_left 0 (add_le_add le_rfl (avg_mono_le ih x))
    · rw [localizedOdometer_of_notMem D ζ (n + 1) hx,
        localizedOdometer_of_notMem D ζ (n + 1 + 1) hx]

/-- Restatement of `localizedOdometer_le_succ` as monotonicity of `n ↦ localizedOdometer D ζ n x`
in the `Monotone` sense. -/
theorem localizedOdometer_mono_time (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (x : Site d) : Monotone (fun n => localizedOdometer D ζ n x) :=
  monotone_nat_of_le_succ fun n => localizedOdometer_le_succ hd D ζ n x

/-- The localized odometer on any domain `D` never exceeds the full, unrestricted odometer
`odometerOf`, since restricting which sites may topple can only lower the heights reached. -/
theorem localizedOdometer_le_full (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (n : ℕ) (x : Site d) : localizedOdometer D ζ n x ≤ odometerOf ζ n x := by
  by_cases hx : x ∈ D
  · exact localizedOdometer_le External.optimalStopping hd D ζ n x hx
  · rw [localizedOdometer_of_notMem D ζ n hx]
    exact odometerOf_nonneg ζ n x

/-- The origin-frozen odometer vanishes at the origin at every time, since the origin is
excluded from its toppling domain `{x ≠ 0}`. -/
theorem originOdometer_zero (ζ : Site d → ℝ) (n : ℕ) : originOdometer ζ n 0 = 0 :=
  localizedOdometer_of_notMem _ ζ n (by simp)

/-- As long as the full odometer has not yet toppled the origin at time `n`, the full odometer
`odometerOf ζ n` agrees everywhere with the origin-frozen odometer `originOdometer ζ n`, proved
by induction on `n` since the two recursions can only differ through the origin. -/
theorem eq_originOdometer_of_origin_zero (hd : 1 ≤ d) (ζ : Site d → ℝ) :
    ∀ n : ℕ, odometerOf ζ n 0 = 0 → odometerOf ζ n = originOdometer ζ n := by
  intro n
  induction n with
  | zero =>
    intro _
    funext x
    exact (localizedOdometer_zero hd _ ζ x).symm
  | succ n ih =>
    intro hn
    have hn0 : odometerOf ζ n 0 = 0 := by
      have h1 := odometerOf_le_succ ζ n (0 : Site d)
      have h2 := odometerOf_nonneg ζ n (0 : Site d)
      linarith
    have he := ih hn0
    funext x
    by_cases hx : x = 0
    · subst hx
      rw [hn, originOdometer_zero]
    · rw [show originOdometer ζ (n + 1) x = max 0 (ζ x + avg (originOdometer ζ n) x) from
        localizedOdometer_succ' hd _ ζ n x hx]
      rw [odometerOf, he]

/-- The full odometer has not yet toppled the origin at time `n + 1` exactly when the
origin-frozen average at the origin plus the noise there is nonpositive, proved by induction on
`n` via `eq_originOdometer_of_origin_zero`. -/
theorem origin_contact_iff (hd : 1 ≤ d) (ζ : Site d → ℝ) : ∀ n : ℕ,
    odometerOf ζ (n + 1) 0 = 0 ↔ ζ 0 + avg (originOdometer ζ n) 0 ≤ 0 := by
  intro n
  induction n with
  | zero =>
    have hw : originOdometer ζ 0 = fun _ => (0 : ℝ) :=
      funext fun x => localizedOdometer_zero hd _ ζ x
    rw [hw]
    simp [odometerOf, avg]
  | succ n ih =>
    constructor
    · intro h
      have hn : odometerOf ζ (n + 1) 0 = 0 := by
        have h1 := odometerOf_le_succ ζ (n + 1) (0 : Site d)
        have h2 := odometerOf_nonneg ζ (n + 1) (0 : Site d)
        linarith
      have he := eq_originOdometer_of_origin_zero hd ζ (n + 1) hn
      rw [odometerOf, he] at h
      exact (max_eq_left_iff.mp h)
    · intro h
      have havg : avg (originOdometer ζ n) 0 ≤ avg (originOdometer ζ (n + 1)) 0 :=
        avg_mono_le (localizedOdometer_le_succ hd _ ζ n) 0
      have hn : odometerOf ζ (n + 1) 0 = 0 := ih.mpr (by linarith)
      have he := eq_originOdometer_of_origin_zero hd ζ (n + 1) hn
      rw [odometerOf, he]
      exact max_eq_left h

/-- The reflection term `max 0 (-ζ 0 - avg (odometerOf ζ n) 0)`, built from the full odometer,
equals the same term built from the origin-frozen odometer, by splitting on the contact
criterion `origin_contact_iff` and using `eq_originOdometer_of_origin_zero` and monotonicity of
`avg` on the two sides of the split. -/
theorem origin_reflection_eq (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) :
    max 0 (-ζ 0 - avg (odometerOf ζ n) 0) = max 0 (-ζ 0 - avg (originOdometer ζ n) 0) := by
  by_cases h : ζ 0 + avg (originOdometer ζ n) 0 ≤ 0
  · have hn1 := (origin_contact_iff hd ζ n).mpr h
    have hn : odometerOf ζ n 0 = 0 := by
      have h1 := odometerOf_le_succ ζ n (0 : Site d)
      have h2 := odometerOf_nonneg ζ n (0 : Site d)
      linarith
    rw [eq_originOdometer_of_origin_zero hd ζ n hn]
  · have hpos : 0 < ζ 0 + avg (originOdometer ζ n) 0 := lt_of_not_ge h
    have havg : avg (originOdometer ζ n) 0 ≤ avg (odometerOf ζ n) 0 :=
      avg_mono_le (localizedOdometer_le_full hd _ ζ n) 0
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]

/-- The origin-frozen odometer is unchanged if the noise value at the origin is resampled to any
`z`, since the origin is never in the toppling domain and so its own noise value never enters
the recursion. -/
theorem originOdometer_update (hd : 1 ≤ d) (ζ : Site d → ℝ) (z : ℝ) :
    ∀ n : ℕ, originOdometer (Function.update ζ 0 z) n = originOdometer ζ n := by
  classical
  intro n
  induction n with
  | zero =>
    funext x
    change localizedOdometer _ _ _ _ = localizedOdometer _ _ _ _
    rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
  | succ n ih =>
    change localizedOdometer _ _ _ = localizedOdometer _ _ _ at ih
    funext x
    by_cases hx : x = 0
    · subst hx
      rw [originOdometer_zero, originOdometer_zero]
    · change localizedOdometer _ _ _ _ = localizedOdometer _ _ _ _
      rw [localizedOdometer_succ' hd _ _ n x hx, localizedOdometer_succ' hd _ _ n x hx,
        Function.update_of_ne hx, ih]

/-- The map `ζ ↦ avg (originOdometer ζ n) 0` is measurable, being a finite sum of measurable
localized odometers divided by a constant. -/
theorem measurable_avg_originOdometer (hd : 1 ≤ d) (n : ℕ) :
    Measurable (fun ζ : Site d → ℝ => avg (originOdometer ζ n) 0) := by
  unfold avg
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_localizedOdometer hd _ n _).add
      (measurable_localizedOdometer hd _ n _)).div_const _

/-- A measurable quantity independent of a resampled atomless coordinate cannot tie it. -/
theorem ae_ne_of_update_invariant {ι : Type*} [DecidableEq ι]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (i : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    (hupdate : ∀ ξ z, F (Function.update ξ i z) = F ξ) :
    ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ι => ν), ξ i ≠ F ξ := by
  set P := Measure.infinitePi (fun _ : ι => ν)
  have hup := LatticeProb.measurePreserving_update_infinitePi (fun _ : ι => ν) i
  have hset : MeasurableSet {ξ : ι → ℝ | ξ i = F ξ} :=
    measurableSet_eq_fun (measurable_pi_apply i) hF
  rw [ae_iff]
  change P {ξ : ι → ℝ | ¬ξ i ≠ F ξ} = 0
  simp only [not_not]
  rw [← hup.measure_preimage hset.nullMeasurableSet]
  have he : (fun q : (ι → ℝ) × ℝ => Function.update q.1 i q.2) ⁻¹'
      {ξ | ξ i = F ξ} = {q : (ι → ℝ) × ℝ | q.2 = F q.1} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Function.update_self, hupdate]
  rw [he, Measure.prod_apply (s := {q : (ι → ℝ) × ℝ | q.2 = F q.1}) (by
    exact measurableSet_eq_fun measurable_snd (hF.comp measurable_fst))]
  have hf (ξ : ι → ℝ) : ν {z : ℝ | z = F ξ} = 0 := hatom (F ξ)
  change (∫⁻ ξ, ν {z : ℝ | z = F ξ} ∂P) = 0
  simp only [hf, lintegral_zero]

/-- Almost surely under the i.i.d. law with atomless marginal `ν`, `origin_contact_iff` upgrades
to a strict inequality: the origin topples at time `n + 1` exactly when the origin-frozen
average at the origin is strictly less than `-ζ 0`. This uses `ae_ne_of_update_invariant` to rule
out the boundary tie, since `originOdometer_update` shows the average does not depend on
`ζ 0`. -/
theorem ae_origin_contact_iff (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (n : ℕ) :
    ∀ᵐ ζ ∂LatticeProb.iidLaw d ν,
      odometerOf ζ (n + 1) 0 = 0 ↔ avg (originOdometer ζ n) 0 < -ζ 0 := by
  classical
  have htie := ae_ne_of_update_invariant ν hatom (0 : Site d)
    (measurable_avg_originOdometer hd n).neg
    (fun ζ z => congrArg (fun f => -avg f 0) (originOdometer_update hd ζ z n))
  filter_upwards [htie] with ζ hζ
  change ζ 0 ≠ -avg (originOdometer ζ n) 0 at hζ
  rw [origin_contact_iff hd ζ n]
  constructor
  · intro h
    by_contra hn
    apply hζ
    push Not at hn
    linarith
  · intro h
    linarith

/-- The increment `E[odometerOf ζ (n+1) 0] - E[odometerOf ζ n 0]` of the mean odometer at the
origin equals the mean of the reflection term `max 0 (-ζ 0 - avg (originOdometer ζ n) 0)`,
combining `meanOdometerOf_succ_sub` with the pointwise identity `origin_reflection_eq`. -/
theorem mean_origin_reflection (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (n : ℕ) :
    (∫ ζ, odometerOf ζ (n + 1) 0 ∂LatticeProb.iidLaw d ν) -
        (∫ ζ, odometerOf ζ n 0 ∂LatticeProb.iidLaw d ν) =
      ∫ ζ, max 0 (-ζ 0 - avg (originOdometer ζ n) 0) ∂LatticeProb.iidLaw d ν := by
  rw [meanOdometerOf_succ_sub hd ν hint hmean hpos n]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => origin_reflection_eq hd ζ n)

/-- Packages the almost-sure contact criterion `ae_origin_contact_iff`, the almost-sure
reflection identity `origin_reflection_eq`, and the mean increment identity
`mean_origin_reflection` for the origin, transported from the noise-indexed odometer
`odometerOf` to the mass-indexed `odometer` on `centeredMassLaw` via the `scenery` map. -/
theorem origin_frozen_identities (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν)
    (hmean : ∫ z, z ∂ν = 0) (n : ℕ) :
    (∀ᵐ σ ∂centeredMassLaw d ν,
      odometer σ (n + 1) 0 = 0 ↔ avg (originOdometer (scenery d σ) n) 0 < -scenery d σ 0) ∧
    (∀ᵐ σ ∂centeredMassLaw d ν,
      max 0 (-scenery d σ 0 - avg (odometer σ n) 0) =
        max 0 (-scenery d σ 0 - avg (originOdometer (scenery d σ) n) 0)) ∧
    meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n =
      ∫ σ, max 0 (-scenery d σ 0 - avg (originOdometer (scenery d σ) n) 0)
        ∂centeredMassLaw d ν := by
  refine ⟨?_, Filter.Eventually.of_forall (fun σ => ?_), ?_⟩
  · have h := ae_origin_contact_iff hd ν hatom n
    rw [← map_scenery_centeredMassLaw d ν hd] at h
    have hs := ae_of_ae_map (measurable_scenery d).aemeasurable h
    filter_upwards [hs] with σ hσ
    simpa only [odometer_eq_odometerOf] using hσ
  · rw [odometer_eq_odometerOf]
    exact origin_reflection_eq hd (scenery d σ) n
  · rw [meanOdometer_eq d ν hd, meanOdometer_eq d ν hd,
      integral_scenery d ν hd
        (F := fun ζ : Site d → ℝ => max 0 (-ζ 0 - avg (originOdometer ζ n) 0))
        ((measurable_const.max ((measurable_pi_apply (0 : Site d)).neg.sub
          (measurable_avg_originOdometer hd n))).aestronglyMeasurable)]
    have hpos : Integrable (fun z : ℝ => max z 0) ν :=
      hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
    exact mean_origin_reflection hd ν hint hmean hpos n

end Sandpile
