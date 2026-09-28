import Sandpile.Support.LinCov

/-!
# Escape probability of the simple random walk

The escape probability of the simple random walk is the reciprocal of the Green function at the
origin, in the form the last-visit estimate `sandpile.tex:4760-4776` (label
`lem:dgt4-weighted-last-visits`) needs: the paper's proof uses that the mean of `I_i^∞` is
`P_0(tau_0^+ = infinity) = G(0,0)^{-1}`.

The identity `escProb_eq` is the one-step decomposition of the walk. Splitting the increments at
time one, the walk returns to the origin exactly when the walk started at its first increment
ever reaches the origin, and the chance of that is `G(x,0)/G(0,0)` by the shared library's
hitting-probability theorem. Averaging over the `2d` first increments and using the Green
function equation at the origin turns this into `1 - G(0,0)^{-1}`.
-/

open MeasureTheory Filter Topology

namespace Sandpile
variable {d : ℕ}

/-- The set of increment sequences whose walk from `y` ever reaches the origin. -/
def hitSet (y : Site d) : Set (ℕ → Site d) := {η | ∃ s : ℕ, walkPath y η s = 0}

/-- `walkPath y η s` is a measurable function of the increment sequence `η`, being a finite sum of
coordinate projections shifted by the constant `y`. -/
theorem measurable_walkPath_apply (y : Site d) (s : ℕ) :
    Measurable fun η : ℕ → Site d => walkPath y η s := by
  unfold walkPath
  exact measurable_const.add (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)

/-- `hitSet y` is measurable, being the countable union over `s` of the measurable preimages of
`{0}` under `walkPath y · s`. -/
theorem measurableSet_hitSet (y : Site d) : MeasurableSet (hitSet (d := d) y) := by
  have h : hitSet (d := d) y = ⋃ s : ℕ, (fun η : ℕ → Site d => walkPath y η s) ⁻¹' {0} := by
    ext η; simp [hitSet]
  rw [h]
  exact MeasurableSet.iUnion fun s =>
    (measurable_walkPath_apply y s) (measurableSet_singleton 0)

/-- The joint set behind the one-step decomposition. -/
def hitPair (d : ℕ) : Set ((ℕ → Site d) × (ℕ → Site d)) :=
  {p | ∃ s : ℕ, walkPath (p.1 0) p.2 s = 0}

/-- `hitPair d` is measurable, by the same countable-union-of-preimages argument as
`measurableSet_hitSet` applied to the joint coordinate. -/
theorem measurableSet_hitPair : MeasurableSet (hitPair d) := by
  have h : hitPair d = ⋃ s : ℕ,
      (fun p : (ℕ → Site d) × (ℕ → Site d) => p.1 0 + ∑ j ∈ Finset.range s, p.2 j) ⁻¹' {0} := by
    ext p; simp [hitPair, walkPath]
  rw [h]
  refine MeasurableSet.iUnion fun s => ?_
  have hm : Measurable fun p : (ℕ → Site d) × (ℕ → Site d) =>
      p.1 0 + ∑ j ∈ Finset.range s, p.2 j :=
    ((measurable_pi_apply 0).comp measurable_fst).add
      (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd)
  exact hm (measurableSet_singleton 0)

/-- Under the i.i.d. increment law, the expectation of the indicator of `hitSet y` equals the
simple random walk's hitting probability `LatticeProb.srwHitProb d y`, obtained by transporting
the indicator along `walkPath` to `LatticeProb.hitOrigin` and reading off
`siteWalkLaw_hitOrigin`. -/
theorem integral_indHitSet [NeZero d] (hd : 1 ≤ d) (y : Site d) :
    ∫ η, Set.indicator (hitSet y) (fun _ => (1:ℝ)) η ∂(LatticeProb.incPathLaw d)
      = LatticeProb.srwHitProb d y := by
  rw [show (fun _ => (1:ℝ)) = (1 : (ℕ → Site d) → ℝ) from rfl,
    integral_indicator_one (measurableSet_hitSet y), measureReal_def]
  have hpre : walkPath (d := d) y ⁻¹' LatticeProb.hitOrigin d = hitSet y := by
    ext η; simp [hitSet, LatticeProb.hitOrigin]
  have hmap : LatticeProb.incPathLaw d (hitSet (d := d) y)
      = walkLaw d y (LatticeProb.hitOrigin d) := by
    rw [show walkLaw d y = (LatticeProb.incPathLaw d).map (walkPath (d := d) y) from rfl,
      Measure.map_apply (measurable_walkPath y) LatticeProb.measurableSet_hitOrigin, hpre]
  rw [hmap, show walkLaw d y = LatticeProb.siteWalkLaw d y from rfl,
    LatticeProb.siteWalkLaw_hitOrigin hd y,
    ENNReal.toReal_ofReal (LatticeProb.srwHitProb_nonneg y)]

/-- Shifting the increment sequence by one and restarting the walk at `ξ 0` reproduces the
origin-started walk one step later: `walkPath (ξ 0) (shiftInc 1 ξ) s = walkPath 0 ξ (s + 1)`. -/
theorem walkPath_shift_one (ξ : ℕ → Site d) (s : ℕ) :
    walkPath (ξ 0) (LatticeProb.shiftInc 1 ξ) s = walkPath (0 : Site d) ξ (s + 1) := by
  simp only [walkPath, LatticeProb.shiftInc, zero_add]
  rw [show s + 1 = 1 + s from Nat.add_comm s 1, Finset.sum_range_add]
  simp

/-- The one-step decomposition: the split pair of the first increment and the shifted tail lies
in `hitPair d` exactly when the origin-started walk along `ξ` eventually leaves `noRetEver d`,
i.e. returns to the origin at some positive time. -/
theorem hitPair_iff (ξ : ℕ → Site d) :
    ((LatticeProb.truncInc 1 ξ, LatticeProb.shiftInc 1 ξ) ∈ hitPair d)
      ↔ walkPath (0 : Site d) ξ ∉ noRetEver d := by
  have h0 : (LatticeProb.truncInc (d := d) 1 ξ) 0 = ξ 0 := by
    simp [LatticeProb.truncInc]
  have hzero : walkPath (0 : Site d) ξ 0 = 0 := by simp [walkPath]
  simp only [hitPair, Set.mem_setOf_eq, h0, noRetEver, Set.mem_setOf_eq, not_forall, hzero]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s + 1, by omega, ?_⟩
    rw [← walkPath_shift_one ξ s] at *
    simpa using hs
  · rintro ⟨r, hr1, hr2⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    exact ⟨s, by rw [walkPath_shift_one ξ s]; simpa using hr2⟩

/-- **Main theorem.** For `d ≥ 3`, the escape probability `escProb d` equals `1 / green d 0 0`.
The proof splits the increments at time one via `hitPair_iff` to express the survival indicator
as `1` minus a hitting indicator, integrates using `integral_indHitSet` and the independence of
the increments, and identifies the result with `Sandpile.External.Sec16.return_probability`. -/
theorem escProb_eq [NeZero d] (hd : 3 ≤ d) : escProb d = 1 / green d 0 0 := by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  set Φ : (ℕ → Site d) → (ℕ → Site d) → ℝ :=
    fun a b => Set.indicator (hitPair d) (fun _ => (1:ℝ)) (a, b) with hΦ
  have hΦmeas : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = Set.indicator (hitPair d) (fun _ => (1:ℝ)) := by
      funext p; rfl
    rw [this]
    exact measurable_const.indicator measurableSet_hitPair
  have hΦb : ∀ a b, ‖Φ a b‖ ≤ 1 := by
    intro a b
    rcases Classical.em ((a, b) ∈ hitPair d) with hm | hm
    · simp [hΦ, Set.indicator_of_mem hm]
    · simp [hΦ, Set.indicator_of_notMem hm]
  -- the survival indicator as one minus the hitting indicator
  have hpt : ∀ ξ : ℕ → Site d,
      survInd 0 (walkPath (0 : Site d) ξ)
        = 1 - Φ (LatticeProb.truncInc 1 ξ) (LatticeProb.shiftInc 1 ξ) := by
    intro ξ
    rw [survInd_zero]
    show Set.indicator (noRetEver d) (fun _ => (1:ℝ)) (walkPath (0 : Site d) ξ)
      = 1 - Set.indicator (hitPair d) (fun _ => (1:ℝ))
        (LatticeProb.truncInc 1 ξ, LatticeProb.shiftInc 1 ξ)
    rcases Classical.em (walkPath (0 : Site d) ξ ∈ noRetEver d) with hm | hm
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_notMem (fun hc => (hitPair_iff ξ).mp hc hm)]
      norm_num
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_mem ((hitPair_iff ξ).mpr hm)]
      norm_num
  have hstep : escProb d = 1 - ∫ ξ, Φ (LatticeProb.truncInc 1 ξ) (LatticeProb.shiftInc 1 ξ)
      ∂(LatticeProb.incPathLaw d) := by
    rw [← integral_survInd (d := d) 0, integral_walkLaw_zero (measurable_survInd 0),
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hint : Integrable (fun ξ : ℕ → Site d =>
        Φ (LatticeProb.truncInc 1 ξ) (LatticeProb.shiftInc 1 ξ)) (LatticeProb.incPathLaw d) := by
      refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ξ => hΦb _ _)
      exact (hΦmeas.comp (((LatticeProb.measurable_truncInc 1).prodMk
        (LatticeProb.measurable_shiftInc 1)))).aestronglyMeasurable
    rw [integral_sub (integrable_const 1) hint, integral_const]
    simp
  rw [hstep, LatticeProb.integral_truncInc_shiftInc d 1 Φ hΦmeas hΦb]
  have hinner : ∀ ξ : ℕ → Site d,
      (∫ η, Φ (LatticeProb.truncInc 1 ξ) η ∂(LatticeProb.incPathLaw d))
        = LatticeProb.srwHitProb d (ξ 0) := by
    intro ξ
    have h0 : (LatticeProb.truncInc (d := d) 1 ξ) 0 = ξ 0 := by simp [LatticeProb.truncInc]
    have hset : ∀ η : ℕ → Site d,
        Φ (LatticeProb.truncInc 1 ξ) η
          = Set.indicator (hitSet (ξ 0)) (fun _ => (1:ℝ)) η := by
      intro η
      show Set.indicator (hitPair d) (fun _ => (1:ℝ)) (LatticeProb.truncInc 1 ξ, η)
        = Set.indicator (hitSet (ξ 0)) (fun _ => (1:ℝ)) η
      rcases Classical.em (η ∈ hitSet (d := d) (ξ 0)) with hm | hm
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem]
        simpa [hitPair, hitSet, h0] using hm
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem]
        simpa [hitPair, hitSet, h0] using hm
    rw [integral_congr_ae (Filter.Eventually.of_forall hset), integral_indHitSet hd1]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  have hmarg : ∫ ξ, LatticeProb.srwHitProb d (ξ 0) ∂(LatticeProb.incPathLaw d)
      = ∫ e, LatticeProb.srwHitProb d e ∂(stepLaw d) := by
    haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd1
    have heval : (Measure.infinitePi fun _ : ℕ => stepLaw d).map (fun ξ : ℕ → Site d => ξ 0)
        = stepLaw d := Measure.infinitePi_map_eval _ 0
    have hmap := integral_map (μ := Measure.infinitePi fun _ : ℕ => stepLaw d)
      (φ := fun ξ : ℕ → Site d => ξ 0) (f := LatticeProb.srwHitProb d)
      (measurable_pi_apply 0).aemeasurable
      (measurable_of_countable (LatticeProb.srwHitProb d)).aestronglyMeasurable
    rw [heval] at hmap
    exact hmap.symm
  rw [hmarg, integral_stepLaw_apply, Sandpile.External.Sec16.return_probability d hd]
  have hG : (1 : ℝ) ≤ green d 0 0 := by
    have := LatticeProb.one_le_srwGreenInf_origin (d := d) hd
    rw [Sandpile.External.Sec16.green_eq d 0 0, sub_zero]
    exact this
  field_simp
  ring

end Sandpile
