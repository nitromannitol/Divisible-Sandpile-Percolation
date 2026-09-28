import Sandpile.Support.LimKernelBounds

/-!
# Convergence in probability of the ball-stopped field

The `L²` distance between the ball-stopped kernel and the Green function of the
ball tends to zero, and with it the probability that the two fields differ.

The kernel `k_T` of the ball-stopped field satisfies `0 ≤ k_T ≤ G` with
`G = 2d · ballKernel` (`Sandpile/Support/LimKernelBounds.lean`), and its mass
increases to the mass of `G`. For a difference `D = G - k_T` squeezed between `0`
and `G` the elementary split

  `D² ≤ D·G ≤ M·D + G²·1_{G > M}`

turns the convergence of the mass, which is an `L¹` statement, into convergence in
`L²`: choose `M` so that the tail `∫_{G>M} G²` is small, which is possible because
`G²` is integrable, and then let the horizon grow. The white-noise average of a
kernel of small `L²` norm is small in probability, by Chebyshev's inequality and
the covariance clause of the white noise, so the ball-stopped field converges in
probability to the ball field at each point of the plane.

What is NOT proved here is the uniformity of that convergence over the points of a
compact rectangle, which is what `Sandpile.Support.BallStoppedApproximation` asks
for.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The elementary split of the square -/

/-- For `0 ≤ K ≤ G` and `0 ≤ M`, the square of the difference is at most `M` times the
difference, plus the square of `G` where `G` exceeds `M`. -/
theorem sq_sub_le_split {G K M : ℝ} (h0 : 0 ≤ K) (hKG : K ≤ G) (hM : 0 ≤ M) :
    (G - K) ^ 2 ≤ M * (G - K) + (if M < G then G ^ 2 else 0) := by
  have hD0 : 0 ≤ G - K := by linarith
  have hDG : G - K ≤ G := by linarith
  by_cases hc : M < G
  · rw [if_pos hc]
    nlinarith
  · rw [if_neg hc]
    rw [not_lt] at hc
    nlinarith

/-- The integral form of `sq_sub_le_split`: for `0 ≤ K ≤ G` almost everywhere,
`∫ (G-K)² ≤ M ∫ (G-K) + ∫_{G>M} G²`, by integrating the pointwise split. -/
theorem integral_sq_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {G K : α → ℝ}
    (hG : Measurable G) (hGsq : Integrable (fun y => G y ^ 2) μ)
    (hDm : AEStronglyMeasurable (fun y => G y - K y) μ)
    (hD : Integrable (fun y => G y - K y) μ)
    (hK0 : 0 ≤ᵐ[μ] K) (hKG : K ≤ᵐ[μ] G) {M : ℝ} (hM : 0 ≤ M) :
    (∫ y, (G y - K y) ^ 2 ∂μ)
      ≤ M * (∫ y, (G y - K y) ∂μ) + ∫ y in {z | M < G z}, G y ^ 2 ∂μ := by
  have hset : MeasurableSet {z | M < G z} := measurableSet_lt measurable_const hG
  have hbound : ∀ᵐ y ∂μ, (G y - K y) ^ 2
      ≤ M * (G y - K y) + {z | M < G z}.indicator (fun z => G z ^ 2) y := by
    filter_upwards [hK0, hKG] with y hy0 hyG
    simp only [Pi.zero_apply] at hy0
    have h := sq_sub_le_split hy0 hyG hM
    by_cases hc : M < G y
    · rw [Set.indicator_of_mem (show y ∈ {z | M < G z} from hc)]
      rwa [if_pos hc] at h
    · rw [Set.indicator_of_notMem (show y ∉ {z | M < G z} from hc)]
      rwa [if_neg hc] at h
  have hDsq : Integrable (fun y => (G y - K y) ^ 2) μ := by
    refine Integrable.mono' hGsq (hDm.pow 2) ?_
    filter_upwards [hK0, hKG] with y hy0 hyG
    simp only [Pi.zero_apply] at hy0
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hD0 : 0 ≤ G y - K y := by linarith
    nlinarith
  have hrhs : Integrable
      (fun y => M * (G y - K y) + {z | M < G z}.indicator (fun z => G z ^ 2) y) μ :=
    (hD.const_mul M).add (hGsq.indicator hset)
  have hmono := integral_mono_ae hDsq hrhs hbound
  rw [integral_add (hD.const_mul M) (hGsq.indicator hset), integral_const_mul,
    integral_indicator hset] at hmono
  exact hmono

/-- The square of an integrable square has a small tail above a large level. -/
theorem exists_setIntegral_gt_sq_lt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {G : α → ℝ} (hG : Measurable G) (hGsq : Integrable (fun y => G y ^ 2) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∫ y in {z | M < G z}, G y ^ 2 ∂μ) < ε := by
  have hmeas : ∀ n : ℕ, MeasurableSet {z | (n : ℝ) < G z} := fun n =>
    measurableSet_lt measurable_const hG
  have hlim : Tendsto
      (fun n : ℕ => ∫ y, {z | (n : ℝ) < G z}.indicator (fun z => G z ^ 2) y ∂μ)
      atTop (𝓝 0) := by
    have hzero : (0 : ℝ) = ∫ _y : α, (0 : ℝ) ∂μ := by simp
    rw [hzero]
    refine tendsto_integral_of_dominated_convergence (fun y => G y ^ 2)
      (fun n => (hGsq.aestronglyMeasurable.indicator (hmeas n))) hGsq (fun n => ?_) ?_
    · filter_upwards with y
      rw [Real.norm_eq_abs]
      by_cases hy : (n : ℝ) < G y
      · rw [Set.indicator_of_mem (show y ∈ {z | (n : ℝ) < G z} from hy),
          abs_of_nonneg (sq_nonneg _)]
      · rw [Set.indicator_of_notMem (show y ∉ {z | (n : ℝ) < G z} from hy), abs_zero]
        exact sq_nonneg _
    · filter_upwards with y
      obtain ⟨N, hN⟩ := exists_nat_gt (G y)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      refine (Set.indicator_of_notMem (show y ∉ {z | (n : ℝ) < G z} from ?_) _).symm
      simp only [Set.mem_setOf_eq, not_lt]
      exact le_trans hN.le (by exact_mod_cast hn)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨(n : ℝ), Nat.cast_nonneg n, ?_⟩
  rwa [integral_indicator (hmeas n)] at hn


/-! ### The `L²` convergence of the kernel -/

/-- `ballKernel d s u` is measurable, as the translate of the measurable
`centredKernel d s` by a fixed shift. -/
theorem measurable_ballKernel (d : ℕ) (s : ℝ) (u : Space 2) :
    Measurable (ballKernel d s u) := by
  rw [ballKernel_eq_centredKernel]
  exact (measurable_centredKernel d s).comp (measurable_const.sub measurable_id)

/-- The square of `G = 2d · ballKernel d s u` is integrable for `d ∈ {2,3}` and
`s > 0`, since `ballKernel d s u` is in `L²` by `memLp_ballKernel`. -/
theorem integrable_sq_ballGreen {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ} (hs : 0 < s)
    (u : Space 2) :
    Integrable (fun y => (2 * (d : ℝ) * ballKernel d s u y) ^ 2)
      (volume : Measure (Space d)) := by
  have h := (memLp_two_iff_integrable_sq
    (measurable_ballKernel d s u).aestronglyMeasurable).mp (memLp_ballKernel hd hs u)
  refine (h.const_mul ((2 * (d : ℝ)) ^ 2)).congr (Eventually.of_forall fun y => ?_)
  ring

variable {ΩB : Type}

/-- **The kernel of the ball-stopped field converges to the Green function of the ball in
`L²`.** -/
theorem tendsto_integral_sq_ballStoppedKernel
    (hOcc : Sandpile.External.BallOccupationDensity) [MeasurableSpace ΩB] {d : ℕ}
    (hd : d = 2 ∨ d = 3) (PB : Measure ΩB) [IsProbabilityMeasure PB]
    {B : Space d → ℝ≥0 → ΩB → Space d} (hB : ∀ y, IsBrownian d y (B y) PB)
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s : ℝ} (hs : 0 < s) (u : Space 2) :
    Tendsto (fun T : ℝ => ∫ y, (2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ^ 2) atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  set G : Space d → ℝ := fun y => 2 * (d : ℝ) * ballKernel d s u y with hGdef
  have hGmeas : Measurable G := (measurable_ballKernel d s u).const_mul _
  have hGsq : Integrable (fun y => G y ^ 2) (volume : Measure (Space d)) :=
    integrable_sq_ballGreen hd hs u
  have hGint : Integrable G (volume : Measure (Space d)) :=
    (integrable_ballKernel hd hs u).const_mul _
  -- the mass of the difference tends to zero
  have hmass : Tendsto (fun T : ℝ => ∫ y, (G y - ballStoppedKernel d PB B s T u y)) atTop
      (𝓝 0) := by
    have hlim := tendsto_integral_ballStoppedKernel hOcc hd PB hB hBc hBm hs u
    have hG0 : (∫ y, G y) = 2 * (d : ℝ) * ∫ y, ballKernel d s u y := by
      rw [hGdef, integral_const_mul]
    have hdiff : Tendsto
        (fun T : ℝ => (∫ y, G y) - ∫ y, ballStoppedKernel d PB B s T u y) atTop
        (𝓝 ((∫ y, G y) - 2 * (d : ℝ) * ∫ y, ballKernel d s u y)) :=
      tendsto_const_nhds.sub hlim
    rw [hG0, sub_self] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [← hG0]
    exact (integral_sub hGint
      (integrable_ballStoppedKernel hd1 PB hBc hBm (s := s) hT u)).symm
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hM0, hMlt⟩ := exists_setIntegral_gt_sq_lt hGmeas hGsq (half_pos hε)
  have hsmall : Tendsto (fun T : ℝ => M * ∫ y, (G y - ballStoppedKernel d PB B s T u y)) atTop
      (𝓝 0) := by
    have := hmass.const_mul M
    rwa [mul_zero] at this
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (hsmall.eventually (gt_mem_nhds (half_pos hε)))] with T hT hTsmall
  have hK0 := ae_nonneg_ballStoppedKernel hd1 PB hB hBc hBm (s := s) hT u
  have hKG := ae_ballStoppedKernel_le hOcc hd PB hB hBc hBm hs hT u
  have hKint : Integrable (ballStoppedKernel d PB B s T u) (volume : Measure (Space d)) :=
    integrable_ballStoppedKernel hd1 PB hBc hBm (s := s) hT u
  have hD : Integrable (fun y => G y - ballStoppedKernel d PB B s T u y)
      (volume : Measure (Space d)) := hGint.sub hKint
  have hsplit := integral_sq_sub_le hGmeas hGsq hD.aestronglyMeasurable hD hK0 hKG hM0
  have hnonneg : 0 ≤ ∫ y, (G y - ballStoppedKernel d PB B s T u y) ^ 2 :=
    integral_nonneg fun y => sq_nonneg _
  rw [Real.norm_of_nonneg hnonneg]
  calc (∫ y, (G y - ballStoppedKernel d PB B s T u y) ^ 2)
      ≤ M * (∫ y, (G y - ballStoppedKernel d PB B s T u y))
        + ∫ y in {z | M < G z}, G y ^ 2 := hsplit
    _ < ε / 2 + ε / 2 := by
        exact add_lt_add hTsmall hMlt
    _ = ε := add_halves ε


/-! ### Chebyshev for the white noise, and the convergence in probability -/

/-- The white-noise average of a square-integrable kernel exceeds a level with probability at
most the `L²` norm of the kernel over the square of the level. -/
theorem measure_abs_whiteNoise_gt_le {ΩW : Type*} [MeasurableSpace ΩW] {d : ℕ}
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (f : Space d → ℝ)
    (hf : MemLp f 2 (volume : Measure (Space d))) {c : ℝ} (hc : 0 < c) :
    PW {ω | c < |W f ω|} ≤ ENNReal.ofReal ((∫ y, f y ^ 2) / c ^ 2) := by
  have hmem : MemLp (W f) 2 PW := (hW.gaussian.hasGaussianLaw_eval f).memLp_two
  have hsq : Integrable (fun ω => (W f ω) ^ 2) PW :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have hval : (∫ ω, (W f ω) ^ 2 ∂PW) = ∫ y, f y ^ 2 := by
    have h := hW.cov f f hf hf
    simpa only [sq] using h
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := PW) (f := fun ω => (W f ω) ^ 2)
    (Eventually.of_forall fun ω => sq_nonneg _) hsq (c ^ 2)
  rw [hval] at hmarkov
  have hsub : {ω | c < |W f ω|} ⊆ {ω | c ^ 2 ≤ (W f ω) ^ 2} := by
    intro ω hω
    have hω' : c < |W f ω| := hω
    have h : c ^ 2 ≤ |W f ω| ^ 2 := by nlinarith [abs_nonneg (W f ω)]
    rwa [sq_abs] at h
  have hle : PW.real {ω | c < |W f ω|} ≤ (∫ y, f y ^ 2) / c ^ 2 := by
    have h1 : PW.real {ω | c < |W f ω|} ≤ PW.real {ω | c ^ 2 ≤ (W f ω) ^ 2} :=
      measureReal_mono hsub (measure_ne_top _ _)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hmarkov, h1, measureReal_nonneg (μ := PW) (s := {ω | c < |W f ω|})]
  calc PW {ω | c < |W f ω|} = ENNReal.ofReal (PW.real {ω | c < |W f ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ((∫ y, f y ^ 2) / c ^ 2) := ENNReal.ofReal_le_ofReal hle

/-- The difference of the two fields is the white-noise average against the difference of
their kernels. -/
theorem ae_whiteNoise_ballField_sub {ΩW : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {W : (Space d → ℝ) → ΩW → ℝ} (hW : IsWhiteNoise d W PW) {Z : ℝ → Space d → ΩW → ℝ}
    (hmod : ∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω)
    (hZc : ContinuousHeatPotential d Z PW)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hs : 0 < s) (hT : 0 < T) (u : Space 2) :
    (fun ω => 2 * (d : ℝ) * (ballField d W s u ω - ballStoppedField d Z PB B s T u ω))
      =ᵐ[PW] W (fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd3 : d ≤ 3 := by rcases hd with h | h <;> omega
  have hmemG : MemLp (fun y => 2 * (d : ℝ) * ballKernel d s u y) 2
      (volume : Measure (Space d)) := (memLp_ballKernel hd hs u).const_mul _
  have hmemK : MemLp (ballStoppedKernel d PB B s T u) 2 (volume : Measure (Space d)) :=
    memLp_ballStoppedKernel hd1 hd3 PB hBc hBm hT.le u
  have hsmul : ((2 * (d : ℝ)) • ballKernel d s u)
      = fun y => 2 * (d : ℝ) * ballKernel d s u y := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul]
  have hG : (fun ω => 2 * (d : ℝ) * ballField d W s u ω) =ᵐ[PW]
      W (fun y => 2 * (d : ℝ) * ballKernel d s u y) := by
    have h := hW.smul (2 * (d : ℝ)) (ballKernel d s u) (memLp_ballKernel hd hs u)
    rw [hsmul] at h
    exact h.symm
  have hK := ae_ballStoppedField_eq_whiteNoise hd1 hd3 hW hmod hZc PB hBc hBm (s := s) hT u
  have hadd := hW.add (fun y => 2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) (ballStoppedKernel d PB B s T u)
    (hmemG.sub hmemK) hmemK
  have hsum : ((fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) + ballStoppedKernel d PB B s T u)
      = fun y => 2 * (d : ℝ) * ballKernel d s u y := by
    funext y
    simp only [Pi.add_apply]
    ring
  rw [hsum] at hadd
  filter_upwards [hG, hK, hadd] with ω h1 h2 h3
  have : 2 * (d : ℝ) * ballField d W s u ω
      = W (fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ω
        + W (ballStoppedKernel d PB B s T u) ω := by rw [h1, h3]
  rw [mul_sub, this, ← h2]
  ring

/-- **The ball-stopped field converges to the ball field in probability**, at each point of
the plane and at each scale.  This is the pointwise half of the sentence
`sandpile.tex:2511-2513`; the uniformity over a compact rectangle is not proved here. -/
theorem eventually_measure_ballStoppedField_sub_le
    (hOcc : Sandpile.External.BallOccupationDensity) {ΩW : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] {d : ℕ} (hd : d = 2 ∨ d = 3) {PW : Measure ΩW}
    [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ} (hW : IsWhiteNoise d W PW)
    {Z : ℝ → Space d → ΩW → ℝ}
    (hmod : ∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω)
    (hZc : ContinuousHeatPotential d Z PW)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s : ℝ} (hs : 0 < s) {c δ : ℝ} (hc : 0 < c)
    (hδ : 0 < δ) (u : Space 2) :
    ∀ᶠ T : ℝ in atTop,
      PW {ω | |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ
        ≤ ENNReal.ofReal δ := by
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd3 : d ≤ 3 := by rcases hd with h | h <;> omega
  have hd0 : (0 : ℝ) < 2 * (d : ℝ) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    linarith
  have hcc : 0 < 2 * (d : ℝ) * c := by positivity
  have hlim := tendsto_integral_sq_ballStoppedKernel hOcc hd PB hB hBc hBm hs u
  have hpos : 0 < δ * (2 * (d : ℝ) * c) ^ 2 := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds hpos)]
    with T hT hTsmall
  have hae := ae_whiteNoise_ballField_sub hd hW hmod hZc PB hBc hBm hs hT u
  have hmemD : MemLp (fun y => 2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) 2 (volume : Measure (Space d)) :=
    ((memLp_ballKernel hd hs u).const_mul _).sub
      (memLp_ballStoppedKernel hd1 hd3 PB hBc hBm hT.le u)
  have hsub : {ω | |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| ≤ c}ᶜ
      ≤ᵐ[PW] {ω | 2 * (d : ℝ) * c < |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ω|} := by
    filter_upwards [hae] with ω hω hmem
    have hgt : c < |ballStoppedField d Z PB B s T u ω - ballField d W s u ω| :=
      lt_of_not_ge hmem
    have hval : |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ω|
        = 2 * (d : ℝ) * |ballField d W s u ω - ballStoppedField d Z PB B s T u ω| := by
      rw [← hω, abs_mul, abs_of_nonneg hd0.le]
    show 2 * (d : ℝ) * c < _
    rw [hval, abs_sub_comm]
    exact mul_lt_mul_of_pos_left hgt hd0
  refine le_trans (measure_mono_ae hsub) ?_
  refine le_trans (measure_abs_whiteNoise_gt_le hW _ hmemD hcc) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by positivity)]
  exact le_of_lt hTsmall

end Sandpile.Support
