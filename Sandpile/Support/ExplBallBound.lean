/-
The two boundedness inputs of `lem:brownian-ball-localization`
(`sandpile.tex:1647-1658`): the terminal reward is bounded above on the
`A`-neighbourhood of the compact set `K`, and the attainable stopping payoffs of
the field are bounded above at every starting point of the neighbourhood.

The paper's proof bounds the value at `u` by the value at the nearest point of
`K` plus the exit-time tail; the two facts here are what that comparison needs.
-/
import Sandpile.Support.ExplBallGaussian
import Sandpile.Support.ExplBrownianEnvelope

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Pointwise

namespace Sandpile.Continuum
open Sandpile.Support

variable {Ω : Type*} [MeasurableSpace Ω] {ΩW : Type*} [MeasurableSpace ΩW]
  {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The terminal reward is bounded above on the `A`-neighbourhood of a compact set, by
continuity on the time strip and compactness of the neighbourhood. -/
theorem exists_bound_on_neighbourhood (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 ≤ T)
    (K : Set (Space d)) (hK : IsCompact K)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∃ M : ℝ, ∀ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) → h T z ≤ M := by
  have hcomp : IsCompact (K + Metric.closedBall (0 : Space d) A) :=
    hK.add (isCompact_closedBall 0 A)
  have hcont : ContinuousOn (fun z : Space d => h T z) (K + Metric.closedBall (0 : Space d) A) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (by
      intro z hz
      exact ⟨⟨hT, le_refl T⟩, trivial⟩)
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  exact ⟨M, fun z hz => (le_abs_self _).trans (hM z (by
    rcases hz with ⟨y, hy, hyz⟩
    exact Set.mem_add.mpr ⟨y, hy, z - y, by simpa using hyz, by abel⟩))⟩

/-- Boundedness of the far values from a bound on the terminal reward near `K` and a uniform
bound on the discounts. -/
theorem bddAbove_farValues_of_bddAbove (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A M S : ℝ) (K : Set (Space d))
    (hM : ∀ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) → h T z ≤ M)
    (hS : ∀ z : Space d, BddAbove (stoppingPayoffs (B z) P h T) ∧
      sSup (stoppingPayoffs (B z) P h T) ≤ S) :
    BddAbove (farValues B P h T A K) := by
  refine ⟨M + S, ?_⟩
  rintro v ⟨z, hz, rfl⟩
  unfold Sandpile.Continuum.brownianValue
  have h1 : h T z ≤ M := hM z hz
  have h2 : Sandpile.Continuum.brownianDiscount (B z) P h T ≤ S := by
    rw [Sandpile.Continuum.brownianDiscount_eq_sSup]
    exact (hS z).2
  linarith

/-- Samplewise polynomial growth of a continuous field, with an amplitude bounded above, bounds
the attainable stopping payoffs above. -/
theorem bddAbove_stoppingPayoffs_of_samplewise_growth {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Space d} {x : Space d} (hB : IsBrownian d x B P)
    (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (h : ℝ → Space d → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (C : Ω → ℝ) (c : ℝ) (hCb : ∀ᵐ ω ∂P, C ω ≤ c) (p : ℕ)
    (hg : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y, ‖h v y‖ ≤ C ω * (1 + ‖y - x‖) ^ p) :
    BddAbove (stoppingPayoffs B P h T) := by
  have hD : Integrable (fun ω => c * (1 + brownianPathRadius B x T.toNNReal ω) ^ p) P :=
    (integrable_brownian_pathRadius_pow hB hm hBc T.toNNReal p).const_mul c
  refine bddAbove_stoppingPayoffs_of_integrable_envelope hB h T hc
    (fun ω => c * (1 + brownianPathRadius B x T.toNNReal ω) ^ p) hD ?_
  filter_upwards [hg, hCb] with ω hω hCω
  intro r hr
  have hr' : r ≤ T.toNNReal := NNReal.coe_le_coe.1 (by rw [Real.coe_toNNReal T hT]; exact hr)
  have h2 := hω (T.toNNReal - r)
    (by rw [NNReal.coe_sub hr', Real.coe_toNNReal T hT]; linarith [NNReal.coe_nonneg r])
    (B ↑r ω)
  rw [NNReal.coe_sub hr', Real.coe_toNNReal T hT] at h2
  have hCnn : 0 ≤ C ω := by
    by_contra hneg
    push Not at hneg
    have h3 : (0:ℝ) < (1 + ‖B ↑r ω - x‖) ^ p := by positivity
    have h4 := mul_neg_of_neg_of_pos hneg h3
    linarith [norm_nonneg (h (T - ↑r) (B ↑r ω)), h2, h4]
  calc ‖h (T - ↑r) (B ↑r ω)‖
      ≤ C ω * (1 + ‖B ↑r ω - x‖) ^ p := h2
    _ ≤ c * (1 + ‖B ↑r ω - x‖) ^ p := mul_le_mul_of_nonneg_right hCω (by positivity)
    _ ≤ c * (1 + brownianPathRadius B x T.toNNReal ω) ^ p :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity)
            (by linarith [norm_le_pathRadius B hBc x T.toNNReal ω hr']) p)
          (by linarith)

/-- A pointwise polynomial bound on the field, with a uniform moment bound on the Brownian
maximum, bounds the Brownian value at the starting point. -/
theorem brownianValue_le_of_pointwise_bound {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Space d} {z : Space d} (hB : IsBrownian d z B P)
    (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (h : ℝ → Space d → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (C M : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hg : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y, ‖h v y‖ ≤ C * (1 + ‖y - z‖) ^ p)
    (hM : ∫ ω, (1 + brownianPathRadius B z T.toNNReal ω) ^ p ∂P ≤ M) :
    brownianValue B P h T z ≤ 2 * C * M := by
  have hR (ω : Ω) : 0 ≤ brownianPathRadius B z T.toNNReal ω :=
    (norm_nonneg (B 0 ω - z)).trans (norm_le_pathRadius B hBc z T.toNNReal ω (s := 0) zero_le)
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ ∫ ω, (1 + brownianPathRadius B z T.toNNReal ω) ^ p ∂P := by
      have := integral_mono_ae (integrable_const (1 : ℝ))
        (integrable_brownian_pathRadius_pow hB hm hBc T.toNNReal p)
        (Filter.Eventually.of_forall fun ω => by
          simpa using one_le_pow₀ (by linarith [hR ω] :
            (1 : ℝ) ≤ 1 + brownianPathRadius B z T.toNNReal ω))
      simpa using this
    linarith
  have hD : Integrable (fun ω => C * (1 + brownianPathRadius B z T.toNNReal ω) ^ p) P :=
    (integrable_brownian_pathRadius_pow hB hm hBc T.toNNReal p).const_mul C
  have hdom : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
      ‖h (T - r) (B r ω)‖ ≤ C * (1 + brownianPathRadius B z T.toNNReal ω) ^ p := by
    filter_upwards with ω
    intro r hr
    have hr' : r ≤ T.toNNReal := NNReal.coe_le_coe.1 (by rw [Real.coe_toNNReal T hT]; exact hr)
    have hstep : ‖h (T - r) (B r ω)‖ ≤ C * (1 + ‖B r ω - z‖) ^ p := by
      have h1 := hg (T.toNNReal - r) (by
        rw [NNReal.coe_sub hr', Real.coe_toNNReal T hT]
        linarith [NNReal.coe_nonneg r]) (B r ω)
      rw [NNReal.coe_sub hr', Real.coe_toNNReal T hT] at h1
      exact h1
    exact hstep.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by linarith [norm_le_pathRadius B hBc z T.toNNReal ω hr']) p) hC)
  have hbdd : BddAbove (stoppingPayoffs B P h T) := by
    refine bddAbove_stoppingPayoffs_of_integrable_envelope hB h T hc
      (fun ω => C * (1 + brownianPathRadius B z T.toNNReal ω) ^ p) hD hdom
  have h0 : h T z ≤ C * M := by
    have h1 := hg T.toNNReal (le_of_eq (Real.coe_toNNReal T hT)) z
    rw [Real.coe_toNNReal T hT] at h1
    have h2 : (1 + ‖z - z‖) ^ p = 1 := by simp
    rw [h2, mul_one] at h1
    exact (le_abs_self _).trans (h1.trans (le_mul_of_one_le_right hC hM1))
  have hmem : (∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P) ∈ stoppingPayoffs B P h T :=
    ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT, rfl⟩
  have hsup : sSup (stoppingPayoffs B P h T) ≤ C * M := by
    refine csSup_le ⟨_, hmem⟩ ?_
    rintro a ⟨τ, hτ, hτT, rfl⟩
    have ht := hτ.aemeasurable P hB.aemeasurable
    have hy := aemeasurable_stopped_position P hB.aemeasurable
      (isBrownianSpace_of_isBrownian hB).cont ht
    have hm' := aemeasurable_stopped_payoff_of_continuousOn P τ _ ht hy h T hc hτT
    have hbτ : ∀ᵐ ω ∂P, ‖-h (T - τ ω) (B (τ ω) ω)‖ ≤
        C * (1 + brownianPathRadius B z T.toNNReal ω) ^ p := by
      filter_upwards [hdom] with ω hω
      simpa only [norm_neg] using hω (τ ω) (hτT ω)
    have h1 : ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P ≤
        ∫ ω, C * (1 + brownianPathRadius B z T.toNNReal ω) ^ p ∂P :=
      integral_mono_ae (hD.mono' hm'.aestronglyMeasurable hbτ) hD
        (hbτ.mono fun ω hω => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hω))
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hM hC)
  have hdisc : brownianDiscount B P h T = sSup (stoppingPayoffs B P h T) := rfl
  unfold brownianValue
  rw [hdisc]
  linarith [h0, hsup]


/-- The bundle of `lem:brownian-ball-localization` at one sample point, from the samplewise
polynomial growth of the field, its continuity on the time strip, and the strong Markov step. -/
theorem ballLocalizationInput_of_growth {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Space d} {u : Space d} (hB : IsBrownian d u B P)
    (hm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous fun s => B s ω)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 < T) (K : Set (Space d)) (hK : IsCompact K)
    (hc : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (C : Ω → ℝ) (c : ℝ) (hCb : ∀ᵐ ω ∂P, C ω ≤ c) (p : ℕ)
    (hg : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y, ‖h v y‖ ≤ C ω * (1 + ‖y - u‖) ^ p)
    (hstep : BallExcessStep B P h T A u (sSup (farValues (fun _ => B) P h T A K))) :
    BallLocalizationInput (fun _ => B) P h T A K u := by
  have hfull : BddAbove (stoppingPayoffs B P h T) :=
    bddAbove_stoppingPayoffs_of_samplewise_growth hB hm hBc h T hT.le hc C c hCb p hg
  obtain ⟨M, hM⟩ := exists_bound_on_neighbourhood h T A hT.le K hK hc
  have hfar : BddAbove (farValues (fun _ => B) P h T A K) :=
    bddAbove_farValues_of_bddAbove (fun _ => B) P h T A M (sSup (stoppingPayoffs B P h T)) K hM
      (fun z => ⟨hfull, le_refl _⟩)
  exact BallLocalizationInput.of (fun _ => B) P h T A K u hfull hfar hstep

/-- The per-sample bundle of `lem:brownian-ball-localization` from samplewise polynomial
growth of the field, the compactness of `K` and the strong Markov step. -/
theorem ballInput_of_samplewise_growth {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t))
    (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 ≤ T) (K : Set (Space d)) (_hK : IsCompact K)
    (hgrowth : ∀ᵐ ω ∂PW, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p)
    (hcontZ : ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (hfar : ∀ᵐ ω ∂PW, BddAbove (farValues B PB (fun t z => Z t z ω) T A K))
    (hstep : ∀ᵐ ω ∂PW, ∀ u ∈ K,
      BallExcessStep (B u) PB (fun t z => Z t z ω) T A u
        (sSup (farValues B PB (fun t z => Z t z ω) T A K))) :
    ∀ᵐ ω ∂PW, ∀ u ∈ K,
      BallLocalizationInput B PB (fun t z => Z t z ω) T A K u := by
  filter_upwards [hgrowth, hcontZ, hfar, hstep] with ω hg hc hf hst
  intro u hu
  obtain ⟨C, hC, p, hp⟩ := hg
  have hfull : BddAbove (stoppingPayoffs (B u) PB (fun t z => Z t z ω) T) :=
    bddAbove_stoppingPayoffs_of_samplewise_growth (hBrown u) (hmeas u) (hcont u)
      (fun t z => Z t z ω) T hT hc (fun _ => C * (1 + ‖u‖) ^ p) (C * (1 + ‖u‖) ^ p)
      (Filter.Eventually.of_forall fun _ => le_rfl) p
      (Filter.Eventually.of_forall fun ω' v hv y => by
        refine le_trans (hp v hv y) ?_
        have h1 : (1 + ‖y‖) ≤ (1 + ‖u‖) * (1 + ‖y - u‖) := by
          have h2 : ‖y‖ ≤ ‖y - u‖ + ‖u‖ := by
            simpa only [sub_add_cancel] using norm_le_norm_sub_add y u
          nlinarith [norm_nonneg (y - u), norm_nonneg u]
        calc C * (1 + ‖y‖) ^ p ≤ C * ((1 + ‖u‖) * (1 + ‖y - u‖)) ^ p :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hC
          _ = C * (1 + ‖u‖) ^ p * (1 + ‖y - u‖) ^ p := by rw [mul_pow]; ring)
  exact BallLocalizationInput.of B PB (fun t z => Z t z ω) T A K u hfull hf (hst u hu)


theorem bddAbove_farValues_of_growth {PW : Measure ΩW} [IsProbabilityMeasure PW]
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t))
    (Z : ℝ → Space d → ΩW → ℝ) (T A : ℝ) (hT : 0 ≤ T) (K : Set (Space d)) (hK : IsCompact K)
    (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ᵐ ω ∂PW, ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖y‖) ^ p)
    (hcontZ : ∀ᵐ ω ∂PW,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (M : ℝ) (hM : ∀ z : Space d,
      ∫ ω, (1 + brownianPathRadius (B z) z T.toNNReal ω) ^ p ∂PB ≤ M) :
    ∀ᵐ ω ∂PW, BddAbove (farValues B PB (fun t z => Z t z ω) T A K) := by
  filter_upwards [hgrowth, hcontZ] with ω hg hc
  obtain ⟨M', hM'⟩ := exists_bound_on_neighbourhood (fun t z => Z t z ω) T A hT K hK hc
  obtain ⟨R, hR⟩ := exists_bound_on_neighbourhood (fun _ z => (1 + ‖z‖) ^ p) T A hT K hK
    (Continuous.continuousOn (by fun_prop))
  refine ⟨2 * C * M * R + C * R, ?_⟩
  rintro v ⟨z, hz, rfl⟩
  have hRz : (1 + ‖z‖) ^ p ≤ R := hR z hz
  have hpoly : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by
    intro v hv y
    refine le_trans (hg v hv y) ?_
    have h1 : (1 + ‖y‖) ≤ (1 + ‖z‖) * (1 + ‖y - z‖) := by
      have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_le_norm_sub_add y z
      nlinarith [norm_nonneg (y - z), norm_nonneg z]
    calc C * (1 + ‖y‖) ^ p ≤ C * ((1 + ‖z‖) * (1 + ‖y - z‖)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hC
      _ = C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by rw [mul_pow]; ring
  have hb := brownianValue_le_of_pointwise_bound (hBrown z) (hmeas z) (hcont z)
    (fun t z => Z t z ω) T hT hc (C * (1 + ‖z‖) ^ p) M (by positivity) p hpoly (hM z)
  have hb' : Z T z ω + sSup (stoppingPayoffs (B z) PB (fun t z => Z t z ω) T) ≤
      2 * (C * (1 + ‖z‖) ^ p) * M := by
    simpa only [Sandpile.Continuum.brownianValue, Sandpile.Continuum.brownianDiscount_eq_sSup]
      using hb
  have hz'' : -(C * (1 + ‖z‖) ^ p) ≤ Z T z ω := by
    have h1 := hpoly T.toNNReal (by rw [Real.coe_toNNReal T hT]) z
    rw [Real.coe_toNNReal T hT, sub_self, norm_zero, add_zero, one_pow, mul_one] at h1
    exact neg_le_of_abs_le h1
  have hCnn : 0 ≤ C * (1 + ‖z‖) ^ p :=
    mul_nonneg hC (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) p)
  have hRnn : 0 ≤ R := le_trans (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) p) hRz
  have hMnn : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ ∫ ω, (1 + brownianPathRadius (B z) z T.toNNReal ω) ^ p ∂PB :=
      integral_nonneg fun ω => pow_nonneg (add_nonneg zero_le_one
        (le_trans (norm_nonneg _) (norm_le_pathRadius (B z) (hcont z) z T.toNNReal ω le_rfl))) p
    linarith [hM z]
  have hstep : sSup (stoppingPayoffs (B z) PB (fun t z => Z t z ω) T) ≤
      C * (1 + ‖z‖) ^ p * (2 * M + 1) := by nlinarith [hb', hz'']
  have hfin : C * (1 + ‖z‖) ^ p * (2 * M + 1) ≤ C * R * (2 * M + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRz hC) (by linarith)
  linarith [hstep, hfin]

end Sandpile.Continuum
