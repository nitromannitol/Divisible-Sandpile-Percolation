import Sandpile.Support.ExplSpatialEnvelope

/-!
# Domination of the Brownian heat kernel and the common-event heat semigroup

`exists_heatKernelBM_dom_bounded` shows that on a bounded window of times `[a,b]` and a
bounded ball of centres, the Brownian heat kernel `heatKernelBM d r x y` is dominated,
uniformly in `r` and `x`, by a constant multiple of the kernel at the fixed time `2b` and
centre `0`: the Gaussian tail in `y` only improves when the centre `x` is confined to a
ball, so the dominating function is a single centred kernel with a doubled time horizon.
This gives, for every fixed `ω`, a single dominating function that works for every `(r,x)`
in a compact box, which is exactly what is needed to justify differentiating or integrating
the Gaussian heat potential `Z` under the integral sign. `gaussianPotential_heat_semigroup_common`
uses this domination to promote the heat-semigroup identity for `Z` from an a.e.-in-`ω`
statement to a single event of full probability on which the identity holds simultaneously
for every rational and irrational time and space argument, by exhausting `(r,x,s)` through
an increasing sequence of compact windows and applying dominated convergence on each one.
`gaussianPotential_increment_semigroup_common` then restates the same common event for
increments `Z(s+δ) - Z(s)` rather than raw values of `Z`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

/-- On a compact time window `[a,b]` and ball of centres of radius `R`, the Brownian heat
kernel `heatKernelBM d r x y` is bounded by a constant (depending only on `a,b,R,d`) times
the kernel `heatKernelBM d (2b) 0 y` evaluated at the doubled time horizon and the origin;
this follows from comparing the Gaussian prefactors and completing the square in the
exponent using `‖y‖ ≤ ‖x-y‖ + R`. -/
theorem exists_heatKernelBM_dom_bounded {d : ℕ} (hd : 1 ≤ d)
    {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, a ≤ r → r ≤ b → ∀ x : Space d, ‖x‖ ≤ R →
      ∀ y : Space d, heatKernelBM d r x y ≤ C * heatKernelBM d (2 * b) 0 y := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hb : 0 < b := ha.trans_le hab
  have hpi := Real.pi_pos
  let A (t : ℝ) := (4 * Real.pi * t / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)
  have hAa : 0 < A a := by dsimp [A]; positivity
  have hAb : 0 < A (2 * b) := by dsimp [A]; positivity
  refine ⟨A a * Real.exp ((d : ℝ) * R ^ 2 / (2 * a)) / A (2 * b), by positivity, ?_⟩
  intro r har hrb x hx y
  have hr : 0 < r := ha.trans_le har
  have hAr : A r ≤ A a := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    gcongr
  have hy : ‖y‖ ≤ ‖x - y‖ + R := by
    have hh := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev y x] at hh
    exact hh.trans (by linarith)
  have hy2 : ‖y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * R ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg y) (by positivity : 0 ≤ ‖x - y‖ + R)).mpr hy
    nlinarith [sq_nonneg (‖x - y‖ - R)]
  have hq : (d : ℝ) * ‖y‖ ^ 2 / (4 * b) ≤
      (d : ℝ) * ‖x - y‖ ^ 2 / (2 * r) + (d : ℝ) * R ^ 2 / (2 * a) := by
    calc (d : ℝ) * ‖y‖ ^ 2 / (4 * b)
        ≤ (d : ℝ) * (2 * ‖x - y‖ ^ 2 + 2 * R ^ 2) / (4 * b) := by gcongr
      _ = (d : ℝ) * ‖x - y‖ ^ 2 / (2 * b) + (d : ℝ) * R ^ 2 / (2 * b) := by ring
      _ ≤ (d : ℝ) * ‖x - y‖ ^ 2 / (2 * r) + (d : ℝ) * R ^ 2 / (2 * a) := by gcongr
  have he : Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * r)) ≤
      Real.exp ((d : ℝ) * R ^ 2 / (2 * a)) * Real.exp (-(d : ℝ) * ‖y‖ ^ 2 / (4 * b)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [neg_mul, neg_div]
    linarith
  unfold heatKernelBM
  rw [zero_sub, norm_neg, show (2 : ℝ) * (2 * b) = 4 * b by ring]
  change A r * _ ≤ _
  calc A r * Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * r))
      ≤ A a * Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * r)) :=
        mul_le_mul_of_nonneg_right hAr (Real.exp_nonneg _)
    _ ≤ A a * (Real.exp ((d : ℝ) * R ^ 2 / (2 * a)) * Real.exp (-(d : ℝ) * ‖y‖ ^ 2 / (4 * b))) :=
      mul_le_mul_of_nonneg_left he hAa.le
    _ = _ := by
      change A a * (_ * _) = (A a * _ / A (2 * b)) * (A (2 * b) * _)
      field_simp [ne_of_gt hAb]

/-- The continuous Gaussian heat-potential semigroup on one common noise event. -/
theorem gaussianPotential_heat_semigroup_common {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂P, ∀ (r s : ℝ), 0 < r → 0 ≤ s → ∀ x : Space d,
      Integrable (fun y => heatKernelBM d r x y * Z s y ω) volume ∧
        (∫ y, heatKernelBM d r x y * Z s y ω) = Z (r + s) x ω - Z r x ω := by
  let μ (n : ℕ) : Measure (Space d) := volume.withDensity
    (fun y => ENNReal.ofReal (heatKernelBM d (2 * ((n : ℝ) + 1)) 0 y))
  have hμ (n : ℕ) : IsProbabilityMeasure (μ n) :=
    isProbabilityMeasure_heatKernelBM hd (by positivity) 0
  have hEnv : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ D : Space d → ℝ, Integrable D (μ n) ∧
      ∀ᵐ y ∂μ n, ∀ t ∈ Set.Icc 0 ((n : ℝ) + 1), ‖Z t y ω‖ ≤ D y := by
    apply ae_all_iff.mpr
    intro n
    letI := hμ n
    exact gaussianPotential_integrable_space_time_envelope hd hd3 hW ν2 Z hmod hc (μ n)
      (by positivity)
  apply gaussianPotential_heat_semigroup_common_of_local_envelopes hd hd3 hW ν2 Z hmod hc
  filter_upwards [hEnv] with ω hω
  intro q
  let L : ℝ := max (max q.1.1 (1 / q.1.1)) (max ‖q.2.2‖ (q.2.1 : ℝ))
  obtain ⟨n, hn⟩ := exists_nat_gt L
  let N : ℝ := (n : ℝ) + 1
  have hNL : L < N := by dsimp [N]; linarith
  have hNr : q.1.1 < N := (le_trans (le_max_left _ _) (le_max_left _ _)).trans_lt hNL
  have hNi : 1 / q.1.1 < N := (le_trans (le_max_right _ _) (le_max_left _ _)).trans_lt hNL
  have hNx : ‖q.2.2‖ < N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hNL
  have hNs : (q.2.1 : ℝ) < N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hNL
  have hN1 : 1 ≤ N := by
    dsimp [N]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hN : 0 < N := zero_lt_one.trans_le hN1
  have ha : 0 < 1 / N := by positivity
  have hab : 1 / N ≤ N := (div_le_iff₀ hN).mpr (by nlinarith)
  have haq : 1 / N < q.1.1 := by
    have hh := (div_lt_iff₀ q.1.property).mp hNi
    apply (div_lt_iff₀ hN).mpr
    nlinarith
  obtain ⟨D, hD, hb⟩ := hω n
  let w (y : Space d) := heatKernelBM d (2 * N) 0 y
  have hw (y : Space d) : 0 < w y := heatKernelBM_pos hd (by positivity) 0 y
  have hwm : Measurable (fun y => ENNReal.ofReal (w y)) := by
    dsimp [w]
    unfold heatKernelBM
    fun_prop
  change Integrable D ((volume : Measure (Space d)).withDensity (fun y => ENNReal.ofReal (w y)))
    at hD
  change ∀ᵐ y ∂(volume : Measure (Space d)).withDensity (fun y => ENNReal.ofReal (w y)),
    ∀ t ∈ Set.Icc 0 N, ‖Z t y ω‖ ≤ D y at hb
  have hbv : ∀ᵐ y ∂(volume : Measure (Space d)), ∀ t ∈ Set.Icc 0 N, ‖Z t y ω‖ ≤ D y := by
    exact ((ae_withDensity_iff hwm).mp hb).mono fun y hy =>
      hy (ne_of_gt (ENNReal.ofReal_pos.mpr (hw y)))
  have hiw : Integrable (fun y => w y * |D y|) (volume : Measure (Space d)) := by
    have hh := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Space d)))
      (g := fun y => |D y|) hwm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hD.abs
    simpa only [ENNReal.toReal_ofReal (hw _).le, smul_eq_mul] using hh
  obtain ⟨C, hC, hK⟩ := exists_heatKernelBM_dom_bounded hd ha hab hN.le
  refine ⟨fun y => C * (w y * |D y|), hiw.const_mul C, ?_⟩
  have hqr : Continuous (fun p : {r : ℝ // 0 < r} × (ℝ≥0 × Space d) => p.1.1) := by fun_prop
  have hqx : Continuous (fun p : {r : ℝ // 0 < r} × (ℝ≥0 × Space d) => ‖p.2.2‖) := by fun_prop
  have hqs : Continuous (fun p : {r : ℝ // 0 < r} × (ℝ≥0 × Space d) => (p.2.1 : ℝ)) := by fun_prop
  filter_upwards [hqr.continuousAt.eventually (lt_mem_nhds haq),
    hqr.continuousAt.eventually (gt_mem_nhds hNr),
    hqx.continuousAt.eventually (gt_mem_nhds hNx),
    hqs.continuousAt.eventually (gt_mem_nhds hNs)] with p hpa hpr hpx hps
  filter_upwards [hbv] with y hy
  rw [norm_mul, Real.norm_of_nonneg (heatKernelBM_nonneg d p.1.property.le p.2.2 y)]
  calc heatKernelBM d p.1.1 p.2.2 y * ‖Z p.2.1 y ω‖
      ≤ heatKernelBM d p.1.1 p.2.2 y * |D y| :=
        mul_le_mul_of_nonneg_left ((hy p.2.1 ⟨p.2.1.property, hps.le⟩).trans (le_abs_self _))
          (heatKernelBM_nonneg d p.1.property.le p.2.2 y)
    _ ≤ (C * w y) * |D y| :=
        mul_le_mul_of_nonneg_right (hK p.1.1 hpa.le hpr.le p.2.2 hpx.le y) (abs_nonneg _)
    _ = C * (w y * |D y|) := by ring
/-- Heat increments satisfy the homogeneous semigroup on the same common noise event. -/
theorem gaussianPotential_increment_semigroup_common {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂P, ∀ (r s δ : ℝ), 0 < r → 0 ≤ s → 0 ≤ δ → ∀ x : Space d,
      Integrable (fun y => heatKernelBM d r x y * (Z (s + δ) y ω - Z s y ω)) volume ∧
        (∫ y, heatKernelBM d r x y * (Z (s + δ) y ω - Z s y ω)) =
          Z (r + s + δ) x ω - Z (r + s) x ω := by
  filter_upwards [gaussianPotential_heat_semigroup_common hd hd3 hW ν2 Z hmod hc] with ω hω
  intro r s δ hr hs hδ x
  have h1 := hω r (s + δ) hr (add_nonneg hs hδ) x
  have h2 := hω r s hr hs x
  simp_rw [mul_sub]
  refine ⟨h1.1.sub h2.1, ?_⟩
  rw [integral_sub h1.1 h2.1, h1.2, h2.2, add_assoc]
  ring
end Sandpile.Support
