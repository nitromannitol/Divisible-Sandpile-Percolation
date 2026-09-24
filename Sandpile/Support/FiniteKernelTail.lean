/-
Concentration of centered finite-kernel fields and short-distance
increments of the cut-off ball Green field.
-/
import Sandpile.Support.ExitConcentration
import Sandpile.Support.FiniteKernel
import Sandpile.Support.ExponentialMoments

open LatticeProb

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Sandpile

lemma integral_linear_pi_zero {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) (a : Fin N → ℝ) :
    (∫ x, ∑ i, a i * x i ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
  have hi (i : Fin N) : Integrable (fun x : Fin N → ℝ => a i * x i) (Measure.pi (fun _ : Fin N => μ)) :=
    (integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hint).const_mul _
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  have he (i : Fin N) : (∫ x : Fin N → ℝ, x i ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
    have hh := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) aestronglyMeasurable_id
    simpa only [id_eq, hmean] using hh
  simp only [integral_const_mul, he, mul_zero, Finset.sum_const_zero]

lemma linear_pi_update {N : ℕ} (a x : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    (∑ j, a j * x j) - ∑ j, a j * Function.update x i y j = a i * (x i - y) := by
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin N) : a j * x j - a j * Function.update x i y j =
      if j = i then a i * (x i - y) else 0 := by
    by_cases hj : j = i
    · subst j; simp [mul_sub]
    · simp only [Function.update_of_ne hj, if_neg hj, sub_self]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma exists_finite_linear_tail (θ K B : ℝ) (hθ : 0 < θ) (hB : 0 < B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ a : Fin N → ℝ, (∑ i, a i ^ 2) ≤ B → ∀ H : ℝ, 0 < H →
        (∀ i, |a i| ≤ B / H) → ∀ t : ℝ, 0 ≤ t →
        (Measure.pi (fun _ : Fin N => μ)) {x | t < |∑ i, a i * x i|} ≤
          ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2) (t * H)))) := by
  obtain ⟨c, C, hc, hC, htail⟩ := weighted_tail_of_norm_bounds θ K B hθ hB
  refine ⟨c, C, hc, hC, ?_⟩
  intro N μ hμ hexp hK hmean a hsum H hH hmax t ht
  letI : IsProbabilityMeasure μ := hμ
  have hh := htail N μ hμ hexp hK (fun x => ∑ i, a i * x i) (by fun_prop)
    (fun i => |a i|) (fun i => abs_nonneg _) (fun x i y => by
      rw [linear_pi_update, abs_mul]) (by simpa only [sq_abs] using hsum) H hH hmax t ht
  rw [integral_linear_pi_zero μ (integrable_id_of_exp_moment μ θ hθ hexp) hmean a] at hh
  simpa only [sub_zero] using hh

lemma exists_finite_kernel_tail (θ K B : ℝ) (hθ : 0 < θ) (hB : 0 < B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (d : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ (a : Site d → ℝ) (s : Finset (Site d)), (∀ u ∉ s, a u = 0) →
        (∑ u ∈ s, a u ^ 2) ≤ B → ∀ H : ℝ, 0 < H →
        (∀ u, |a u| ≤ B / H) → ∀ t : ℝ, 0 ≤ t →
        (LatticeProb.iidLaw d μ) {ζ | t < |∑' u : Site d, a u * ζ u|} ≤
          ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2) (t * H)))) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_finite_linear_tail θ K B hθ hB
  refine ⟨c, C, hc, hC, ?_⟩
  intro d μ hμ hexp hK hmean a s hs hsum H hH hmax t ht
  letI : IsProbabilityMeasure μ := hμ
  let A (i : Fin s.card) := a (siteEnum s i)
  have hsum' : (∑ i, A i ^ 2) ≤ B := by
    change (∑ i, a (siteEnum s i) ^ 2) ≤ B
    rw [sum_siteEnum s (fun u => a u ^ 2)]
    exact hsum
  have he (ζ : Site d → ℝ) : (∑' u, a u * ζ u) = ∑ i, A i * ζ (siteEnum s i) := by
    rw [show (∑ i, A i * ζ (siteEnum s i)) = ∑ u ∈ s, a u * ζ u from sum_siteEnum s (fun u => a u * ζ u)]
    exact tsum_eq_sum (fun u hu => by rw [hs u hu, zero_mul])
  have hm : MeasurableSet {x : Fin s.card → ℝ | t < |∑ i, A i * x i|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hp := (LatticeProb.measurePreserving_pick _ μ (siteEnum s) (siteEnum_injective s)).measure_preimage hm.nullMeasurableSet
  have hevent : {ζ : Site d → ℝ | t < |∑' u, a u * ζ u|} =
      (fun ζ : Site d → ℝ => fun i => ζ (siteEnum s i)) ⁻¹' {x : Fin s.card → ℝ | t < |∑ i, A i * x i|} := by
    ext ζ
    simp only [mem_preimage, mem_setOf_eq, he]
  rw [hevent, hp]
  exact htail s.card μ hμ hexp hK hmean A hsum' H hH (fun i => hmax _) t ht

lemma finiteKernelField_eq_tsum_translated {d : ℕ} (h : Site d → ℝ)
    (ζ : Site d → ℝ) (z : Site d) :
    finiteKernelField h ζ z = ∑' y : Site d, h (y - z) * ζ y := by
  have he := (Equiv.subRight z).tsum_eq (fun u => h u * ζ (z + u))
  simpa only [finiteKernelField, Equiv.subRight_apply, add_sub_cancel] using he.symm

lemma finiteKernelField_sub_eq_tsum {d : ℕ} (h : Site d → ℝ) (z w : Site d)
    (s : Finset (Site d)) (hz : ∀ y ∉ s, h (y - z) = 0) (hw : ∀ y ∉ s, h (y - w) = 0)
    (ζ : Site d → ℝ) : finiteKernelField h ζ z - finiteKernelField h ζ w =
      ∑' y : Site d, (h (y - z) - h (y - w)) * ζ y := by
  have hsz : Summable (fun y : Site d => h (y - z) * ζ y) :=
    summable_of_ne_finset_zero (s := s) (fun y hy => by rw [hz y hy, zero_mul])
  have hsw : Summable (fun y : Site d => h (y - w) * ζ y) :=
    summable_of_ne_finset_zero (s := s) (fun y hy => by rw [hw y hy, zero_mul])
  rw [finiteKernelField_eq_tsum_translated h ζ z, finiteKernelField_eq_tsum_translated h ζ w,
    ← hsz.tsum_sub hsw]
  exact tsum_congr (fun y => by ring)

lemma exists_far_increment_tail (hBall : External.BallGreenBounds)
    (θ K M : ℝ) (hθ : 0 < θ) (hM : 1 ≤ M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ z w : Site 4, External.BallGreen.latticeNorm (w - z) ≤ M * L →
      ∀ t : ℝ, 0 ≤ t →
        (LatticeProb.iidLaw 4 μ) {ζ | t < |finiteKernelField (External.BallGreen.cutField r L φ) ζ z -
          finiteKernelField (External.BallGreen.cutField r L φ) ζ w|} ≤
        ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2) (t * (L : ℝ) ^ 2)))) := by
  classical
  obtain ⟨G, g, hG, _, hball⟩ := hBall
  let B := G * (1 + M) ^ 4 + 2 * G
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨c, C, hc, hC, htail⟩ := exists_finite_kernel_tail θ K B hθ hB
  refine ⟨c, C, hc, hC, ?_⟩
  intro μ hμ hexp hK hmean r L hr hL φ hφ z w hzw t ht
  letI : IsProbabilityMeasure μ := hμ
  let h := External.BallGreen.cutField r L φ
  let k (y : Site 4) := h (y - z) - h (y - w)
  obtain ⟨s, hs⟩ := exists_finiteKernelField_coordinates (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (![z, w])
  have hz (y : Site 4) (hy : y ∉ s) : h (y - z) = 0 := hs 0 y hy
  have hw (y : Site 4) (hy : y ∉ s) : h (y - w) = 0 := hs 1 y hy
  have hk (y : Site 4) (hy : y ∉ s) : k y = 0 := by dsimp [k]; rw [hz y hy, hw y hy, sub_self]
  have hks : Summable (fun y : Site 4 => k y ^ 2) :=
    summable_of_ne_finset_zero (s := s) (fun y hy => by rw [hk y hy, zero_pow (by decide : 2 ≠ 0)])
  obtain ⟨ha, _, hshift⟩ := (hball r hr).2.2.2.2.1 L hL φ hφ
  have he : (∑' y : Site 4, k y ^ 2) = ∑' u : Site 4, (h u - h (u - (w - z))) ^ 2 := by
    calc
      _ = ∑' y : Site 4, (h (y - z) - h ((y - z) - (w - z))) ^ 2 :=
        tsum_congr (fun y => by dsimp [k]; rw [show (y - z) - (w - z) = y - w by abel])
      _ = _ := (Equiv.subRight z).tsum_eq (fun u => (h u - h (u - (w - z))) ^ 2)
  have hsum : (∑ y ∈ s, k y ^ 2) ≤ B := by
    calc
      _ ≤ ∑' y, k y ^ 2 := hks.sum_le_tsum s (fun _ _ => sq_nonneg _)
      _ = _ := he
      _ ≤ G * (1 + M) ^ 4 := hshift M hM (w - z) hzw
      _ ≤ B := by dsimp [B]; linarith
  have hmax (y : Site 4) : |k y| ≤ B / (L : ℝ) ^ 2 := by
    calc
      _ ≤ |h (y - z)| + |h (y - w)| := (abs_sub_le (h (y - z)) 0 (h (y - w))).trans_eq (by simp only [sub_zero, zero_sub, abs_neg])
      _ ≤ G / (L : ℝ) ^ 2 + G / (L : ℝ) ^ 2 := add_le_add (ha _) (ha _)
      _ = (2 * G) / (L : ℝ) ^ 2 := by ring
      _ ≤ B / (L : ℝ) ^ 2 := div_le_div_of_nonneg_right (by dsimp [B]; linarith [mul_nonneg hG.le (pow_nonneg (by linarith : 0 ≤ 1 + M) 4)]) (sq_nonneg _)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hh := htail 4 μ hμ hexp hK hmean k s hk hsum ((L : ℝ) ^ 2) (by positivity) hmax t ht
  have hfield (ζ : Site 4 → ℝ) : finiteKernelField h ζ z - finiteKernelField h ζ w = ∑' y, k y * ζ y :=
    finiteKernelField_sub_eq_tsum h z w s hz hw ζ
  change (LatticeProb.iidLaw 4 μ) {ζ | t < |finiteKernelField h ζ z - finiteKernelField h ζ w|} ≤ _
  simpa only [hfield] using hh

end Sandpile
