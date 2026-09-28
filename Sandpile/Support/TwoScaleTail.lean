import Sandpile.Support.FiniteKernelTail

/-!
# Two-Scale Bernstein Concentration

Bernstein concentration with separate square-sum and maximum coefficient
scales, uniform in both scales and in the number of coordinates.
`weighted_tail_of_two_norm_bounds` derives the two-scale tail
`exp(-c min(s²/V, s/A))` for a Lipschitz functional of independent,
exponentially-integrable coordinates from the single-scale bound of
`Sandpile.Support.FiniteKernelTail`.  `exists_finite_kernel_two_scale_tail`
and `exists_finite_kernel_field_two_scale_tail` transport the same tail to a
finitely supported linear functional of the site field and to its
translate-indexed family, using the site enumeration of a finite support set.
-/

open LatticeProb

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace Sandpile

/-- The two-scale Bernstein tail: for a Lipschitz `F` of `N` independent coordinates with
per-coordinate Lipschitz constants `ℓ` of square-sum at most `V` and maximum at most `A`,
`P(|F - E F| > s) ≤ C exp(-c min(s²/V, s/A))` with `c, C` depending only on the exponential
moment bound `θ, K` of the common law, not on `N`, `V`, or `A`. Proved by comparing the
single-scale tail of `Sandpile.Support.FiniteKernelTail` at the actual norms of `ℓ` to the
one at the hypothesised bounds `V, A`, handling `ℓ = 0` separately. -/
theorem weighted_tail_of_two_norm_bounds (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ * |z|)) ν → (∫ z, Real.exp (θ * |z|) ∂ν) ≤ K →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F → ∀ ℓ : Fin N → ℝ,
        (∀ i, 0 ≤ ℓ i) →
        (∀ ξ i v, |F ξ - F (Function.update ξ i v)| ≤ ℓ i * |ξ i - v|) →
        ∀ V A : ℝ, 0 < V → 0 < A → (∑ i, ℓ i ^ 2) ≤ V → (∀ i, ℓ i ≤ A) →
        ∀ s : ℝ, 0 ≤ s →
          (Measure.pi fun _ : Fin N => ν)
              {ξ | s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / V) (s / A)))) := by
  obtain ⟨c₀, C, hc₀, hC, htail⟩ := weighted_exp_conc_tail θ K hθ
  refine ⟨c₀, C, hc₀, hC, ?_⟩
  intro N ν hν hexp hK F hFm ℓ hℓ hLip V A _hV _hA hsum hmax s hs
  haveI := hν
  classical
  by_cases hne : ∃ i, ℓ i ≠ 0
  · haveI : Nonempty (Fin N) := ⟨hne.choose⟩
    have hInf : lInfNorm ℓ ≤ A := ciSup_le fun i => hmax i
    have hInf0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
    have hTwo0 : 0 < lTwoNorm ℓ ^ 2 := sq_pos_of_pos (lTwoNorm_pos ℓ hℓ hne)
    have hTwo : lTwoNorm ℓ ^ 2 ≤ V := by rwa [lTwoNorm_sq]
    have hmin : c₀ * min (s ^ 2 / V) (s / A) ≤
        c₀ * min (s ^ 2 / lTwoNorm ℓ ^ 2) (s / lInfNorm ℓ) :=
      mul_le_mul_of_nonneg_left (min_le_min
        (div_le_div_of_nonneg_left (sq_nonneg s) hTwo0 hTwo)
        (div_le_div_of_nonneg_left hs hInf0 hInf)) hc₀.le
    have ht := htail N ν hν hexp hK F hFm ℓ hℓ hne hLip s hs
    refine (measure_mono
      (fun ξ (hξ : s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|) => hξ.le)).trans
      (ht.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hC.le
  · have hz : ∀ i, ℓ i = 0 := by simpa using hne
    have hc : ∀ ξ, F ξ = F 0 := by
      intro ξ
      have h := abs_sub_le_sum_lip F ℓ hLip ξ 0
      simp only [hz, zero_mul, Finset.sum_const_zero] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hm : (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin N => ν)) = F 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hc), integral_const]
      simp
    have he : {ξ : Fin N → ℝ | s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      change s < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)| at hξ
      rw [hc ξ, hm, sub_self, abs_zero] at hξ
      exact hs.not_gt hξ
    rw [he, measure_empty]
    exact bot_le

/-- The two-scale tail transported to a finitely supported linear functional of the site
field: for `a` supported on `s` with `∑_{u∈s} a u ^ 2 ≤ V` and `|a u| ≤ A`,
`P(|∑' u, a u ζ u| > t) ≤ C exp(-c min(t²/V, t/A))` under the i.i.d. law `iidLaw d μ`, by
enumerating `s` with `siteEnum` to reduce to `weighted_tail_of_two_norm_bounds`. -/
lemma exists_finite_kernel_two_scale_tail (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (d : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ (a : Site d → ℝ) (s : Finset (Site d)), (∀ u ∉ s, a u = 0) →
        ∀ V A : ℝ, 0 < V → 0 < A → (∑ u ∈ s, a u ^ 2) ≤ V →
        (∀ u, |a u| ≤ A) → ∀ t : ℝ, 0 ≤ t →
        (LatticeProb.iidLaw d μ) {ζ | t < |∑' u : Site d, a u * ζ u|} ≤
          ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2 / V) (t / A)))) := by
  obtain ⟨c, C, hc, hC, htail⟩ := weighted_tail_of_two_norm_bounds θ K hθ
  refine ⟨c, C, hc, hC, ?_⟩
  intro d μ hμ hexp hK hmean a s hs V A hV hA hsum hmax t ht
  letI : IsProbabilityMeasure μ := hμ
  let coeff (i : Fin s.card) := a (siteEnum s i)
  have hsum' : (∑ i, coeff i ^ 2) ≤ V := by
    change (∑ i, a (siteEnum s i) ^ 2) ≤ V
    rw [sum_siteEnum s (fun u => a u ^ 2)]
    exact hsum
  have he (ζ : Site d → ℝ) : (∑' u, a u * ζ u) = ∑ i, coeff i * ζ (siteEnum s i) := by
    rw [show (∑ i, coeff i * ζ (siteEnum s i)) = ∑ u ∈ s, a u * ζ u from
      sum_siteEnum s (fun u => a u * ζ u)]
    exact tsum_eq_sum (fun u hu => by rw [hs u hu, zero_mul])
  have hm : MeasurableSet {x : Fin s.card → ℝ | t < |∑ i, coeff i * x i|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hp := (LatticeProb.measurePreserving_pick _ μ (siteEnum s)
      (siteEnum_injective s)).measure_preimage hm.nullMeasurableSet
  have hevent : {ζ : Site d → ℝ | t < |∑' u, a u * ζ u|} =
      (fun ζ : Site d → ℝ => fun i => ζ (siteEnum s i)) ⁻¹'
        {x : Fin s.card → ℝ | t < |∑ i, coeff i * x i|} := by
    ext ζ
    simp only [mem_preimage, mem_setOf_eq, he]
  rw [hevent, hp]
  have hh := htail s.card μ hμ hexp hK (fun x => ∑ i, coeff i * x i) (by fun_prop)
    (fun i => |coeff i|) (fun i => abs_nonneg _) (fun x i y => by
      rw [linear_pi_update, abs_mul]) V A hV hA (by simpa only [sq_abs] using hsum')
      (fun i => hmax _) t ht
  rw [integral_linear_pi_zero μ (integrable_id_of_exp_moment μ θ hθ hexp) hmean coeff] at hh
  simpa only [sub_zero] using hh


/-- The two-scale tail transported to the finite kernel field `finiteKernelField a ζ z`
at an arbitrary base point `z`: the same conclusion as
`exists_finite_kernel_two_scale_tail` holds for `a` compactly supported and summably
square-bounded (`∑' u, a u ^ 2 ≤ V`), by translating the support to `s.image (· + z)` and
reducing to that lemma via `finiteKernelField_eq_tsum_translated`. -/
lemma exists_finite_kernel_field_two_scale_tail (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (d : ℕ) (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ (a : Site d → ℝ) (s : Finset (Site d)), (∀ u ∉ s, a u = 0) →
        ∀ V A : ℝ, 0 < V → 0 < A → (∑' u, a u ^ 2) ≤ V →
        (∀ u, |a u| ≤ A) → ∀ (z : Site d) (t : ℝ), 0 ≤ t →
        (LatticeProb.iidLaw d μ) {ζ | t < |finiteKernelField a ζ z|} ≤
          ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2 / V) (t / A)))) := by
  classical
  obtain ⟨c, C, hc, hC, htail⟩ := exists_finite_kernel_two_scale_tail θ K hθ
  refine ⟨c, C, hc, hC, ?_⟩
  intro d μ hμ hexp hK hmean a s hs V A hV hA hsum hmax z t ht
  let k (y : Site d) := a (y - z)
  let S := s.image (fun u => z + u)
  have hk (y : Site d) (hy : y ∉ S) : k y = 0 := by
    apply hs
    intro hu
    apply hy
    exact Finset.mem_image.mpr ⟨y - z, hu, by abel⟩
  have hks : Summable (fun y : Site d => k y ^ 2) :=
    summable_of_ne_finset_zero (s := S) (fun y hy => by rw [hk y hy, zero_pow (by decide : 2 ≠ 0)])
  have hsq : (∑ y ∈ S, k y ^ 2) ≤ V := by
    calc
      _ ≤ ∑' y, k y ^ 2 := hks.sum_le_tsum S (fun _ _ => sq_nonneg _)
      _ = ∑' u, a u ^ 2 := (Equiv.subRight z).tsum_eq (fun u => a u ^ 2)
      _ ≤ V := hsum
  have hh := htail d μ hμ hexp hK hmean k S hk V A hV hA hsq (fun y => hmax (y-z)) t ht
  simpa only [finiteKernelField_eq_tsum_translated, k] using hh

end Sandpile
