/-
The uniform block tail of `sandpile.tex:2827-2881`.  The quadratic MGF lower
bound follows from a uniform amount of mass on a negative half-line; the
upper bound follows from the exponential moment.  The second-moment argument
is applied to the exponential of the negative membrane value.
-/
import Sandpile.Support.BlockMoment
import Sandpile.Support.D4Difference

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

theorem exists_membrane_negative_tail_four (hVS : Sandpile.External.VarianceScale)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ a C δ : ℝ, 0 < a ∧ 0 < C ∧ 0 < δ ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        ∀ θ : ℝ, 0 < θ → θ ≤ δ → ∀ m : ℕ,
          2 * Real.log 2 ≤ a * θ ^ 2 * (∑' z : Site 4, greenTime 4 m 0 z ^ 2) →
          Real.exp (-(C * θ ^ 2 * (∑' z : Site 4, greenTime 4 m 0 z ^ 2))) / 16 ≤
            (LatticeProb.iidLaw 4 ν).real
              {ζ | a * θ / 2 * (∑' z : Site 4, greenTime 4 m 0 z ^ 2) < -membrane ζ m 0} := by
  classical
  obtain ⟨a, q, ha, hq, hq1, htail⟩ := exists_uniform_left_tail ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨M, hM, -, hMinf⟩ := exists_greenTime_norm_bounds_four hVS
  have hM0 : 0 < M := by linarith
  set α := q * a ^ 2 / 8
  set g := 16 / θ₀ ^ 2 * max K₀ 1
  set δ := min (θ₀ / (4 * M)) (1 / (a * M))
  refine ⟨α, 4 * g, δ, by dsimp [α]; positivity,
    by dsimp [g]; positivity, by dsimp [δ]; positivity, ?_⟩
  intro ν hprob hmean hvar hexp hK θ hθ hθδ m hlarge
  haveI := hprob
  have hint := integrable_id_of_exp_moment ν θ₀ hθ₀ hexp
  have htail' : q ≤ ν.real (Set.Iic (-a)) := by
    have h := htail ν hprob hmean hvar hexp hK
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp h
  have hSG : SubGaussianOn id g (θ₀ / 2) ν :=
    subGaussianOn_of_exp_moment ν θ₀ (max K₀ 1) hθ₀ hexp
      (hK.trans (le_max_left _ _)) hint hmean
  have hθM : θ * M ≤ θ₀ / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * M by positivity)).mp
      (hθδ.trans (min_le_left _ _))
    nlinarith
  have haθM : a * θ * M ≤ 1 := by
    have h := (le_div_iff₀ (mul_pos ha hM0)).mp (hθδ.trans (min_le_right _ _))
    nlinarith
  set N := (boxFinset (0 : Site 4) m).card
  set ℓ : Fin N → ℝ := fun i => greenTime 4 m 0 (boxEnum 0 m i)
  set Q := ∑' z : Site 4, greenTime 4 m 0 z ^ 2
  set μ := Measure.pi fun _ : Fin N => ν
  have hℓ (i : Fin N) : 0 ≤ ℓ i := greenTime_nonneg m 0 _
  have hℓM (i : Fin N) : ℓ i ≤ M := hMinf m 0 _
  have hsum : (∑ i, ℓ i ^ 2) = Q := by
    dsimp [Q, ℓ]
    rw [tsum_greenTime_sq_eq_sum]
    exact sum_boxEnum 0 m fun z => greenTime 4 m 0 z ^ 2
  have hQ : 0 ≤ Q := by rw [← hsum]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsmall (i : Fin N) : q * a ^ 2 * (θ * ℓ i) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ a * θ * ℓ i := mul_nonneg (mul_pos ha hθ).le (hℓ i)
    have h1 : a * θ * ℓ i ≤ 1 :=
      (mul_le_mul_of_nonneg_left (hℓM i) (mul_pos ha hθ).le).trans haθM
    have h2 : (a * θ * ℓ i) ^ 2 ≤ 1 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right hq1 (sq_nonneg (a * θ * ℓ i))
    nlinarith
  have hs1 (i : Fin N) : |(-θ) * ℓ i| ≤ θ₀ / 2 := by
    rw [abs_mul, abs_neg, abs_of_pos hθ, abs_of_nonneg (hℓ i)]
    have := mul_le_mul_of_nonneg_left (hℓM i) hθ.le
    linarith
  have hs2 (i : Fin N) : |(-(2 * θ)) * ℓ i| ≤ θ₀ / 2 := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * θ), abs_of_nonneg (hℓ i)]
    have := mul_le_mul_of_nonneg_left (hℓM i) hθ.le
    nlinarith
  have hi1 : Integrable (fun ξ : Fin N → ℝ => Real.exp (-(θ * ∑ i, ℓ i * ξ i))) μ := by
    simpa only [neg_mul] using integrable_exp_weighted_sum ν hSG ℓ (-θ) hs1
  have hi2 : Integrable (fun ξ : Fin N → ℝ => Real.exp (-(2 * θ * ∑ i, ℓ i * ξ i))) μ := by
    simpa only [neg_mul] using integrable_exp_weighted_sum ν hSG ℓ (-(2 * θ)) hs2
  have hlower : Real.exp (α * θ ^ 2 * Q) ≤
      ∫ ξ : Fin N → ℝ, Real.exp (-(θ * ∑ i, ℓ i * ξ i)) ∂μ := by
    rw [← hsum]
    apply integral_exp_neg_weighted_lower ν hint hmean ha hq.le hθ.le htail' ℓ hℓ hsmall
    intro i
    simpa only [neg_mul, id_eq] using (hSG ((-θ) * ℓ i) (hs1 i)).1
  have hupper : (∫ ξ : Fin N → ℝ, Real.exp (-(2 * θ * ∑ i, ℓ i * ξ i)) ∂μ) ≤
      Real.exp ((4 * g) * θ ^ 2 * Q) := by
    have h := integral_exp_weighted_sum_le ν g (θ₀ / 2) hSG ℓ (-(2 * θ)) hs2
    simp only [neg_mul, neg_sq, hsum] at h
    convert h using 1
    congr 1
    ring
  have hZ : Measurable (fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i) := by
    fun_prop
  have hprob' := measure_neg_tail_of_exp_moments μ (fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i) hZ
    (show 0 ≤ α by dsimp [α]; positivity) hθ hQ hi1 hi2 hlower hupper hlarge
  have hmp := LatticeProb.measurePreserving_pick _ ν (boxEnum (0 : Site 4) m) (boxEnum_injective 0 m)
  have hmeas : MeasurableSet {ξ : Fin N → ℝ | α * θ / 2 * Q < -(∑ i, ℓ i * ξ i)} :=
    measurableSet_lt measurable_const hZ.neg
  have hpre : {ζ : Site 4 → ℝ | α * θ / 2 * Q < -membrane ζ m 0} =
      (fun ζ : Site 4 → ℝ => fun i => ζ (boxEnum 0 m i)) ⁻¹'
        {ξ : Fin N → ℝ | α * θ / 2 * Q < -(∑ i, ℓ i * ξ i)} := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_preimage, membrane_eq_sum_boxEnum m 0 ζ]
    rfl
  calc Real.exp (-((4 * g) * θ ^ 2 * Q)) / 16
      ≤ μ.real {ξ : Fin N → ℝ | α * θ / 2 * Q < -(∑ i, ℓ i * ξ i)} := hprob'
    _ = (LatticeProb.iidLaw 4 ν).real {ζ | α * θ / 2 * Q < -membrane ζ m 0} := by
      rw [measureReal_def, measureReal_def, hpre, hmp.measure_preimage hmeas.nullMeasurableSet]

end Sandpile
