/-
Stationarity and variance compactness in the contradiction argument for
critical percolation, `sandpile.tex:2613-2627`. It suffices to exclude bad
blocks at the origin along laws whose variances converge to a positive limit.
-/
import Sandpile.Support.PercVarianceSubseq

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Sandpile

/-- The probability of a bad localized block does not depend on its centre. -/
theorem measure_bad_block_d23_eq_origin (d : ℕ) (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (R t : ℕ) (ℓ : ℝ) (z : Site 2) :
    LatticeProb.iidLaw d ν {ζ | ¬ BlockGood R (d23Field d R t ζ) ℓ z} =
      LatticeProb.iidLaw d ν {ζ | ¬ BlockGood R (d23Field d R t ζ) ℓ 0} := by
  let y : Site d := planeSite ![2 * (R : ℤ) * z 0, 2 * (R : ℤ) * z 1]
  have hset : {ζ | ¬ BlockGood R (d23Field d R t ζ) ℓ z} =
      shiftField y ⁻¹' {ζ | ¬ BlockGood R (d23Field d R t ζ) ℓ 0} := by
    ext ζ
    exact not_congr (by simpa [y] using blockGood_d23Field_shift hd R t ℓ ζ 0 z)
  have hmeas : MeasurableSet {ζ : Site d → ℝ |
      ¬ BlockGood R (d23Field d R t ζ) ℓ 0} :=
    (measurableSet_blockGood_d23Field hd R t ℓ 0).compl
  rw [hset, ← Measure.map_apply (measurable_shiftField y) hmeas]
  exact congrArg (fun μ : Measure (Site d → ℝ) =>
    μ {ζ | ¬ BlockGood R (d23Field d R t ζ) ℓ 0}) (massLaw_map_shiftField d ν y)

/-- Uniform exponential moments turn the extended variance bounds into genuine
real bounds and give a subsequential variance limit above the prescribed square. -/
theorem exists_subseq_variance_of_exp_bound (laws : ℕ → Measure ℝ)
    (ν₀ θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hprob : ∀ n, IsProbabilityMeasure (laws n))
    (hmean : ∀ n, ∫ z, z ∂(laws n) = 0)
    (hvar : ∀ n, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (laws n))
    (hint : ∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (laws n))
    (hexp : ∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(laws n) ≤ K₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ℝ,
      ν₀ ^ 2 ≤ v ∧ v ≤ (4 / θ₀ ^ 2) * K₀ ∧
      Tendsto (fun n => variance id (laws (φ n))) atTop (𝓝 v) := by
  have hK : 0 ≤ K₀ :=
    (integral_nonneg fun z => (Real.exp_pos (θ₀ * |z|)).le).trans (hexp 0)
  have hupper (n : ℕ) : evariance id (laws n) ≤
      ENNReal.ofReal ((4 / θ₀ ^ 2) * K₀) := by
    letI := hprob n
    exact evariance_le_of_exp_moment hθ₀ (hmean n) (hint n) (hexp n)
  have hlo (n : ℕ) : ν₀ ^ 2 ≤ variance id (laws n) := by
    have hfin : evariance id (laws n) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hupper n)
    simpa [variance, ENNReal.toReal_ofReal (sq_nonneg ν₀)] using
      ENNReal.toReal_mono hfin (hvar n)
  have hhi (n : ℕ) : variance id (laws n) ≤ (4 / θ₀ ^ 2) * K₀ := by
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hupper n)
  exact exists_subseq_tendsto_variance ((hlo 0).trans (hhi 0))
    (fun n => variance id (laws n)) hlo hhi

/-- The uniform block estimate follows once bad origin blocks are ruled out
along sequences with convergent variances. The level and horizon are chosen
before the laws and their variance limit. -/
theorem d23BlockCrossing_of_convergent_variance
    (d : ℕ) (hd : 1 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hseq : ∀ δ : ℝ, 0 < δ → ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (Rs : ℕ → ℕ) (laws : ℕ → Measure ℝ) (v : ℝ),
        (∀ n, n + 1 ≤ Rs n) →
        (∀ n, IsProbabilityMeasure (laws n)) →
        (∀ n, ∫ z, z ∂(laws n) = 0) →
        (∀ n, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (laws n)) →
        (∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (laws n)) →
        (∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(laws n) ≤ K₀) →
        ν₀ ^ 2 ≤ v → 0 < v → v ≤ (4 / θ₀ ^ 2) * K₀ →
        Tendsto (fun n => variance id (laws n)) atTop (𝓝 v) →
        ¬ (∀ n, ENNReal.ofReal δ < LatticeProb.iidLaw d (laws n)
          {ζ : Site d → ℝ | ¬ BlockGood (Rs n)
            (d23Field d (Rs n) ⌊(Rs n : ℝ) ^ 2 * T⌋₊ ζ)
            (c * (Rs n : ℝ) ^ (2 - (d : ℝ) / 2)) 0})) :
    D23BlockCrossing d ν₀ θ₀ K₀ := by
  apply d23BlockCrossing_of_sequential d ν₀ θ₀ K₀ hθ₀
  intro δ hδ
  obtain ⟨c, T, hc, hT, hno⟩ := hseq δ hδ
  refine ⟨c, T, hc, hT, ?_⟩
  intro Rs laws zs hRs hprob hmean hvar _hupper hint hexp hbad
  obtain ⟨φ, hφ, v, hvlo, hvhi, hv⟩ :=
    exists_subseq_variance_of_exp_bound laws ν₀ θ₀ K₀ hθ₀ hprob hmean hvar hint hexp
  apply hno (fun n => Rs (φ n)) (fun n => laws (φ n)) v
    (fun n => (Nat.add_le_add_right (hφ.id_le n) 1).trans (hRs (φ n)))
    (fun n => hprob (φ n)) (fun n => hmean (φ n)) (fun n => hvar (φ n))
    (fun n => hint (φ n)) (fun n => hexp (φ n)) hvlo
    ((sq_pos_of_pos hν₀).trans_le hvlo) hvhi hv
  intro n
  letI := hprob (φ n)
  simpa only [measure_bad_block_d23_eq_origin d hd] using hbad (φ n)

end Sandpile
