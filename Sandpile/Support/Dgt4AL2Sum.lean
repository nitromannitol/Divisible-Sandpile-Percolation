/-
The `L²` bound for a finite sum: the `L²` norm of `∑_{i<j}f_i` is at most `j` times the
largest `L²` norm of a term.  It is the summation step of the `L²` assembly of
`eq:dgt4-centered-value-decay` of case (a) Step 1 of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5074-5077`).  The proof is the pointwise Cauchy-Schwarz bound
`(∑_{i<j}f_i)² ≤ j∑_{i<j}f_i²`.
-/
import Sandpile.Support.Dgt4AL2Tri

open MeasureTheory Filter Topology

namespace Sandpile

/-- `‖∑_{i<j}f_i‖₂ ≤ j·B` when every `‖f_i‖₂ ≤ B`. -/
theorem sqrt_integral_sq_sum_range_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (B : ℝ) (j : ℕ)
    (hB : 0 ≤ B)
    (hint : ∀ i, Integrable (fun ω => f i ω ^ 2) μ)
    (hsum : ∀ k, Integrable (fun ω => (∑ i ∈ Finset.range k, f i ω) ^ 2) μ)
    (hterm : ∀ i, Real.sqrt (∫ ω, f i ω ^ 2 ∂μ) ≤ B) :
    Real.sqrt (∫ ω, (∑ i ∈ Finset.range j, f i ω) ^ 2 ∂μ) ≤ j * B := by
  have hpt : ∀ ω, (∑ i ∈ Finset.range j, f i ω) ^ 2
      ≤ (j : ℝ) * ∑ i ∈ Finset.range j, f i ω ^ 2 := by
    intro ω
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range j) (f := fun i => f i ω)
    simpa using h
  have hsumsq : Integrable (fun ω => ∑ i ∈ Finset.range j, f i ω ^ 2) μ :=
    integrable_finsetSum _ fun i _ => hint i
  have hle : ∫ ω, (∑ i ∈ Finset.range j, f i ω) ^ 2 ∂μ
      ≤ ∫ ω, (j : ℝ) * ∑ i ∈ Finset.range j, f i ω ^ 2 ∂μ :=
    integral_mono (hsum j) (hsumsq.const_mul _) hpt
  have hsplit : ∫ ω, (j : ℝ) * ∑ i ∈ Finset.range j, f i ω ^ 2 ∂μ
      = (j : ℝ) * ∑ i ∈ Finset.range j, ∫ ω, f i ω ^ 2 ∂μ := by
    rw [integral_const_mul]
    congr 1
    exact integral_finsetSum _ fun i _ => hint i
  have hterm' : ∀ i ∈ Finset.range j, ∫ ω, f i ω ^ 2 ∂μ ≤ B ^ 2 := by
    intro i _
    have hnn : 0 ≤ ∫ ω, f i ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have h := hterm i
    nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, f i ω ^ 2 ∂μ), hB]
  have hfin : ∑ i ∈ Finset.range j, ∫ ω, f i ω ^ 2 ∂μ ≤ ∑ _i ∈ Finset.range j, B ^ 2 :=
    Finset.sum_le_sum hterm'
  rw [hsplit] at hle
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg B
  have hcard : ∑ _i ∈ Finset.range j, B ^ 2 = (j : ℝ) * B ^ 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hcard] at hfin
  have hfinal : ∫ ω, (∑ i ∈ Finset.range j, f i ω) ^ 2 ∂μ ≤ ((j : ℝ) * B) ^ 2 := by
    have h2 := mul_le_mul_of_nonneg_left hfin (Nat.cast_nonneg (α := ℝ) j)
    nlinarith [hle, h2, Nat.cast_nonneg (α := ℝ) j, sq_nonneg B]
  calc Real.sqrt (∫ ω, (∑ i ∈ Finset.range j, f i ω) ^ 2 ∂μ)
      ≤ Real.sqrt (((j : ℝ) * B) ^ 2) := Real.sqrt_le_sqrt hfinal
    _ = (j : ℝ) * B := Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg j) hB)

end Sandpile
