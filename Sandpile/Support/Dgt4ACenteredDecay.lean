/-
The `L²` assembly of `eq:dgt4-centered-value-decay` of case (a) Step 1 of
`prop:dgt4-contact-asymptotics` (`sandpile.tex:5074-5077`): the telescoping
`w(0)+c = P^j(w+c)(0) + \sum_{i<j}P^i(w-Pw)(0)` of `Support/Dgt4ATelescope.lean`,
the `L²` bound on the `j`-step average and the `L²` bound on each telescoping term
combine into

  `(E[(V_\infty(0)-u_n(0)+E u_n(0))^2])^{1/2} ≤ Cj n^{-1/2}\sqrt{\log(n+2)} + Cj^{-(d-4)/4}`.

The two `L²` bounds are the inputs the paper's Gaussian concentration supplies; the
summation is `Support/Dgt4AL2Sum.lean`.
-/
import Sandpile.Support.Dgt4AL2Sum

open MeasureTheory Filter Topology Set

namespace Sandpile

/-- **`eq:dgt4-centered-value-decay`** (`sandpile.tex:5069-5072`), in the form the paper
uses: if the centred value splits as `w + c = u + v` with `L²` bounds `A` on `u` and `j*B`
on `v`, then its `L²` norm is at most `j*B + A`. -/
theorem sqrt_integral_sq_centeredValue_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (w u v : Ω → ℝ) (c B A : ℝ) (j : ℕ)
    (hB : 0 ≤ B)
    (hterm : ∀ _ : ℕ, Real.sqrt (∫ ω, (w ω - (∫ η, w η ∂μ)) ^ 2 ∂μ) ≤ B)
    (hstep : Real.sqrt (∫ ω, u ω ^ 2 ∂μ) ≤ A)
    (hint : ∀ _ : ℕ, Integrable (fun ω => (w ω - (∫ η, w η ∂μ)) ^ 2) μ)
    (hsum : ∀ k : ℕ, Integrable (fun ω => (∑ _ ∈ Finset.range k,
      (w ω - (∫ η, w η ∂μ))) ^ 2) μ)
    (hu : Integrable (fun ω => u ω ^ 2) μ)
    (hvint : Integrable (fun ω => v ω ^ 2) μ)
    (huv : Integrable (fun ω => (u ω + v ω) ^ 2) μ)
    (hdec : ∀ ω, w ω + c = u ω + v ω)
    (hv : ∀ ω, v ω = ∑ _ ∈ Finset.range j, (w ω - (∫ η, w η ∂μ))) :
    Real.sqrt (∫ ω, (w ω + c) ^ 2 ∂μ) ≤ 2 * (j * B + A) := by
  have hsq : (fun ω => (w ω + c) ^ 2) = fun ω => (u ω + v ω) ^ 2 := by
    funext ω
    rw [hdec ω]
  have h1 : Real.sqrt (∫ ω, (w ω + c) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, (u ω + v ω) ^ 2 ∂μ) := by
    rw [hsq]
  have h2 : Real.sqrt (∫ ω, (u ω + v ω) ^ 2 ∂μ)
      ≤ Real.sqrt 2 * (Real.sqrt (∫ ω, u ω ^ 2 ∂μ)
        + Real.sqrt (∫ ω, v ω ^ 2 ∂μ)) :=
    sqrt_integral_sq_add_le μ u v hu hvint huv
  have h3 : Real.sqrt (∫ ω, v ω ^ 2 ∂μ) ≤ j * B := by
    have hvint : (∫ ω, v ω ^ 2 ∂μ)
        = ∫ ω, (∑ i ∈ Finset.range j, (w ω - (∫ η, w η ∂μ))) ^ 2 ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only []
      rw [hv ω]
    rw [hvint]
    exact sqrt_integral_sq_sum_range_le μ (fun _ ω => w ω - (∫ η, w η ∂μ)) B j hB
      (fun i => hint i) hsum (fun i => hterm i)
  have h4 : Real.sqrt 2 * (Real.sqrt (∫ ω, u ω ^ 2 ∂μ)
      + Real.sqrt (∫ ω, v ω ^ 2 ∂μ)) ≤ 2 * (j * B + A) := by
    have h2le : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hsum2 : Real.sqrt (∫ ω, u ω ^ 2 ∂μ) + Real.sqrt (∫ ω, v ω ^ 2 ∂μ) ≤ A + j * B := by
      linarith
    have h0 : 0 ≤ Real.sqrt (∫ ω, u ω ^ 2 ∂μ) + Real.sqrt (∫ ω, v ω ^ 2 ∂μ) := by
      positivity
    calc Real.sqrt 2 * (Real.sqrt (∫ ω, u ω ^ 2 ∂μ) + Real.sqrt (∫ ω, v ω ^ 2 ∂μ))
        ≤ 2 * (Real.sqrt (∫ ω, u ω ^ 2 ∂μ) + Real.sqrt (∫ ω, v ω ^ 2 ∂μ)) :=
          mul_le_mul_of_nonneg_right h2le h0
      _ ≤ 2 * (j * B + A) := by linarith
  linarith

end Sandpile
