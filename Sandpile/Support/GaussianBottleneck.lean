import Sandpile.Support.GaussianScale
import Sandpile.Support.GaussianApproximation
import Sandpile.Support.CrossingApproximation

/-!
# Gaussian exponential concentration for rectangle crossing values

Gaussian exponential concentration for rectangle crossing values of finite linear fields
and translated finite Green kernels. `hasSubgaussianMGF_crossingValue_linear` shows the
crossing value of a finite linear field `linearField A x`, centred at its Gaussian mean, is
subgaussian with variance proxy `π²D²/4` when the coefficients obey `∑ A v i² ≤ D²`, using
that `crossingValue` is Lipschitz in `x` and `hasSubgaussianMGF_of_smooth_uniform_approximation`.
`hasSubgaussianMGF_crossingValue_gaussian` rescales this to an arbitrary Gaussian variance `v`
by pulling the scale `√v` into the coefficients. `finiteKernelField_integral` transports an
integral of a measurable function of the kernel field family to the finite product law of a
common support, mirroring `finiteKernelField_sublevel_measure` for integrals, and
`hasSubgaussianMGF_finiteKernel_crossing` combines it with the linear-field subgaussian bound
to get the same concentration for a translated finite kernel field.
`subgaussian_centered_lower_tail` extracts the one-sided lower-tail bound
`P(f ≤ m - t) ≤ exp(-t²/2c)` from a subgaussian MGF bound, and
`exists_gaussian_far_crossing_concentration` specializes the whole chain to the cut-off ball
Green field, giving a lower-tail bound with variance proxy `π²GV log(r)/2`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

/-- The crossing value of a finite linear field `linearField A x`, centred at its Gaussian
mean, has a subgaussian MGF with variance proxy `π²D²/4` when `∑ A v i² ≤ D²`: this follows
from `hasSubgaussianMGF_of_smooth_uniform_approximation`, using that `crossingValue` composed
with `linearField A` is Lipschitz (`lipschitzWith_crossingValue_linear_euclidean`) and can be
uniformly approximated by smooth functions (`exists_smooth_crossing_uniform_approximation`). -/
lemma hasSubgaussianMGF_crossingValue_linear {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {I : Type*} [Fintype I]
    (A : Q → I → ℝ) (D : ℝ≥0) (hA : ∀ v, (∑ i, A v i ^ 2) ≤ (D : ℝ) ^ 2) :
    HasSubgaussianMGF (fun x : EuclideanSpace ℝ I => crossingValue Q (linearField A x.ofLp) -
      ∫ y : EuclideanSpace ℝ I, crossingValue Q (linearField A y.ofLp)
        ∂stdGaussian (EuclideanSpace ℝ I))
      ⟨Real.pi ^ 2 * (D : ℝ) ^ 2 / 4, by positivity⟩ (stdGaussian (EuclideanSpace ℝ I)) := by
  apply hasSubgaussianMGF_of_smooth_uniform_approximation
    (lipschitzWith_crossingValue_linear_euclidean hQ
      (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hN)) A D hA)
  exact exists_smooth_crossing_uniform_approximation hQ hN A D hA

/-- Rescaling `hasSubgaussianMGF_crossingValue_linear` from the standard Gaussian to
`Measure.pi (fun _ => gaussianReal 0 v)`: the coordinates `B z i = √v · A z i` obey
`∑ B z i² ≤ D²` when `v ∑ A z i² ≤ D²`, and pushing forward along the scaling map
`measurePreserving_stdGaussian_scaled_coordinates` transports the centred subgaussian bound
for `B` to one for `A` under the scaled product law. -/
lemma hasSubgaussianMGF_crossingValue_gaussian {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {I : Type*} [Fintype I]
    (A : Q → I → ℝ) (v D : ℝ≥0) (hA : ∀ z, (v : ℝ) * (∑ i, A z i ^ 2) ≤ (D : ℝ) ^ 2) :
    HasSubgaussianMGF (fun x : I → ℝ => crossingValue Q (linearField A x) -
      ∫ y : I → ℝ, crossingValue Q (linearField A y)
        ∂Measure.pi (fun _ : I => gaussianReal 0 v))
      ⟨Real.pi ^ 2 * (D : ℝ) ^ 2 / 4, by positivity⟩
      (Measure.pi (fun _ : I => gaussianReal 0 v)) := by
  let B (z : Q) (i : I) := Real.sqrt (v : ℝ) * A z i
  have hB (z : Q) : (∑ i, B z i ^ 2) ≤ (D : ℝ) ^ 2 := by
    calc
      _ = (v : ℝ) * (∑ i, A z i ^ 2) := by
        simp only [B, mul_pow, Real.sq_sqrt v.coe_nonneg, Finset.mul_sum]
      _ ≤ _ := hA z
  have hh := hasSubgaussianMGF_crossingValue_linear hQ hN B D hB
  have hf : Measurable (fun x : I → ℝ => crossingValue Q (linearField A x)) :=
    ((continuous_crossingValue hQ (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hN))).comp
      (continuous_linearField A)).measurable
  apply hasSubgaussianMGF_centered_of_measurePreserving
    (measurePreserving_stdGaussian_scaled_coordinates v) hf
  have he (x : EuclideanSpace ℝ I) :
      linearField A (fun i => Real.sqrt (v : ℝ) * x.ofLp i) = linearField B x.ofLp := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    dsimp [B]
    ring
  simpa only [he] using hh

/-- Integrating a measurable function `value` of the kernel field family under the i.i.d.
law equals integrating the corresponding `linearField` on the finite restriction, using
`measurePreserving_finite_restrict` to transport the integral and
`finiteKernelField_eq_linearField` to identify the two integrands. -/
lemma finiteKernelField_integral {d : ℕ} {V : Type*} [Fintype V]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Site d → ℝ) (z : V → Site d)
    (s : Finset (Site d)) (hs : ∀ v y, y ∉ s → h (y - z v) = 0)
    (value : (V → ℝ) → ℝ) (hv : Measurable value) :
    (∫ ζ, value (fun v => finiteKernelField h ζ (z v)) ∂LatticeProb.iidLaw d μ) =
      ∫ x, value (linearField (fun v (i : s) => h ((i : Site d) - z v)) x)
        ∂Measure.pi (fun _ : s => μ) := by
  have hm := measurePreserving_finite_restrict μ s
  have hc := hv.comp (continuous_linearField (fun v (i : s) => h ((i : Site d) - z v))).measurable
  have hh := integral_map hm.aemeasurable hc.aestronglyMeasurable
  rw [hm.map_eq] at hh
  simpa only [Function.comp_def, finiteKernelField_eq_linearField h z s hs] using hh.symm

/-- The crossing value of a translated finite kernel field `finiteKernelField h ζ (z w)`,
centred at its mean under the i.i.d. Gaussian law, is subgaussian with the same variance
proxy `π²D²/4` as the linear case: the coordinates `A w i = h(i - z w)` on a common finite
support (`exists_finiteKernelField_coordinates`) obey `v ∑ A w i² ≤ D²` by
`sum_translate_sq_le_tsum`, so `hasSubgaussianMGF_crossingValue_gaussian` applies to them,
and `finiteKernelField_eq_linearField`/`finiteKernelField_integral` transport the bound back
to the kernel field family. -/
lemma hasSubgaussianMGF_finiteKernel_crossing {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {d : ℕ}
    {h : Site d → ℝ} (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0)
    (hsq : Summable (fun u => h u ^ 2)) (z : Q → Site d) (v D : ℝ≥0)
    (hD : (v : ℝ) * (∑' u, h u ^ 2) ≤ (D : ℝ) ^ 2) :
    HasSubgaussianMGF
      (fun ζ : Site d → ℝ => crossingValue Q (fun w => finiteKernelField h ζ (z w)) -
        ∫ ξ : Site d → ℝ, crossingValue Q (fun w => finiteKernelField h ξ (z w))
          ∂LatticeProb.iidLaw d (gaussianReal 0 v))
      ⟨Real.pi ^ 2 * (D : ℝ) ^ 2 / 4, by positivity⟩
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  obtain ⟨s, hs⟩ := exists_finiteKernelField_coordinates t ht z
  let A (w : Q) (i : s) := h ((i : Site d) - z w)
  have hA (w : Q) : (v : ℝ) * (∑ i, A w i ^ 2) ≤ (D : ℝ) ^ 2 := by
    exact (mul_le_mul_of_nonneg_left (sum_translate_sq_le_tsum hsq s (z w)) v.coe_nonneg).trans hD
  have hh := hasSubgaussianMGF_crossingValue_gaussian hQ hN A v D hA
  have hm := measurePreserving_finite_restrict (gaussianReal 0 v) s
  have hmval :=
    measurable_crossingValue hQ (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hN))
  have he := finiteKernelField_integral (gaussianReal 0 v) h z s hs (crossingValue Q) hmval
  rw [← hm.map_eq] at hh
  have hp := hh.of_map hm.aemeasurable
  rw [hm.map_eq] at hp
  rw [he]
  simpa only [Function.comp_def, A, finiteKernelField_eq_linearField h z s hs] using hp

/-- **The one-sided lower tail of a subgaussian random variable.** If `f - m` has a
subgaussian MGF with variance proxy `c`, then `P(f ≤ m - t) ≤ exp(-t²/2c)`: apply the
subgaussian upper-tail bound to `-(f - m)` and rewrite the event. -/
lemma subgaussian_centered_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {m : ℝ} {c : ℝ≥0}
    (hf : HasSubgaussianMGF (fun x => f x - m) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {x | f x ≤ m - t} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
  have he : {x | f x ≤ m - t} = {x | t ≤ -(f x - m)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hh <;> linarith
  rw [he]
  have hh := hf.neg.measure_ge_le ht
  change μ.real {x | t ≤ -(f x - m)} ≤ _ at hh
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    using ENNReal.ofReal_le_ofReal hh

/-- **The cut-off ball Green field crossing value concentrates below its Gaussian mean at
scale `log r`.** Combines `hasSubgaussianMGF_finiteKernel_crossing`, with `D² = V G log r`
bounding `v ∑' cutField²` via `cutField_square_sum_bound` and `v ≤ V`, with
`subgaussian_centered_lower_tail` to get variance proxy `2(π²D²/4) = π²GV log(r)/2`. -/
lemma exists_gaussian_far_crossing_concentration (hBall : External.BallGreenBounds) :
    ∃ C > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card → ∀ z : Q → Site 4,
        ∀ v V : ℝ≥0, v ≤ V → ∀ t : ℝ, 0 ≤ t →
          LatticeProb.iidLaw 4 (gaussianReal 0 v)
            {ζ |
              crossingValue Q
                (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w)) ≤
              (∫ ξ : Site 4 → ℝ,
                crossingValue Q
                  (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ξ (z w))
                ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) - t} ≤
            ENNReal.ofReal (Real.exp (-t ^ 2 / (C * V * Real.log r))) := by
  obtain ⟨G, hG, hsum⟩ := cutField_square_sum_bound hBall
  refine ⟨Real.pi ^ 2 * G / 2, by positivity, ?_⟩
  intro r hr L φ hφ Q hQ hN z v V hv t ht
  let D : ℝ≥0 := ⟨Real.sqrt ((V : ℝ) * G * Real.log r), Real.sqrt_nonneg _⟩
  have hn : 0 ≤ (V : ℝ) * G * Real.log r :=
    mul_nonneg (mul_nonneg V.coe_nonneg hG.le) (Real.log_natCast_nonneg r)
  have hD : (v : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) ≤ (D : ℝ) ^ 2 := by
    change (v : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) ≤
      Real.sqrt ((V : ℝ) * G * Real.log r) ^ 2
    rw [Real.sq_sqrt hn]
    calc
      _ ≤ (V : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) :=
        mul_le_mul_of_nonneg_right (show (v : ℝ) ≤ V from hv) (tsum_nonneg (fun _ => sq_nonneg _))
      _ ≤ (V : ℝ) * (G * Real.log r) := mul_le_mul_of_nonneg_left (hsum r hr L φ hφ) V.coe_nonneg
      _ = _ := by ring
  have hSG := hasSubgaussianMGF_finiteKernel_crossing hQ hN (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu)
    (summable_cutField_sq r L φ) z v D hD
  have hp := subgaussian_centered_lower_tail hSG ht
  have hd : 2 * (Real.pi ^ 2 * (D : ℝ) ^ 2 / 4) = (Real.pi ^ 2 * G / 2) * V * Real.log r := by
    change 2 * (Real.pi ^ 2 * Real.sqrt ((V : ℝ) * G * Real.log r) ^ 2 / 4) = _
    rw [Real.sq_sqrt hn]
    ring
  change _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (Real.pi ^ 2 * (D : ℝ) ^ 2 / 4)))) at hp
  rw [hd] at hp
  exact hp

end Sandpile
