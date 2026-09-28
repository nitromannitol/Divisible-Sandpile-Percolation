import Sandpile.Support.LinConvexSite
import Sandpile.Support.LinChooseL
import Sandpile.Support.LinL2Two

/-!
# Step 2 of the linearization, abstracted from the tested field

Step 2 of `lem:dgt4-linearization-from-survival` (`sandpile.tex:5803-5845`), abstracted
from the tested field.

The paper's Step 2 has three moves. The convex-linear bound of `lem:convex-linear-bound`
applied to the tested field gives `eq:dgt4-convex-linear-remainder`, the vanishing in
`L²` of `F_R - E F_R - ∑_z E[∂_{ζ(z)}F_R] ζ(z)`, from the vanishing variance sum
`eq:dgt4-derivative-variance-limit` and the uniform Green bound
`eq:dgt4-tested-green-bound`. Replacing the mean-gradient coefficients by the profile
coefficients costs `eq:dgt4-linear-coefficient-replacement`, which is the second moment
of a linear functional of the scenery and is controlled by the `ℓ¹` distance of the two
coefficient arrays. Adding the two gives `eq:dgt4-linearization-from-paths`.

Everything here is stated for an arbitrary family of coordinatewise convex functionals of
the field that read finitely many sites, so that the tested field enters only through the
four estimates the paper proves about it.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {V : Type*} [DecidableEq V]

/-- **`eq:dgt4-convex-linear-remainder` (`sandpile.tex:5812-5825`).**  A family of
coordinatewise convex functionals of the field, each reading finitely many sites,
with right derivatives between `0` and `b_R(v)` whose squares are uniformly
summable, and with vanishing site sum of derivative variances, agrees with its
linearization in `L²`. -/
theorem tendsto_l2_convex_linear_remainder {l : Filter ℝ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (S : ℝ → Finset V) (F : ℝ → (V → ℝ) → ℝ) (D : ℝ → V → (V → ℝ) → ℝ) (b : ℝ → V → ℝ)
    (hFm : ∀ R, Measurable (F R))
    (hloc : ∀ (R : ℝ) (ω η : V → ℝ), (∀ v ∈ S R, ω v = η v) → F R ω = F R η)
    (hDm : ∀ R v, Measurable (D R v))
    (hconv : ∀ (R : ℝ) (v : V) (ω : V → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => F R (Function.update ω v y))
    (hderiv : ∀ (R : ℝ) (v : V) (ω : V → ℝ),
      HasDerivWithinAt (fun y => F R (Function.update ω v y)) (D R v ω) (Set.Ici (ω v)) (ω v))
    (hDb : ∀ R : ℝ, ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν),
      ∀ v ∈ S R, 0 ≤ D R v ω ∧ D R v ω ≤ b R v)
    (B₀ : ℝ) (hB₀ : ∀ R : ℝ, ∑ v ∈ S R, b R v ^ 2 ≤ B₀)
    (hVar : Tendsto (fun R : ℝ =>
      ∑ v ∈ S R, variance (D R v) (Measure.infinitePi fun _ : V => ν)) l (𝓝 0)) :
    Tendsto (fun R : ℝ =>
      ∫ ω, (F R ω - (∫ η, F R η ∂(Measure.infinitePi fun _ : V => ν))
          - ∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v) ^ 2
        ∂(Measure.infinitePi fun _ : V => ν)) l (𝓝 0) := by
  have hB₀0 : 0 ≤ B₀ :=
    le_trans (Finset.sum_nonneg fun v _ => sq_nonneg _) (hB₀ 0)
  refine tendsto_zero_of_forall_L (C := convexLinearConst) (B := B₀)
    convexLinearConst_pos.le hB₀0 (Filter.Eventually.of_forall fun R =>
      integral_nonneg fun ω => sq_nonneg _)
    (tendsto_truncatedGap ν hsq) ?_ hVar
  intro L hL
  refine Filter.Eventually.of_forall fun R => ?_
  refine le_trans (convex_linear_bound_local ν hmean hsq (S R) (F R) (hFm R) (hloc R)
    (D R) (hDm R) (hconv R) (hderiv R) (b R) (hDb R) L hL) ?_
  have hgap : 0 ≤ Sandpile.truncatedGap ν L :=
    integral_nonneg fun y => integral_nonneg fun z => by positivity
  have : convexLinearConst * Sandpile.truncatedGap ν L * ∑ v ∈ S R, b R v ^ 2
      ≤ convexLinearConst * Sandpile.truncatedGap ν L * B₀ :=
    mul_le_mul_of_nonneg_left (hB₀ R) (mul_nonneg convexLinearConst_pos.le hgap)
  linarith

/-- **Step 2 of `lem:dgt4-linearization-from-survival`.**  With the coefficient
replacement `eq:dgt4-linear-coefficient-replacement`, the convex-linear remainder
becomes `eq:dgt4-linearization-from-paths`: the functional agrees in `L²` with
the linear field of the profile coefficients. -/
theorem tendsto_l2_linear_of_convex {l : Filter ℝ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (S : ℝ → Finset V) (F : ℝ → (V → ℝ) → ℝ) (D : ℝ → V → (V → ℝ) → ℝ) (b : ℝ → V → ℝ)
    (coef : ℝ → V → ℝ)
    (hFm : ∀ R, Measurable (F R))
    (hloc : ∀ (R : ℝ) (ω η : V → ℝ), (∀ v ∈ S R, ω v = η v) → F R ω = F R η)
    (hDm : ∀ R v, Measurable (D R v))
    (hconv : ∀ (R : ℝ) (v : V) (ω : V → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => F R (Function.update ω v y))
    (hderiv : ∀ (R : ℝ) (v : V) (ω : V → ℝ),
      HasDerivWithinAt (fun y => F R (Function.update ω v y)) (D R v ω) (Set.Ici (ω v)) (ω v))
    (hDb : ∀ R : ℝ, ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν),
      ∀ v ∈ S R, 0 ≤ D R v ω ∧ D R v ω ≤ b R v)
    (B₀ : ℝ) (hB₀ : ∀ R : ℝ, ∑ v ∈ S R, b R v ^ 2 ≤ B₀)
    (hVar : Tendsto (fun R : ℝ =>
      ∑ v ∈ S R, variance (D R v) (Measure.infinitePi fun _ : V => ν)) l (𝓝 0))
    (hcoef : Tendsto (fun R : ℝ => ∑ v ∈ S R,
      ((∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) - coef R v) ^ 2) l (𝓝 0))
    (hI1 : ∀ R : ℝ, Integrable (fun ω => (F R ω
        - (∫ η, F R η ∂(Measure.infinitePi fun _ : V => ν))
        - ∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v) ^ 2)
      (Measure.infinitePi fun _ : V => ν))
    (hI2 : ∀ R : ℝ, Integrable (fun ω =>
        (∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v
          - ∑ v ∈ S R, coef R v * ω v) ^ 2) (Measure.infinitePi fun _ : V => ν))
    (hI3 : ∀ R : ℝ, Integrable (fun ω => (F R ω
        - (∫ η, F R η ∂(Measure.infinitePi fun _ : V => ν))
        - ∑ v ∈ S R, coef R v * ω v) ^ 2) (Measure.infinitePi fun _ : V => ν)) :
    Tendsto (fun R : ℝ =>
      ∫ ω, (F R ω - (∫ η, F R η ∂(Measure.infinitePi fun _ : V => ν))
          - ∑ v ∈ S R, coef R v * ω v) ^ 2
        ∂(Measure.infinitePi fun _ : V => ν)) l (𝓝 0) := by
  have hmemLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  have hrepl : Tendsto (fun R : ℝ =>
      ∫ ω, (∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v
        - ∑ v ∈ S R, coef R v * ω v) ^ 2 ∂(Measure.infinitePi fun _ : V => ν))
      l (𝓝 0) := by
    have hsub : ∀ (R : ℝ) (ω : V → ℝ),
        ∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v
          - ∑ v ∈ S R, coef R v * ω v
        = ∑ v ∈ S R,
            ((∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) - coef R v) * ω v := by
      intro R ω
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    have hbound : ∀ R : ℝ,
        ∫ ω, (∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v
          - ∑ v ∈ S R, coef R v * ω v) ^ 2 ∂(Measure.infinitePi fun _ : V => ν)
        ≤ (∫ z, z ^ 2 ∂ν) * ∑ v ∈ S R,
            ((∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) - coef R v) ^ 2 := by
      intro R
      have := integral_sq_linear_eq_site ν hmean hmemLp (S R)
        (fun v => (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) - coef R v)
      refine le_trans (le_of_eq ?_) (le_of_eq this)
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        congrArg (fun t => t ^ 2) (hsub R ω))
    refine squeeze_zero (fun R => integral_nonneg fun ω => sq_nonneg _) hbound ?_
    have : Tendsto (fun R : ℝ => (∫ z, z ^ 2 ∂ν) * ∑ v ∈ S R,
        ((∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) - coef R v) ^ 2)
        l (𝓝 ((∫ z, z ^ 2 ∂ν) * 0)) :=
      (hcoef.const_mul _)
    simpa using this
  exact tendsto_l2_of_two_remainders (Measure.infinitePi fun _ : V => ν)
    (fun R ω => F R ω)
    (fun R _ => ∫ η, F R η ∂(Measure.infinitePi fun _ : V => ν))
    (fun R ω => ∑ v ∈ S R, coef R v * ω v)
    (fun R ω => ∑ v ∈ S R, (∫ η, D R v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v)
    hI1 hI2 hI3
    (tendsto_l2_convex_linear_remainder ν hmean hsq S F D b hFm hloc hDm hconv hderiv hDb
      B₀ hB₀ hVar)
    hrepl

end Sandpile
