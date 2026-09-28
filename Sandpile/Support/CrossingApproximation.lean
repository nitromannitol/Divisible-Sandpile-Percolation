import Sandpile.Support.EuclideanField
import Sandpile.Support.StableBottleneck
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth uniform approximation of crossing values on Euclidean fields

Uniform smooth approximation of rectangle crossing values with the same Lipschitz constant in
Euclidean scenery coordinates. `FieldNonexpansive.lipschitzWith` records that a nonexpansive
field functional is automatically `1`-Lipschitz for the sup-metric on field configurations, and
`contDiff_linearField_euclidean` records that a linear parametrization `linearField A` of field
configurations by a Euclidean parameter space is smooth (`C^∞`). The main result,
`exists_smooth_crossing_uniform_approximation`, combines these with the general smoothing
bottleneck `exists_positive_rectangle_bottleneck` to build, for a lattice rectangle `Q` and any
`D`-bounded linear parametrization `A`, a `C^1`, `D`-Lipschitz function `g` on the parameter
space that approximates `crossingValue Q (linearField A x.ofLp)` uniformly to within any given
tolerance `e`.
-/

open LatticeProb

open scoped BigOperators NNReal
noncomputable section
namespace Sandpile

/-- A nonexpansive field functional `f` (in the sense of `FieldNonexpansive`) is `1`-Lipschitz
for the sup-distance on field configurations, since the defining inequality of `FieldNonexpansive`
applied with the sup-distance bound at every coordinate gives exactly the Lipschitz estimate. -/
lemma FieldNonexpansive.lipschitzWith {V : Type*} [Fintype V] {f : (V → ℝ) → ℝ}
    (hf : FieldNonexpansive f) : LipschitzWith 1 f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact hf x y (dist x y) dist_nonneg (fun i => by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y i)

/-- The linear field map `x ↦ linearField A x.ofLp` is smooth (`C^∞`) as a function of the
Euclidean parameter `x`, since each output coordinate `v` is a finite sum of coordinate
projections of `x` scaled by the constants `A v i`. -/
lemma contDiff_linearField_euclidean {V I : Type*} [Fintype V] [Fintype I]
    (A : V → I → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ I => linearField A x.ofLp) := by
  apply contDiff_pi.mpr
  intro v
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ I => ∑ i, A v i * x.ofLp i)
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp PiLp.contDiff_ofLp)

/-- For a lattice rectangle `Q` with at least two sites and a `D`-bounded linear parametrization
`A` of field configurations by the Euclidean space `EuclideanSpace ℝ I`, there is a `C^1`,
`D`-Lipschitz function `g` on the parameter space that approximates
`crossingValue Q (linearField A x.ofLp)` uniformly to within any given tolerance `e > 0`; `g`
is `L ∘ linearField A` for the bottleneck smoothing `L` given by
`exists_positive_rectangle_bottleneck` at a smoothing depth `β` chosen large enough relative to
`e`, and its Lipschitz constant is inherited from `FieldNonexpansive.lipschitzWith`. -/
lemma exists_smooth_crossing_uniform_approximation {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {I : Type*} [Fintype I]
    (A : Q → I → ℝ) (D : ℝ≥0) (hA : ∀ v, (∑ i, A v i ^ 2) ≤ (D : ℝ) ^ 2)
    (e : ℝ) (he : 0 < e) :
    ∃ g : EuclideanSpace ℝ I → ℝ, ContDiff ℝ 1 g ∧ LipschitzWith D g ∧
      ∀ x, |crossingValue Q (linearField A x.ofLp) - g x| ≤ e := by
  classical
  obtain ⟨C, hC, hs⟩ := exists_positive_rectangle_bottleneck
  let β : ℝ := max 1 (C * (Real.log Q.card) ^ 2 / e)
  have hβ : 1 ≤ β := le_max_left _ _
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  obtain ⟨n, L, _, ⟨J, hJ⟩, happrox⟩ := hs Q hQ hN β hβ
  let g (x : EuclideanSpace ℝ I) := L (linearField A x.ofLp)
  refine ⟨g, ?_, ?_, ?_⟩
  · exact (hJ.smooth.comp (contDiff_linearField_euclidean A)).of_le (by simp)
  · have hh := (FieldNonexpansive.lipschitzWith hJ.nonexpansive).comp
      (lipschitzWith_linearField_euclidean A D hA)
    simpa only [one_mul, Function.comp_def] using hh
  · intro x
    calc
      _ = |L (linearField A x.ofLp) - crossingValue Q (linearField A x.ofLp)| := abs_sub_comm _ _
      _ ≤ C * (Real.log Q.card) ^ 2 / β := happrox _
      _ ≤ e := by
        apply (div_le_iff₀ hβpos).mpr
        have hh : C * (Real.log Q.card) ^ 2 / e ≤ β := le_max_right _ _
        exact (div_le_iff₀ he).mp hh |>.trans_eq (mul_comm β e)

end Sandpile
