import Sandpile.Support.CornerMeasure
import Sandpile.Support.DirectionalThird
import LatticeProb.Prob.TaylorComparison
import Sandpile.Support.StableIntegral

/-!
# A finite Lindeberg comparison via matching third moments

`MatchingThirdMoments` packages the third-order Taylor comparison hypotheses between two laws
`μ` and `ν`, and `MatchingThirdMoments.compare` bounds the resulting gap for a single test
function by `J * T / 3` in terms of a third-derivative envelope `J` and the moment constant
`T`. `finite_product_lindeberg` iterates this comparison coordinate by coordinate across a
finite index set, replacing `μ` by `ν` one coordinate at a time along `linearField A` under
stable derivative envelopes for the composed function `φ` and a bound on the cubic overlap of
the columns of `A`, giving a single Lindeberg-type bound for a smooth bounded function of the
linear combination.
-/

open LatticeProb

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Sandpile

/-- The hypotheses that let a third-order Taylor comparison of test functions between `μ` and
`ν` go through: `μ` and `ν` have the same mean and second moment, are integrable in `x` and
`x ^ 2`, and their weighted third-absolute-moment integrals `∫ |x| ^ 3 * exp (κ|x|)` are both
bounded by a common constant `T`. -/
structure MatchingThirdMoments (μ ν : Measure ℝ) (κ T : ℝ) : Prop where
  mu_id : Integrable (fun x : ℝ => x) μ
  nu_id : Integrable (fun x : ℝ => x) ν
  mu_sq : Integrable (fun x : ℝ => x ^ 2) μ
  nu_sq : Integrable (fun x : ℝ => x ^ 2) ν
  mean_eq : (∫ x : ℝ, x ∂μ) = ∫ x : ℝ, x ∂ν
  second_eq : (∫ x : ℝ, x ^ 2 ∂μ) = ∫ x : ℝ, x ^ 2 ∂ν
  mu_weight : Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) μ
  nu_weight : Integrable (fun x : ℝ => |x| ^ 3 * Real.exp (κ * |x|)) ν
  mu_bound : (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂μ) ≤ T
  nu_bound : (∫ x : ℝ, |x| ^ 3 * Real.exp (κ * |x|) ∂ν) ≤ T

/-- The constant `T` of `MatchingThirdMoments` is nonnegative, since it bounds the nonnegative
integral `∫ |x| ^ 3 * exp (κ|x|) dμ`. -/
lemma MatchingThirdMoments.nonneg {μ ν : Measure ℝ} {κ T : ℝ}
    (h : MatchingThirdMoments μ ν κ T) : 0 ≤ T :=
  (integral_nonneg
    (fun x => mul_nonneg (pow_nonneg (abs_nonneg x) 3) (Real.exp_pos _).le)).trans h.mu_bound

/-- For `f` with `ContDiff ℝ 3` and third derivative bounded by `J * exp (κ|x|)`, matching
third moments (`MatchingThirdMoments`) bound the gap `|∫ f dν - ∫ f dμ|` by `J * T / 3`, via
the library's third-order Taylor comparison `integral_comparison_third_order`. -/
lemma MatchingThirdMoments.compare {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {κ T : ℝ}
    (h : MatchingThirdMoments μ ν κ T) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (hμf : Integrable f μ) (hνf : Integrable f ν) {J : ℝ} (hJ : 0 ≤ J) (hκ : 0 ≤ κ)
    (hbound : ∀ x, |iteratedDeriv 3 f x| ≤ J * Real.exp (κ * |x|)) :
    |(∫ x, f x ∂ν) - (∫ x, f x ∂μ)| ≤ J * T / 3 :=
  integral_comparison_third_order hf hμf hνf h.mu_id h.nu_id h.mu_sq h.nu_sq
    h.mean_eq h.second_eq hJ hκ hbound h.mu_weight h.nu_weight h.mu_bound h.nu_bound

/-- A continuous function bounded in absolute value by a constant `M` is integrable against
any finite measure. -/
lemma integrable_continuous_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable M
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hM x)

variable {I V : Type*} [Fintype I] [Fintype V]

/-- The linear field `v ↦ ∑ i, A v i * x i` built from a matrix `A : V → I → ℝ` and a vector
`x : I → ℝ`. -/
def linearField (A : V → I → ℝ) (x : I → ℝ) : V → ℝ := fun v => ∑ i, A v i * x i

omit [Fintype V] in
/-- `linearField A` is continuous in `x`, as a finite sum of continuous coordinate
projections. -/
lemma continuous_linearField (A : V → I → ℝ) : Continuous (linearField A) := by
  unfold linearField
  fun_prop

variable [DecidableEq I] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Splitting `linearField A` along the coordinate `i` gives the affine line `fieldLine`: the
value of the field with the `i`-th coordinate set to `0`, translated by `x` times the `i`-th
column `fun v => A v i`. -/
lemma linearField_split_line (A : V → I → ℝ) (i : I)
    (r : {j : I // j ≠ i} → ℝ) (x : ℝ) :
    linearField A ((measurableFunSplitAt i).symm (x, r)) =
      fieldLine (linearField A ((measurableFunSplitAt i).symm (0, r))) (fun v => A v i) x := by
  ext v
  have he (a : ℝ) : linearField A ((measurableFunSplitAt i).symm (a, r)) v =
      A v i * a + ∑ j : {j : I // j ≠ i}, A v j * r j := by
    unfold linearField
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i]
    simp only [measurableFunSplitAt_symm_self, measurableFunSplitAt_symm_other]
  change _ = linearField A ((measurableFunSplitAt i).symm (0, r)) v + A v i * x
  rw [he x, he 0]
  ring

/-- The finite Lindeberg-type comparison: for a bounded, smooth `φ`, a matrix `A` whose
entries are bounded by `a`, matching third moments (`MatchingThirdMoments`) between `μ` and
`ν` at weight `κ = K * a`, stable triple partial derivatives of `φ` bounded by `J` with
column sum `B` and overlap `Q`, and a common small-ball lower bound `p` for `μ` and `ν`, the
difference `|∫ φ ∘ linearField A dν^I - ∫ φ ∘ linearField A dμ^I|` is at most
`(T / 3) * (exp (K * (a * R)) / p) * (B * Q)`. -/
lemma finite_product_lindeberg (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ : (V → ℝ) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {M : ℝ} (hφbound : ∀ F, |φ F| ≤ M)
    (A : V → I → ℝ) {J : V → V → V → (V → ℝ) → ℝ}
    (hJcont : ∀ v w z, Continuous (J v w z))
    {K a R p T B Q : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (hR : 0 ≤ R) (hp : 0 < p) (hQ : 0 ≤ Q)
    (hJstable : ∀ v w z, ExpStable K (J v w z))
    (hJbound : ∀ v w z F, |coordPartial (coordPartial (coordPartial φ v) w) z F| ≤ J v w z F)
    (hJsum : ∀ F, ∑ v, ∑ w, ∑ z, J v w z F ≤ B)
    (hA : ∀ v i, |A v i| ≤ a)
    (hoverlap : ∀ v w z, ∑ i, |A v i * A w i * A z i| ≤ Q)
    (hm : MatchingThirdMoments μ ν (K * a) T)
    (hμsmall : p ≤ μ.real (Icc (-R) R)) (hνsmall : p ≤ ν.real (Icc (-R) R)) :
    |(∫ x, φ (linearField A x) ∂Measure.pi (fun _ : I => ν)) -
      (∫ x, φ (linearField A x) ∂Measure.pi (fun _ : I => μ))| ≤
      ((T / 3) * (Real.exp (K * (a * R)) / p)) * (B * Q) := by
  let D (i : I) : (V → ℝ) → ℝ := thirdContraction J (fun v => A v i)
  have hDstable (i : I) : ExpStable K (D i) := expStable_thirdContraction hJstable _
  have hDcont (i : I) : Continuous (D i) := continuous_thirdContraction hJcont _
  have hDsum (F : V → ℝ) : ∑ i, D i F ≤ B * Q :=
    sum_thirdContraction_le (fun v w z F => (hJstable v w z).nonneg F) A hQ hoverlap hJsum F
  have hDbound (i : I) (F : V → ℝ) : |D i F| ≤ B * Q := by
    rw [abs_of_nonneg ((hDstable i).nonneg F)]
    exact (Finset.single_le_sum (fun j _ => (hDstable j).nonneg F)
      (Finset.mem_univ i)).trans (hDsum F)
  let E (i : I) (x : I → ℝ) : ℝ := D i (linearField A x)
  let f (x : I → ℝ) : ℝ := φ (linearField A x)
  have hf (s : I → Bool) : Integrable f (Measure.pi (cornerLaw μ ν s)) :=
    integrable_continuous_of_abs_bound (hφ.continuous.comp (continuous_linearField A))
      (fun x => hφbound _)
  have hE (s : I → Bool) (i : I) : Integrable (E i) (Measure.pi (cornerLaw μ ν s)) :=
    integrable_continuous_of_abs_bound ((hDcont i).comp (continuous_linearField A))
      (fun x => hDbound i _)
  apply corner_expectation_replacement_bound μ ν E hf hE
    (mul_nonneg (div_nonneg hm.nonneg (by norm_num)) (div_nonneg (Real.exp_pos _).le hp.le))
    (fun x => hDsum (linearField A x))
  intro s i r
  let F := linearField A ((measurableFunSplitAt i).symm (0, r))
  let col : V → ℝ := fun v => A v i
  have hlinecont := contDiff_fieldLine F col
  have hfμ : Integrable (fun x => φ (fieldLine F col x)) μ :=
    integrable_continuous_of_abs_bound (hφ.continuous.comp hlinecont.continuous)
      (fun x => hφbound _)
  have hfν : Integrable (fun x => φ (fieldLine F col x)) ν :=
    integrable_continuous_of_abs_bound (hφ.continuous.comp hlinecont.continuous)
      (fun x => hφbound _)
  have hDi : Integrable (fun x => D i (fieldLine F col x)) (cornerLaw μ ν s i) :=
    integrable_continuous_of_abs_bound ((hDcont i).comp hlinecont.continuous)
      (fun x => hDbound i _)
  have ht := hm.compare
    ((hφ.comp hlinecont).of_le (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top)))
    hfμ hfν ((hDstable i).nonneg F) (mul_nonneg hK ha)
    (abs_iteratedDeriv_three_le_stable hφ hJstable hJbound F col ha (fun v => hA v i))
  have hsmall : p ≤ (cornerLaw μ ν s i).real (Icc (-R) R) := by
    unfold cornerLaw
    cases s i
    · exact hμsmall
    · exact hνsmall
  have hbase := ExpStable.base_le_integral_line (hDstable i) F col hDi ha hR hp
    (fun v => hA v i) hsmall
  have hφline : (fun x : ℝ => φ (linearField A ((measurableFunSplitAt i).symm (x, r)))) =
      fun x => φ (fieldLine F col x) := by
    funext x
    rw [linearField_split_line]
  have hDline : (fun x : ℝ => D i (linearField A ((measurableFunSplitAt i).symm (x, r)))) =
      fun x => D i (fieldLine F col x) := by
    funext x
    rw [linearField_split_line]
  dsimp only [f, E]
  rw [hφline, hDline]
  change |(∫ x, φ (fieldLine F col x) ∂ν) - (∫ x, φ (fieldLine F col x) ∂μ)| ≤
    ((T / 3) * (Real.exp (K * (a * R)) / p)) *
      ∫ x, D i (fieldLine F col x) ∂cornerLaw μ ν s i
  calc
    _ ≤ D i F * T / 3 := ht
    _ = (T / 3) * D i F := by ring
    _ ≤ (T / 3) * ((Real.exp (K * (a * R)) / p) *
        ∫ x, D i (fieldLine F col x) ∂cornerLaw μ ν s i) :=
      mul_le_mul_of_nonneg_left hbase (div_nonneg hm.nonneg (by norm_num))
    _ = _ := by ring

end Sandpile
