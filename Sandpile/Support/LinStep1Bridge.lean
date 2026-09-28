import Sandpile.Support.LinStep1Factor
import Sandpile.Support.LinThresholdNull
import Sandpile.Support.LinFactor

/-! # Step 1 Bridge

The two branches of Step 1 of `lem:dgt4-path-survival` in the shape Step 2 consumes.

`Support/LinStep2Replace.lean` asks for the factorization along the last-visit sites of a path
as an explicit hypothesis, because the paper proves it separately in the two cases of
`sandpile.tex:5454-5455`.  Here each case is supplied.

* In the independent branch `J=-G(0,0)\zeta` the factorization is an identity, not an estimate
  (`indep_path_factorization`): the paper's "When the $J(x)$ are independent, the left-hand side
  of \eqref{eq:dgt4-path-threshold-factorization} is zero".  The proof reads the family
  `xs : Fin m → \Z^d` as the Finset of its values, which is what
  `Sandpile.centeredMassLaw_threshold_factorization` is stated over; the level at a value is
  recovered from the index by `Function.invFun`, which is a left inverse because `xs` is
  injective.
* In the Gaussian branch `J=-V_\infty` the factorization is
  `Sandpile.eventually_gauss_path_factorization` (`Support/LinStep1Factor.lean`), whose two-sided
  tail hypotheses are stated for the law of `J(0)` itself.  `measureReal_threshold_gt_gauss`
  identifies `\P(J(0)>c)` with the upper Gaussian tail at `c` of the law of variance
  `\Var(\zeta(0))\sum_zG(0,z)^2`; the threshold event is only NULL measurable, so the
  complement is taken with `measure_compl₀` and the null measurability of
  `Support/LinThresholdNull.lean`.  `eventually_gauss_path_factorization_of_field` is then the
  factorization written through `J`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The independent branch -/

/-- **Step 1 in the independent branch**: the factorization is exact. -/
theorem indep_path_factorization (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -(green d 0 0 * scenery d σ x))
    (m : ℕ) (xs : Fin m → Site d) (hxs : Function.Injective xs) (c : Fin m → ℝ) :
    (centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ c i}
      = ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ c i} := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  have hne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set b : Site d → ℝ := fun x => c (Function.invFun xs x) with hb
  have hbxs : ∀ i : Fin m, b (xs i) = c i := by
    intro i
    rw [hb]
    simp only
    rw [Function.leftInverse_invFun hxs i]
  have hset : {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ c i}
      = {σ : Site d → ℝ | ∀ x ∈ Finset.image xs Finset.univ, J σ x ≤ b x} := by
    ext σ
    simp only [Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro h x ⟨i, rfl⟩
      rw [hbxs i]
      exact h i
    · intro h i
      have := h (xs i) ⟨i, rfl⟩
      rwa [hbxs i] at this
  have hprod : ∏ x ∈ Finset.image xs Finset.univ,
      (centeredMassLaw d ν) {σ : Site d → ℝ | J σ 0 ≤ b x}
      = ∏ i : Fin m, (centeredMassLaw d ν) {σ : Site d → ℝ | J σ 0 ≤ c i} := by
    rw [Finset.prod_image (fun i _ j _ h => hxs h)]
    exact Finset.prod_congr rfl fun i _ => by rw [hbxs i]
  rw [measureReal_def, hset,
    centeredMassLaw_threshold_factorization ν J hJ (Finset.image xs Finset.univ) b, hprod,
    ENNReal.toReal_prod]
  rfl

/-! ### The one-site tail of the Gaussian branch -/

/-- **The one-site threshold tail of the Gaussian branch.**  `P(J(0) > c)` is the upper
Gaussian tail at `c` of the law of `J(0)`, whose variance is `Var(ζ(0))∑_zG(0,z)^2`. -/
theorem measureReal_threshold_gt_gauss (hd : 5 ≤ d) (v : ℝ≥0) (c : ℝ) :
    (centeredMassLaw d (gaussianReal 0 v)).real
        {σ : Site d → ℝ | c < -infiniteGreenField (scenery d σ) 0}
      = (gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real (Set.Ioi c) := by
  have hcompl : {σ : Site d → ℝ | c < -infiniteGreenField (scenery d σ) 0}
      = {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ c}ᶜ := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hIoi : (Set.Ioi c) = (Set.Iic c)ᶜ := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_compl_iff, Set.mem_Iic, not_le]
  have hnull : NullMeasurableSet {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ c}
      (centeredMassLaw d (gaussianReal 0 v)) :=
    nullMeasurableSet_le (aemeasurable_infiniteGreenField_mass hd v 0).neg aemeasurable_const
  have h1 : (centeredMassLaw d (gaussianReal 0 v))
      {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ c}ᶜ
      = 1 - (centeredMassLaw d (gaussianReal 0 v))
        {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ c} := by
    rw [measure_compl₀ hnull (measure_ne_top _ _), measure_univ]
  have h2 : (gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)) (Set.Iic c)ᶜ
      = 1 - (gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)) (Set.Iic c) := by
    rw [measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
  rw [hcompl, hIoi, measureReal_def, measureReal_def, h1, h2,
    measure_threshold_single hd v 0 c]

/-! ### The Gaussian branch -/

/-- **Step 1 in the shape Step 2 consumes**: the factorization along the last-visit sites of a
path, with the levels read through the field `J` of `sandpile.tex:5449-5450`. -/
theorem eventually_gauss_path_factorization_of_field
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)
    (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop, ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs →
      (m : ℝ) ≤ A * R ^ 2 →
      ∀ c : Fin m → ℝ,
        (∀ i, Real.sqrt ((v : ℝ) * greenSqSum d) ≤ c i) →
        (∀ i, (centeredMassLaw d (gaussianReal 0 v)).real
            {σ : Site d → ℝ | c i < J σ 0} ≤ K / R ^ 2) →
        (∀ i, 1 / (K * R ^ 2) ≤ (centeredMassLaw d (gaussianReal 0 v)).real
            {σ : Site d → ℝ | c i < J σ 0}) →
        |(centeredMassLaw d (gaussianReal 0 v)).real
              {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ c i}
            - ∏ i : Fin m, (centeredMassLaw d (gaussianReal 0 v)).real
              {σ : Site d → ℝ | J σ 0 ≤ c i}| ≤ theta := by
  filter_upwards [eventually_gauss_path_factorization hNormal hd v hv A K hA hK htheta] with
    R hR
  intro m xs hxs hm c hc hup hlow
  have hev : ∀ i : Fin m, {σ : Site d → ℝ | c i < J σ 0}
      = {σ : Site d → ℝ | c i < -infiniteGreenField (scenery d σ) 0} := by
    intro i
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  have hup' : ∀ i, ((gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real
      (Set.Ioi (c i))) ≤ K / R ^ 2 := by
    intro i
    rw [← measureReal_threshold_gt_gauss hd v (c i), ← hev i]
    exact hup i
  have hlow' : ∀ i, 1 / (K * R ^ 2) ≤ ((gaussianReal 0 (((v : ℝ) * greenSqSum d).toNNReal)).real
      (Set.Ioi (c i))) := by
    intro i
    rw [← measureReal_threshold_gt_gauss hd v (c i), ← hev i]
    exact hlow i
  have hmain := hR m xs hxs hm c hc hup' hlow'
  have hset : {σ : Site d → ℝ | ∀ i : Fin m, J σ (xs i) ≤ c i}
      = {σ : Site d → ℝ | ∀ i : Fin m, -infiniteGreenField (scenery d σ) (xs i) ≤ c i} := by
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  have hset0 : ∀ i : Fin m, {σ : Site d → ℝ | J σ 0 ≤ c i}
      = {σ : Site d → ℝ | -infiniteGreenField (scenery d σ) 0 ≤ c i} := by
    intro i
    ext σ
    simp only [Set.mem_setOf_eq, hJ]
  rw [hset]
  simp only [hset0]
  simpa only [measureReal_def] using hmain

end Sandpile
