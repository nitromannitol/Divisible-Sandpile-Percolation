/-
Third derivatives along field lines, stable positive contractions,
and uniform coefficient overlap bounds.
-/
import LatticeProb.Analysis.SoftStability
import Mathlib.Analysis.Calculus.Taylor

open LatticeProb

open scoped BigOperators

noncomputable section

namespace Sandpile

variable {V : Type*} [Fintype V] [DecidableEq V]

def fieldLine (F A : V → ℝ) (x : ℝ) : V → ℝ := fun v => F v + A v * x

def directionalDerivative (f : (V → ℝ) → ℝ) (A : V → ℝ) (F : V → ℝ) : ℝ :=
  ∑ v, A v * coordPartial f v F

omit [DecidableEq V] in
lemma contDiff_fieldLine (F A : V → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fieldLine F A) := by
  apply contDiff_pi.mpr
  intro v
  exact contDiff_const.add (contDiff_const.mul contDiff_id)

omit [Fintype V] [DecidableEq V] in
lemma hasDerivAt_fieldLine (F A : V → ℝ) (x : ℝ) :
    HasDerivAt (fieldLine F A) A x := by
  apply hasDerivAt_pi.mpr
  intro v
  convert (hasDerivAt_const x (F v)).add ((hasDerivAt_id x).const_mul (A v)) using 1 <;>
    first | rfl | simp

lemma directionalDerivative_eq_fderiv (f : (V → ℝ) → ℝ) (F A : V → ℝ) :
    directionalDerivative f A F = fderiv ℝ f F A := by
  have hs : A = ∑ v, A v • Pi.single v (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, Pi.smul_apply]
  calc
    _ = fderiv ℝ f F (∑ v, A v • Pi.single v (1 : ℝ)) := by
      simp only [directionalDerivative, map_sum, map_smul, smul_eq_mul, coordPartial]
    _ = _ := congrArg (fderiv ℝ f F) hs.symm

lemma contDiff_directionalDerivative {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A : V → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (directionalDerivative f A) := by
  exact ContDiff.sum (fun v _ => contDiff_const.mul (contDiff_coordPartial hf v))

lemma hasDerivAt_comp_fieldLine {f : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (F A : V → ℝ) (x : ℝ) :
    HasDerivAt (fun u => f (fieldLine F A u)) (directionalDerivative f A (fieldLine F A x)) x := by
  have h := (hf (fieldLine F A x)).hasFDerivAt.comp_hasDerivAt x (hasDerivAt_fieldLine F A x)
  rw [← directionalDerivative_eq_fderiv] at h
  convert h using 1 <;> rfl

lemma deriv_comp_fieldLine {f : (V → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (F A : V → ℝ) :
    deriv (fun x => f (fieldLine F A x)) = fun x => directionalDerivative f A (fieldLine F A x) := by
  ext x
  exact (hasDerivAt_comp_fieldLine hf F A x).deriv

lemma coordPartial_directionalDerivative {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A : V → ℝ) (j : V) (F : V → ℝ) :
    coordPartial (directionalDerivative f A) j F =
      ∑ i, A i * coordPartial (coordPartial f i) j F := by
  unfold directionalDerivative
  rw [coordPartial_sum (fun i => (contDiff_const.mul (contDiff_coordPartial hf i)).differentiable (by simp))]
  simp only [coordPartial_const_mul _ ((contDiff_coordPartial hf _).differentiable (by simp))]

lemma directionalDerivative_three {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A F : V → ℝ) :
    directionalDerivative (directionalDerivative (directionalDerivative f A) A) A F =
      ∑ i, ∑ j, ∑ k, A i * A j * A k *
        coordPartial (coordPartial (coordPartial f i) j) k F := by
  have hdf := contDiff_directionalDerivative hf A
  have he (j k : V) :
      coordPartial (coordPartial (directionalDerivative f A) j) k F =
        ∑ i, A i * coordPartial (coordPartial (coordPartial f i) j) k F := by
    rw [show coordPartial (directionalDerivative f A) j =
      fun x => ∑ i, A i * coordPartial (coordPartial f i) j x from
        funext (coordPartial_directionalDerivative hf A j)]
    rw [coordPartial_sum (fun i => (contDiff_const.mul
      (contDiff_coordPartial (contDiff_coordPartial hf i) j)).differentiable (by simp))]
    simp only [coordPartial_const_mul _
      ((contDiff_coordPartial (contDiff_coordPartial hf _) _).differentiable (by simp))]
  change (∑ k, A k * coordPartial (directionalDerivative (directionalDerivative f A) A) k F) = _
  simp_rw [coordPartial_directionalDerivative hdf, he, Finset.mul_sum]
  calc
    _ = ∑ j, ∑ i, ∑ k, A k * (A j * (A i *
        coordPartial (coordPartial (coordPartial f i) j) k F)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

lemma iteratedDeriv_three_comp_fieldLine {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (F A : V → ℝ) (x : ℝ) :
    iteratedDeriv 3 (fun u => f (fieldLine F A u)) x =
      ∑ i, ∑ j, ∑ k, A i * A j * A k *
        coordPartial (coordPartial (coordPartial f i) j) k (fieldLine F A x) := by
  have hdf := contDiff_directionalDerivative hf A
  have hddf := contDiff_directionalDerivative hdf A
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_comp_fieldLine (hf.differentiable (by simp)),
    deriv_comp_fieldLine (hdf.differentiable (by simp)),
    deriv_comp_fieldLine (hddf.differentiable (by simp))]
  exact directionalDerivative_three hf A (fieldLine F A x)

def thirdContraction (J : V → V → V → (V → ℝ) → ℝ)
    (A F : V → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, |A i * A j * A k| * J i j k F

omit [DecidableEq V] in
lemma continuous_thirdContraction {J : V → V → V → (V → ℝ) → ℝ}
    (hJ : ∀ i j k, Continuous (J i j k)) (A : V → ℝ) :
    Continuous (thirdContraction J A) := by
  unfold thirdContraction
  fun_prop

omit [DecidableEq V] in
lemma expStable_thirdContraction {K : ℝ} {J : V → V → V → (V → ℝ) → ℝ}
    (hJ : ∀ i j k, ExpStable K (J i j k)) (A : V → ℝ) :
    ExpStable K (thirdContraction J A) := by
  exact ExpStable.sum (fun i => ExpStable.sum (fun j => ExpStable.sum (fun k =>
    (hJ i j k).const_mul (abs_nonneg _))))

lemma abs_iteratedDeriv_three_le_contraction {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {J : V → V → V → (V → ℝ) → ℝ}
    (hJ : ∀ i j k F, |coordPartial (coordPartial (coordPartial f i) j) k F| ≤ J i j k F)
    (F A : V → ℝ) (x : ℝ) :
    |iteratedDeriv 3 (fun u => f (fieldLine F A u)) x| ≤ thirdContraction J A (fieldLine F A x) := by
  rw [iteratedDeriv_three_comp_fieldLine hf]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hJ i j k _) (abs_nonneg _)

lemma abs_iteratedDeriv_three_le_stable {f : (V → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : ℝ} {J : V → V → V → (V → ℝ) → ℝ}
    (hJ : ∀ i j k, ExpStable K (J i j k))
    (hbound : ∀ i j k F, |coordPartial (coordPartial (coordPartial f i) j) k F| ≤ J i j k F)
    (F A : V → ℝ) {a : ℝ} (ha : 0 ≤ a) (hA : ∀ v, |A v| ≤ a) (x : ℝ) :
    |iteratedDeriv 3 (fun u => f (fieldLine F A u)) x| ≤
      thirdContraction J A F * Real.exp ((K * a) * |x|) := by
  have hs := (expStable_thirdContraction hJ A).2 (fieldLine F A x) F (a * |x|)
    (mul_nonneg ha (abs_nonneg x)) (fun v => by
      simp only [fieldLine, add_sub_cancel_left, abs_mul]
      exact mul_le_mul_of_nonneg_right (hA v) (abs_nonneg x))
  have h := (abs_iteratedDeriv_three_le_contraction hf hbound F A x).trans hs
  exact h.trans_eq (by rw [← mul_assoc]; ring)

lemma triple_product_le_cubes {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * (a * b * c) ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  have hs : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h := mul_nonneg (add_nonneg (add_nonneg ha hb) hc) hs
  nlinarith

omit [Fintype V] [DecidableEq V] in
lemma sum_abs_triple_le_cube_bound {I : Type*} [Fintype I]
    (A : V → I → ℝ) {Q : ℝ} (hQ : ∀ v, ∑ i, |A v i| ^ 3 ≤ Q) (v w z : V) :
    ∑ i, |A v i * A w i * A z i| ≤ Q := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    triple_product_le_cubes (abs_nonneg (A v i)) (abs_nonneg (A w i)) (abs_nonneg (A z i)))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← abs_mul] at h
  linarith [hQ v, hQ w, hQ z]

omit [DecidableEq V] in
lemma sum_thirdContraction_le {I : Type*} [Fintype I]
    {J : V → V → V → (V → ℝ) → ℝ} (hJ : ∀ i j k F, 0 ≤ J i j k F)
    (A : V → I → ℝ) {B Q : ℝ} (hQ : 0 ≤ Q)
    (hoverlap : ∀ v w z, ∑ i, |A v i * A w i * A z i| ≤ Q)
    (hB : ∀ F, ∑ v, ∑ w, ∑ z, J v w z F ≤ B) (F : V → ℝ) :
    ∑ i, thirdContraction J (fun v => A v i) F ≤ B * Q := by
  have he : (∑ i, thirdContraction J (fun v => A v i) F) =
      ∑ v, ∑ w, ∑ z, (∑ i, |A v i * A w i * A z i|) * J v w z F := by
    unfold thirdContraction
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [he]
  calc
    _ ≤ ∑ v, ∑ w, ∑ z, Q * J v w z F := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sum_le_sum
      intro w _
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right (hoverlap v w z) (hJ v w z F)
    _ = Q * (∑ v, ∑ w, ∑ z, J v w z F) := by simp only [Finset.mul_sum]
    _ ≤ B * Q := by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB F) hQ

end Sandpile
