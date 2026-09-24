/-
Coordinate comparisons under mixed finite product laws, with every
envelope summed under the same product measure.
-/
import Sandpile.Support.FiniteProductSplit
import Sandpile.Support.BernoulliInterpolation

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Sandpile

variable {I α : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace α]

def cornerLaw (μ ν : Measure α) (s : I → Bool) (i : I) : Measure α :=
  if s i then ν else μ

instance isProbabilityMeasure_cornerLaw (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : I → Bool) (i : I) :
    IsProbabilityMeasure (cornerLaw μ ν s i) := by
  unfold cornerLaw
  cases s i <;> infer_instance

def cornerExpectation (μ ν : Measure α) (f : (I → α) → ℝ) (s : I → Bool) : ℝ :=
  ∫ x, f x ∂Measure.pi (cornerLaw μ ν s)

omit [Fintype I] in
@[simp] lemma cornerLaw_update_self (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool) :
    cornerLaw μ ν (Function.update s i b) i = if b then ν else μ := by
  simp [cornerLaw]

omit [Fintype I] in
@[simp] lemma cornerLaw_update_other (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool)
    (j : {j : I // j ≠ i}) : cornerLaw μ ν (Function.update s i b) j = cornerLaw μ ν s j := by
  simp [cornerLaw, j.property]

omit [Fintype I] in
lemma cornerLaw_update_rest (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool) :
    (fun j : {j : I // j ≠ i} => cornerLaw μ ν (Function.update s i b) j) =
      fun j : {j : I // j ≠ i} => cornerLaw μ ν s j := by
  funext j
  exact cornerLaw_update_other μ ν s i b j

variable (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma cornerExpectation_split {f : (I → α) → ℝ} (s : I → Bool) (i : I)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν s))) :
    cornerExpectation μ ν f s =
      ∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂cornerLaw μ ν s i
        ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) :=
  integral_pi_splitAt _ i hf

lemma cornerExpectation_update {f : (I → α) → ℝ} (s : I → Bool) (i : I) (b : Bool)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i b)))) :
    cornerExpectation μ ν f (Function.update s i b) =
      ∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂(if b then ν else μ)
        ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) := by
  rw [cornerExpectation_split μ ν _ i hf, cornerLaw_update_self, cornerLaw_update_rest]

lemma integrable_corner_split {f : (I → α) → ℝ} (s : I → Bool) (i : I)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν s))) :
    Integrable (fun p => f ((measurableFunSplitAt i).symm p))
      ((cornerLaw μ ν s i).prod
        (Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j))) := by
  exact ((measurePreserving_funSplitAt (cornerLaw μ ν s) i).symm.integrable_comp_emb
    (measurableFunSplitAt i).symm.measurableEmbedding).mpr hf

lemma integrable_corner_split_update {f : (I → α) → ℝ} (s : I → Bool) (i : I) (b : Bool)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i b)))) :
    Integrable (fun p => f ((measurableFunSplitAt i).symm p))
      ((if b then ν else μ).prod
        (Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j))) := by
  have h := integrable_corner_split μ ν (Function.update s i b) i hf
  rwa [cornerLaw_update_self, cornerLaw_update_rest] at h

lemma abs_cornerExpectation_difference_le {f E : (I → α) → ℝ} (s : I → Bool) (i : I)
    (hνf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i true))))
    (hμf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i false))))
    (hE : Integrable E (Measure.pi (cornerLaw μ ν s))) {C : ℝ}
    (hlocal : ∀ r : {j : I // j ≠ i} → α,
      |(∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂ν) -
        (∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂μ)| ≤
      C * ∫ a, E ((measurableFunSplitAt i).symm (a, r)) ∂cornerLaw μ ν s i) :
    |cornerExpectation μ ν f (Function.update s i true) -
      cornerExpectation μ ν f (Function.update s i false)| ≤ C * cornerExpectation μ ν E s := by
  have hν := (integrable_corner_split_update μ ν s i true hνf).integral_prod_right
  have hμ := (integrable_corner_split_update μ ν s i false hμf).integral_prod_right
  simp only [Bool.false_eq_true, reduceIte] at hν hμ
  have hEi := (integrable_corner_split μ ν s i hE).integral_prod_right
  rw [cornerExpectation_update μ ν s i true hνf,
    cornerExpectation_update μ ν s i false hμf, cornerExpectation_split μ ν s i hE]
  change |(∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂ν
      ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j)) -
    (∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂μ
      ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j))| ≤ _
  rw [← integral_sub hν hμ]
  calc
    _ ≤ ∫ r, |(∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂ν) -
        (∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂μ)|
      ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) := abs_integral_le_integral_abs
    _ ≤ ∫ r, C * ∫ a, E ((measurableFunSplitAt i).symm (a, r)) ∂cornerLaw μ ν s i
      ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) :=
      integral_mono (hν.sub hμ).abs (hEi.const_mul C) hlocal
    _ = _ := integral_const_mul _ _

omit [DecidableEq I] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
lemma cornerExpectation_sum (E : I → (I → α) → ℝ) (s : I → Bool)
    (hE : ∀ i, Integrable (E i) (Measure.pi (cornerLaw μ ν s))) :
    cornerExpectation μ ν (fun x => ∑ i, E i x) s = ∑ i, cornerExpectation μ ν (E i) s := by
  exact integral_finsetSum _ (fun i _ => hE i)

lemma corner_expectation_replacement_bound {f : (I → α) → ℝ} (E : I → (I → α) → ℝ)
    (hf : ∀ s, Integrable f (Measure.pi (cornerLaw μ ν s)))
    (hE : ∀ s i, Integrable (E i) (Measure.pi (cornerLaw μ ν s)))
    {C B : ℝ} (hC : 0 ≤ C) (hB : ∀ x, ∑ i, E i x ≤ B)
    (hlocal : ∀ (s : I → Bool) (i : I) (r : {j : I // j ≠ i} → α),
      |(∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂ν) -
        (∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂μ)| ≤
      C * ∫ a, E i ((measurableFunSplitAt i).symm (a, r)) ∂cornerLaw μ ν s i) :
    |(∫ x, f x ∂Measure.pi (fun _ : I => ν)) -
      (∫ x, f x ∂Measure.pi (fun _ : I => μ))| ≤ C * B := by
  have h := corner_replacement_bound_pointwise (cornerExpectation μ ν f) (C * B) (fun s => by
    calc
      _ ≤ ∑ i, C * cornerExpectation μ ν (E i) s := Finset.sum_le_sum (fun i _ =>
        abs_cornerExpectation_difference_le μ ν s i (hf _) (hf _) (hE s i) (hlocal s i))
      _ = C * cornerExpectation μ ν (fun x => ∑ i, E i x) s := by
        rw [← Finset.mul_sum, ← cornerExpectation_sum μ ν E s (hE s)]
      _ ≤ C * B := by
        apply mul_le_mul_of_nonneg_left _ hC
        calc
          _ ≤ ∫ _ : I → α, B ∂Measure.pi (cornerLaw μ ν s) :=
            integral_mono (integrable_finsetSum _ (fun i _ => hE s i)) (integrable_const B) hB
          _ = B := by simp)
  have htrue : cornerLaw μ ν (fun _ : I => true) = fun _ : I => ν := by
    funext i
    rfl
  have hfalse : cornerLaw μ ν (fun _ : I => false) = fun _ : I => μ := by
    funext i
    rfl
  dsimp only [cornerExpectation] at h
  rw [htrue, hfalse] at h
  exact h

end Sandpile
