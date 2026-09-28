import Sandpile.Support.FiniteProductSplit
import Sandpile.Support.BernoulliInterpolation

/-!
# Corner expectations under mixed finite product measures

For probability measures `μ` and `ν` on `α` and a Boolean corner `s : I → Bool`, `cornerLaw μ ν s
i` is `ν` where `s i` is `true` and `μ` otherwise, and `cornerExpectation μ ν f s` is the
expectation of `f` under the mixed product measure `Measure.pi (cornerLaw μ ν s)`. This module
bounds the coordinatewise finite differences of `cornerExpectation μ ν f` by envelopes `E i`
(`abs_cornerExpectation_difference_le`), by splitting the product integral at one coordinate
(`Sandpile.Support.FiniteProductSplit`), and feeds the result into the Bernoulli-interpolation
replacement bound of `Sandpile.Support.BernoulliInterpolation`
(`corner_expectation_replacement_bound`) to compare the expectations of `f` under the constant
product measures `ν^I` and `μ^I`, with every envelope summed under the same product measure.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Sandpile

variable {I α : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace α]

/-- The measure `cornerLaw μ ν s` uses at coordinate `i`: `ν` when `s i` is `true`, `μ`
otherwise. `Measure.pi (cornerLaw μ ν s)` interpolates coordinatewise between the constant
product measures `Measure.pi (fun _ => μ)` and `Measure.pi (fun _ => ν)`. -/
def cornerLaw (μ ν : Measure α) (s : I → Bool) (i : I) : Measure α :=
  if s i then ν else μ

/-- `cornerLaw μ ν s i` is a probability measure whenever `μ` and `ν` both are, since it is
defined to equal one or the other. -/
instance isProbabilityMeasure_cornerLaw (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (s : I → Bool) (i : I) :
    IsProbabilityMeasure (cornerLaw μ ν s i) := by
  unfold cornerLaw
  cases s i <;> infer_instance

/-- The expectation of `f` under the mixed product measure `Measure.pi (cornerLaw μ ν s)`: the
function `corner_replacement_bound_pointwise` is applied to below, to compare its value at the
all-`true` and all-`false` corners. -/
def cornerExpectation (μ ν : Measure α) (f : (I → α) → ℝ) (s : I → Bool) : ℝ :=
  ∫ x, f x ∂Measure.pi (cornerLaw μ ν s)

omit [Fintype I] in
/-- Updating `s` at `i` to `b` sets `cornerLaw μ ν s i` to `ν` or `μ` according to `b`. -/
@[simp] lemma cornerLaw_update_self (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool) :
    cornerLaw μ ν (Function.update s i b) i = if b then ν else μ := by
  simp [cornerLaw]

omit [Fintype I] in
/-- Updating `s` at `i` leaves `cornerLaw μ ν s j` unchanged at any coordinate `j ≠ i`. -/
@[simp] lemma cornerLaw_update_other (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool)
    (j : {j : I // j ≠ i}) : cornerLaw μ ν (Function.update s i b) j = cornerLaw μ ν s j := by
  simp [cornerLaw, j.property]

omit [Fintype I] in
/-- The family `cornerLaw μ ν s` restricted to the coordinates other than `i`, as a function, is
unchanged by updating `s` at `i` (`cornerLaw_update_other` applied pointwise). -/
lemma cornerLaw_update_rest (μ ν : Measure α) (s : I → Bool) (i : I) (b : Bool) :
    (fun j : {j : I // j ≠ i} => cornerLaw μ ν (Function.update s i b) j) =
      fun j : {j : I // j ≠ i} => cornerLaw μ ν s j := by
  funext j
  exact cornerLaw_update_other μ ν s i b j

variable (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Splits `cornerExpectation μ ν f s` as an iterated integral over coordinate `i` and the
remaining coordinates, by `integral_pi_splitAt` applied to the product law `cornerLaw μ ν s`. -/
lemma cornerExpectation_split {f : (I → α) → ℝ} (s : I → Bool) (i : I)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν s))) :
    cornerExpectation μ ν f s =
      ∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂cornerLaw μ ν s i
        ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) :=
  integral_pi_splitAt _ i hf

/-- The same splitting for the corner `Function.update s i b`: after rewriting by
`cornerLaw_update_self` and `cornerLaw_update_rest`, the `i`-th integral is against `ν` or `μ`
according to `b`, while the remaining coordinates keep the law of `s`. -/
lemma cornerExpectation_update {f : (I → α) → ℝ} (s : I → Bool) (i : I) (b : Bool)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i b)))) :
    cornerExpectation μ ν f (Function.update s i b) =
      ∫ r, ∫ a, f ((measurableFunSplitAt i).symm (a, r)) ∂(if b then ν else μ)
        ∂Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j) := by
  rw [cornerExpectation_split μ ν _ i hf, cornerLaw_update_self, cornerLaw_update_rest]

/-- Integrability of `f` under `Measure.pi (cornerLaw μ ν s)` transfers, along the
measure-preserving splitting `measurableFunSplitAt i`, to integrability of the transported
function under the product of `cornerLaw μ ν s i` with the law of the remaining coordinates. -/
lemma integrable_corner_split {f : (I → α) → ℝ} (s : I → Bool) (i : I)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν s))) :
    Integrable (fun p => f ((measurableFunSplitAt i).symm p))
      ((cornerLaw μ ν s i).prod
        (Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j))) := by
  exact ((measurePreserving_funSplitAt (cornerLaw μ ν s) i).symm.integrable_comp_emb
    (measurableFunSplitAt i).symm.measurableEmbedding).mpr hf

/-- The same transfer as `integrable_corner_split` for the corner `Function.update s i b`, with
the `i`-th factor rewritten to `if b then ν else μ` via `cornerLaw_update_self` and
`cornerLaw_update_rest`. -/
lemma integrable_corner_split_update {f : (I → α) → ℝ} (s : I → Bool) (i : I) (b : Bool)
    (hf : Integrable f (Measure.pi (cornerLaw μ ν (Function.update s i b)))) :
    Integrable (fun p => f ((measurableFunSplitAt i).symm p))
      ((if b then ν else μ).prod
        (Measure.pi (fun j : {j : I // j ≠ i} => cornerLaw μ ν s j))) := by
  have h := integrable_corner_split μ ν (Function.update s i b) i hf
  rwa [cornerLaw_update_self, cornerLaw_update_rest] at h

/-- The coordinatewise finite difference of `cornerExpectation μ ν f` at coordinate `i` is
bounded by `C` times `cornerExpectation μ ν E s`, given a bound `hlocal` on the difference of the
`i`-th integrals against `ν` and `μ` at every fixed configuration of the remaining coordinates.
Obtained by splitting the integral at `i` (`cornerExpectation_split`, `cornerExpectation_update`)
and applying `integral_mono` to the resulting integrands. -/
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
/-- `cornerExpectation μ ν` is additive in a finite sum of integrands, by linearity of the
integral (`integral_finsetSum`). -/
lemma cornerExpectation_sum (E : I → (I → α) → ℝ) (s : I → Bool)
    (hE : ∀ i, Integrable (E i) (Measure.pi (cornerLaw μ ν s))) :
    cornerExpectation μ ν (fun x => ∑ i, E i x) s = ∑ i, cornerExpectation μ ν (E i) s := by
  exact integral_finsetSum _ (fun i _ => hE i)

/-- `corner_replacement_bound_pointwise` specialized to `F = cornerExpectation μ ν f`: given a
local bound `hlocal` on the effect at each coordinate `i` of swapping that coordinate from `μ`
to `ν`, controlled by envelopes `E i` whose pointwise sum is at most `B`, the total difference
between the expectations of `f` under the constant product measures `ν^I` and `μ^I` is at most
`C * B`. -/
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
