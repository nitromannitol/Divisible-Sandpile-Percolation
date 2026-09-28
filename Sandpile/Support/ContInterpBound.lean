import Sandpile.Support.HeatPotentialDefs
import LatticeProb.Support.ContSums

/-!
# The interpolated field is a convex combination of its mesh values

`linInterp`, the frozen definition of `prop:dlt4-heat-potential-invariance`, writes the value at
a point `(r,w)` as a sum over the `2 ^ d` spatial corners of its cell, each weighted by a product
of fractional parts, of the two time values at `⌊R²r⌋` and `⌊R²r⌋ + 1` weighted by the fractional
part of `R²r`. `prod_ite_nonneg` and `fract_mem` record that all `2 ^ (d + 1)` of these weights
are nonnegative for `r ≥ 0`, and `abs_sum_weight_mul_le` is the elementary fact that a convex
combination is bounded by the largest term combined; `abs_linInterp_le` assembles them to show
the interpolated value never leaves the range of the mesh values it interpolates. This is the
first step of the tightness clause, reducing the uniform norm of `Z_R^{lin}` on a compact set to
the largest mesh value in a neighbourhood of it. `ContGreenFubini` already carries the same
weights under the names `cornerWeight`, `timeWeight` and `interpTermWeight`; what this file adds
is the consequence for the interpolated VALUE.
-/

open LatticeProb

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Frozen.HeatPotentialInvariance

/-- The multilinear weights of one cell are nonnegative. -/
theorem prod_ite_nonneg {d : ℕ} (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1)
    (ε : Fin d → Bool) : 0 ≤ ∏ i : Fin d, if ε i then t i else 1 - t i := by
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : ε i
  · rw [if_pos h]; exact ht i
  · rw [if_neg h]; linarith [ht1 i]

/-- A convex combination is bounded by the largest of the values combined. -/
theorem abs_sum_weight_mul_le {ι : Type*} [Fintype ι] (lam v : ι → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1) (M : ℝ) (hv : ∀ i, |v i| ≤ M) :
    |∑ i, lam i * v i| ≤ M := by
  calc |∑ i, lam i * v i|
      ≤ ∑ i, |lam i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, lam i * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hlam i)]
        exact mul_le_mul_of_nonneg_left (hv i) (hlam i)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The fractional part of a real number lies in the unit interval. -/
theorem fract_mem (x : ℝ) : 0 ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 1 :=
  ⟨by linarith [Int.floor_le x], by linarith [Int.lt_floor_add_one x]⟩

/-- **The interpolated field is bounded by the mesh values it interpolates.**  At
a nonnegative time the `2^{d+1}` multilinear weights are nonnegative and sum to
one, so the interpolation is a convex combination. -/
theorem abs_linInterp_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (w : Sandpile.Continuum.Space d) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M) :
    |linInterp d R ζ r w| ≤ M := by
  classical
  set a : ℕ := ⌊R ^ 2 * r⌋₊ with ha
  set s : ℝ := R ^ 2 * r - (a : ℝ) with hs
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set t : Fin d → ℝ := fun i => R * w i - (b i : ℝ) with ht
  have hrR : 0 ≤ R ^ 2 * r := mul_nonneg (sq_nonneg R) hr
  have hs0 : 0 ≤ s := by
    have hle := Nat.floor_le hrR
    rw [← ha] at hle
    rw [hs]
    linarith
  have hs1 : s ≤ 1 := by
    have hlt := Nat.lt_floor_add_one (R ^ 2 * r)
    rw [← ha] at hlt
    rw [hs]
    linarith
  have ht0 : ∀ i, 0 ≤ t i := fun i => (fract_mem (R * w i)).1
  have ht1 : ∀ i, t i ≤ 1 := fun i => (fract_mem (R * w i)).2
  have hval : ∀ ε : Fin d → Bool,
      |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0) +
        s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| ≤ M := by
    intro ε
    have h1 := hM a (fun i => b i + if ε i then 1 else 0)
    have h2 := hM (a + 1) (fun i => b i + if ε i then 1 else 0)
    calc |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0) +
          s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)|
        ≤ |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0)| +
            |s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| :=
          abs_add_le _ _
      _ = (1 - s) * |meshValue d R ζ a (fun i => b i + if ε i then 1 else 0)| +
            s * |meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s),
            abs_of_nonneg hs0]
      _ ≤ (1 - s) * M + s * M := by
          have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - s)
          have := mul_le_mul_of_nonneg_left h2 hs0
          linarith
      _ = M := by ring
  exact abs_sum_weight_mul_le _ _ (fun ε => prod_ite_nonneg t ht0 ht1 ε)
    (sum_prod_ite d t) M hval

end Sandpile.Support
