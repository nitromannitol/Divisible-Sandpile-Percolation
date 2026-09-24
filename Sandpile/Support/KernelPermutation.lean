/-
Coordinate-permutation covariance of killed kernels and invariance of the radial cutoff Green kernel.
-/
import Sandpile.Support.FiniteKernel

open scoped BigOperators
noncomputable section
namespace Sandpile

def permuteSite {d : ℕ} (e : Fin d ≃ Fin d) : Site d ≃+ Site d where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := rfl

lemma permuteSite_unit {d : ℕ} (e : Fin d ≃ Fin d) (i : Fin d) :
    permuteSite e (unit i) = unit (e.symm i) := by
  ext j
  change (unit i) (e j) = (unit (e.symm i)) j
  by_cases hj : j = e.symm i
  · subst j; simp [unit]
  · have hh : e j ≠ i := fun he => hj (e.injective (by simpa using he))
    simp [unit, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hh]

lemma killedKernel_permute {d : ℕ} (e : Fin d ≃ Fin d) (D : Set (Site d)) :
    ∀ (n : ℕ) (x y : Site d), killedKernel ((permuteSite e) ⁻¹' D) n x y =
      killedKernel D n (permuteSite e x) (permuteSite e y) := by
  intro n
  induction n with
  | zero =>
    intro x y
    simp only [killedKernel]
    by_cases hx : permuteSite e x ∈ D
    · rw [Set.indicator_of_mem (show x ∈ (permuteSite e) ⁻¹' D from hx), Set.indicator_of_mem hx]
      simp only [(permuteSite e).injective.eq_iff]
    · rw [Set.indicator_of_notMem (show x ∉ (permuteSite e) ⁻¹' D from hx), Set.indicator_of_notMem hx]
  | succ n ih =>
    intro x y
    simp only [killedKernel]
    by_cases hx : permuteSite e x ∈ D
    · rw [Set.indicator_of_mem (show x ∈ (permuteSite e) ⁻¹' D from hx), Set.indicator_of_mem hx]
      simp only [ih, map_add, map_sub, permuteSite_unit]
      congr 1
      exact e.symm.sum_comp (fun i => killedKernel D n (permuteSite e x + unit i) (permuteSite e y) +
        killedKernel D n (permuteSite e x - unit i) (permuteSite e y))
    · rw [Set.indicator_of_notMem (show x ∉ (permuteSite e) ⁻¹' D from hx), Set.indicator_of_notMem hx]

lemma killedGreen_permute {d : ℕ} (e : Fin d ≃ Fin d) (D : Set (Site d)) (x y : Site d) :
    killedGreen ((permuteSite e) ⁻¹' D) x y = killedGreen D (permuteSite e x) (permuteSite e y) := by
  exact tsum_congr (fun n => killedKernel_permute e D n x y)

lemma ball_preimage_permute (e : Fin 4 ≃ Fin 4) (r : ℕ) :
    (permuteSite e) ⁻¹' External.BallGreen.box r = External.BallGreen.box r := by
  ext x
  change (∀ i, (x (e i)).natAbs ≤ r) ↔ ∀ i, (x i).natAbs ≤ r
  constructor
  · intro h i
    simpa using h (e.symm i)
  · intro h i
    exact h (e i)

lemma latticeNorm_permute (e : Fin 4 ≃ Fin 4) (x : Site 4) :
    External.BallGreen.latticeNorm (permuteSite e x) = External.BallGreen.latticeNorm x := by
  unfold External.BallGreen.latticeNorm
  congr 1
  exact e.sum_comp (fun i => ((x i : ℤ) : ℝ) ^ 2)

lemma cutField_permute (e : Fin 4 ≃ Fin 4) (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) :
    External.BallGreen.cutField r L φ (permuteSite e x) = External.BallGreen.cutField r L φ x := by
  unfold External.BallGreen.cutField
  rw [latticeNorm_permute]
  congr 1
  have hh := killedGreen_permute e (External.BallGreen.box r) 0 x
  simpa only [ball_preimage_permute, map_zero] using hh.symm

end Sandpile
