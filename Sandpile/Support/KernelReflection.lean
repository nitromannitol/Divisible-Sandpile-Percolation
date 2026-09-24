/-
Coordinate-reflection covariance of killed kernels and invariance of the cutoff Green kernel.
-/
import Sandpile.Support.KernelPermutation

open scoped BigOperators
noncomputable section
namespace Sandpile

def reflectSite {d : ℕ} (i : Fin d) : Site d ≃+ Site d where
  toFun x j := if j = i then -x j else x j
  invFun x j := if j = i then -x j else x j
  left_inv x := by ext j; by_cases hj : j = i <;> simp [hj]
  right_inv x := by ext j; by_cases hj : j = i <;> simp [hj]
  map_add' x y := by ext j; by_cases hj : j = i <;> simp [hj, add_comm]

lemma reflectSite_unit {d : ℕ} (i j : Fin d) :
    reflectSite i (unit j) = if j = i then -unit j else unit j := by
  ext k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i <;> simp [reflectSite, unit, hk]
  · by_cases hk : k = i <;> by_cases hkj : k = j <;> simp_all [reflectSite, unit]

lemma killedKernel_reflect {d : ℕ} (i : Fin d) (D : Set (Site d)) :
    ∀ (n : ℕ) (x y : Site d), killedKernel ((reflectSite i) ⁻¹' D) n x y =
      killedKernel D n (reflectSite i x) (reflectSite i y) := by
  intro n
  induction n with
  | zero =>
    intro x y
    simp only [killedKernel]
    by_cases hx : reflectSite i x ∈ D
    · rw [Set.indicator_of_mem (show x ∈ (reflectSite i) ⁻¹' D from hx), Set.indicator_of_mem hx]
      simp only [(reflectSite i).injective.eq_iff]
    · rw [Set.indicator_of_notMem (show x ∉ (reflectSite i) ⁻¹' D from hx), Set.indicator_of_notMem hx]
  | succ n ih =>
    intro x y
    simp only [killedKernel]
    by_cases hx : reflectSite i x ∈ D
    · rw [Set.indicator_of_mem (show x ∈ (reflectSite i) ⁻¹' D from hx), Set.indicator_of_mem hx]
      simp only [ih, map_add, map_sub, reflectSite_unit]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i <;> simp [hj, add_comm, sub_eq_add_neg]
    · rw [Set.indicator_of_notMem (show x ∉ (reflectSite i) ⁻¹' D from hx), Set.indicator_of_notMem hx]

lemma killedGreen_reflect {d : ℕ} (i : Fin d) (D : Set (Site d)) (x y : Site d) :
    killedGreen ((reflectSite i) ⁻¹' D) x y = killedGreen D (reflectSite i x) (reflectSite i y) := by
  exact tsum_congr (fun n => killedKernel_reflect i D n x y)

lemma ball_preimage_reflect (i : Fin 4) (r : ℕ) :
    (reflectSite i) ⁻¹' External.BallGreen.box r = External.BallGreen.box r := by
  ext x
  change (∀ j, (if j = i then -x j else x j).natAbs ≤ r) ↔ ∀ j, (x j).natAbs ≤ r
  have he (j : Fin 4) : (if j = i then -x j else x j).natAbs = (x j).natAbs := by
    split_ifs <;> simp
  simp only [he]

lemma latticeNorm_reflect (i : Fin 4) (x : Site 4) :
    External.BallGreen.latticeNorm (reflectSite i x) = External.BallGreen.latticeNorm x := by
  unfold External.BallGreen.latticeNorm
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (((if j = i then -x j else x j) : ℤ) : ℝ) ^ 2 = ((x j : ℤ) : ℝ) ^ 2
  split_ifs <;> simp

lemma cutField_reflect (i : Fin 4) (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) :
    External.BallGreen.cutField r L φ (reflectSite i x) = External.BallGreen.cutField r L φ x := by
  unfold External.BallGreen.cutField
  rw [latticeNorm_reflect]
  congr 1
  have hh := killedGreen_reflect i (External.BallGreen.box r) 0 x
  simpa only [ball_preimage_reflect, map_zero] using hh.symm

end Sandpile
