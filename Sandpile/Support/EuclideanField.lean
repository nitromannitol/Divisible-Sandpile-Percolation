import Sandpile.Support.CrossingContinuity
import Sandpile.Support.NearKernel

/-! # Lipschitz Bounds for Euclidean Linear Fields of Cutoff Green Functions

Lipschitz estimates, in the Euclidean structure on a finite-dimensional coefficient space,
for `crossingValue` applied to a `linearField` built from translates of the truncated Green
function `External.BallGreen.cutField`. The chain runs from the elementary Cauchy-Schwarz
bound `abs_euclidean_linear_le` through the Lipschitz constant of `linearField` and its
composition with `crossingValue`, to the quantitative bound `cutField_square_sum_bound` on the
sum of squares of the cutoff field, which supplies the Lipschitz constant
`sqrt(G log r)` used in `exists_far_rectangle_euclidean_lipschitz`.
-/

open scoped BigOperators NNReal

noncomputable section
namespace Sandpile

/-- A Cauchy-Schwarz bound for a linear functional with coefficients of bounded square sum: if
`∑ i, a i ^ 2 ≤ D ^ 2` then `|∑ i, a i * x i| ≤ D * ‖x‖` in `EuclideanSpace ℝ I`. -/
lemma abs_euclidean_linear_le {I : Type*} [Fintype I] (a : I → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (ha : (∑ i, a i ^ 2) ≤ D ^ 2) (x : EuclideanSpace ℝ I) :
    |∑ i, a i * x.ofLp i| ≤ D * ‖x‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD (norm_nonneg x))).mp
  rw [sq_abs, mul_pow, EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a x.ofLp).trans
    (mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

/-- `x ↦ linearField A x` is `D`-Lipschitz on `EuclideanSpace ℝ I` whenever every row `A v` of
the coefficient matrix has square sum at most `D ^ 2`, by applying `abs_euclidean_linear_le`
coordinatewise to the difference `x - y`. -/
lemma lipschitzWith_linearField_euclidean {V I : Type*} [Fintype V] [Fintype I]
    (A : V → I → ℝ) (D : ℝ≥0) (hA : ∀ v, (∑ i, A v i ^ 2) ≤ (D : ℝ) ^ 2) :
    LipschitzWith D (fun x : EuclideanSpace ℝ I => linearField A x.ofLp) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg D.coe_nonneg dist_nonneg)).mpr
  intro v
  rw [Real.dist_eq]
  have he : linearField A x.ofLp v - linearField A y.ofLp v =
      ∑ i, A v i * (x - y).ofLp i := by
    simp [linearField, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  simpa only [dist_eq_norm] using abs_euclidean_linear_le (A v) D.coe_nonneg (hA v) (x - y)

/-- Composing the 1-Lipschitz map `crossingValue Q` with a `D`-Lipschitz `linearField` gives a
`D`-Lipschitz function of the Euclidean coefficient space, using
`lipschitzWith_linearField_euclidean` and `lipschitzWith_crossingValue`. -/
lemma lipschitzWith_crossingValue_linear_euclidean {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : Q.Nonempty) {I : Type*} [Fintype I]
    (A : Q → I → ℝ) (D : ℝ≥0) (hA : ∀ v, (∑ i, A v i ^ 2) ≤ (D : ℝ) ^ 2) :
    LipschitzWith D (fun x : EuclideanSpace ℝ I => crossingValue Q (linearField A x.ofLp)) := by
  have hh := (lipschitzWith_crossingValue hQ hN).comp (lipschitzWith_linearField_euclidean A D hA)
  simpa only [one_mul, Function.comp_def] using hh

/-- `External.BallGreen.cutField r L φ` squared is summable over `Site 4`, since it vanishes
outside the finite box `boxFinset 0 r`. -/
lemma summable_cutField_sq (r L : ℕ) (φ : ℝ → ℝ) :
    Summable (fun u : Site 4 => External.BallGreen.cutField r L φ u ^ 2) := by
  apply summable_of_ne_finset_zero (s := boxFinset 0 r)
  intro u hu
  rw [cutField_eq_zero_of_notMem_boxFinset r L φ hu, zero_pow (by decide : 2 ≠ 0)]

/-- A finite sum, over a finset `s` of sites, of squares of a summable function `h` shifted by
`z` is bounded by the full sum `∑' u, h u ^ 2`, since the shift is a bijection of `Site d`. -/
lemma sum_translate_sq_le_tsum {d : ℕ} {h : Site d → ℝ}
    (hh : Summable (fun u => h u ^ 2)) (s : Finset (Site d)) (z : Site d) :
    (∑ y : s, h ((y : Site d) - z) ^ 2) ≤ ∑' u, h u ^ 2 := by
  classical
  have hs : Summable (fun y : Site d => h (y - z) ^ 2) :=
    hh.comp_injective (Equiv.subRight z).injective
  calc
    _ = ∑ y ∈ s, h (y - z) ^ 2 := Finset.sum_coe_sort s (fun y => h (y - z) ^ 2)
    _ ≤ ∑' y : Site d, h (y - z) ^ 2 := hs.sum_le_tsum s (fun _ _ => sq_nonneg _)
    _ = _ := (Equiv.subRight z).tsum_eq (fun u => h u ^ 2)

/-- **Quantitative square-sum bound for the cutoff field.**  Under `External.BallGreenBounds`,
the sum over all sites of `External.BallGreen.cutField r L φ ^ 2` is at most `G * log r` for a
constant `G` uniform in the radius `r ≥ 2`, the range `L` and the cutoff profile `φ`, by
comparing the cutoff field to the killed Green function on the box of radius `r`. -/
lemma cutField_square_sum_bound (hBall : External.BallGreenBounds) :
    ∃ G > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) ≤ G * Real.log r := by
  obtain ⟨G, g, hG, _, hb⟩ := hBall
  refine ⟨G, hG, ?_⟩
  intro r hr L φ hφ
  calc
    _ ≤ ∑' u : Site 4, killedGreen (External.BallGreen.box r) 0 u ^ 2 := by
      refine Summable.tsum_le_tsum ?_ (summable_cutField_sq r L φ) (summable_killedGreen_box_sq r)
      intro u
      have hnear := (nearKernel_nonneg_le r L hφ u).1
      dsimp [nearKernel] at hnear
      exact (sq_le_sq₀ (cutField_nonneg r L hφ u) ((hb r hr).1 u).1).mpr (by linarith)
    _ ≤ _ := (hb r hr).2.1

/-- **Assembled Lipschitz bound at a far rectangle.**  For each finite set `s` of sites playing
the role of coefficients `z : Q → Site 4`, the crossing value of the linear field built from
sites translated by `z` is Lipschitz, uniformly in `r`, `L` and the cutoff `φ`, with constant
`sqrt(G log r)` for the constant `G` of `cutField_square_sum_bound`. -/
lemma exists_far_rectangle_euclidean_lipschitz (hBall : External.BallGreenBounds) :
    ∃ G > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → Q.Nonempty → ∀ z : Q → Site 4,
        ∀ s : Finset (Site 4), LipschitzWith ⟨Real.sqrt (G * Real.log r), Real.sqrt_nonneg _⟩
          (fun x : EuclideanSpace ℝ s => crossingValue Q
            (linearField
              (fun v (i : s) => External.BallGreen.cutField r L φ ((i : Site 4) - z v))
              x.ofLp)) := by
  obtain ⟨G, hG, hsum⟩ := cutField_square_sum_bound hBall
  refine ⟨G, hG, ?_⟩
  intro r hr L φ hφ Q hQ hN z s
  apply lipschitzWith_crossingValue_linear_euclidean hQ hN
  intro v
  change (∑ i : s, External.BallGreen.cutField r L φ ((i : Site 4) - z v) ^ 2) ≤
    Real.sqrt (G * Real.log r) ^ 2
  rw [Real.sq_sqrt (mul_nonneg hG.le (Real.log_natCast_nonneg r))]
  exact (sum_translate_sq_le_tsum (summable_cutField_sq r L φ) s (z v)).trans (hsum r hr L φ hφ)

end Sandpile
