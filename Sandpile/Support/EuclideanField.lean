import Sandpile.Support.CrossingContinuity
import Sandpile.Support.NearKernel

open scoped BigOperators NNReal

noncomputable section
namespace Sandpile

lemma abs_euclidean_linear_le {I : Type*} [Fintype I] (a : I → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (ha : (∑ i, a i ^ 2) ≤ D ^ 2) (x : EuclideanSpace ℝ I) :
    |∑ i, a i * x.ofLp i| ≤ D * ‖x‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD (norm_nonneg x))).mp
  rw [sq_abs, mul_pow, EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a x.ofLp).trans
    (mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

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

lemma lipschitzWith_crossingValue_linear_euclidean {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : Q.Nonempty) {I : Type*} [Fintype I]
    (A : Q → I → ℝ) (D : ℝ≥0) (hA : ∀ v, (∑ i, A v i ^ 2) ≤ (D : ℝ) ^ 2) :
    LipschitzWith D (fun x : EuclideanSpace ℝ I => crossingValue Q (linearField A x.ofLp)) := by
  have hh := (lipschitzWith_crossingValue hQ hN).comp (lipschitzWith_linearField_euclidean A D hA)
  simpa only [one_mul, Function.comp_def] using hh

lemma summable_cutField_sq (r L : ℕ) (φ : ℝ → ℝ) :
    Summable (fun u : Site 4 => External.BallGreen.cutField r L φ u ^ 2) := by
  apply summable_of_ne_finset_zero (s := boxFinset 0 r)
  intro u hu
  rw [cutField_eq_zero_of_notMem_boxFinset r L φ hu, zero_pow (by decide : 2 ≠ 0)]

lemma sum_translate_sq_le_tsum {d : ℕ} {h : Site d → ℝ}
    (hh : Summable (fun u => h u ^ 2)) (s : Finset (Site d)) (z : Site d) :
    (∑ y : s, h ((y : Site d) - z) ^ 2) ≤ ∑' u, h u ^ 2 := by
  classical
  have hs : Summable (fun y : Site d => h (y - z) ^ 2) := hh.comp_injective (Equiv.subRight z).injective
  calc
    _ = ∑ y ∈ s, h (y - z) ^ 2 := Finset.sum_coe_sort s (fun y => h (y - z) ^ 2)
    _ ≤ ∑' y : Site d, h (y - z) ^ 2 := hs.sum_le_tsum s (fun _ _ => sq_nonneg _)
    _ = _ := (Equiv.subRight z).tsum_eq (fun u => h u ^ 2)

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

lemma exists_far_rectangle_euclidean_lipschitz (hBall : External.BallGreenBounds) :
    ∃ G > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → Q.Nonempty → ∀ z : Q → Site 4,
        ∀ s : Finset (Site 4), LipschitzWith ⟨Real.sqrt (G * Real.log r), Real.sqrt_nonneg _⟩
          (fun x : EuclideanSpace ℝ s => crossingValue Q
            (linearField (fun v (i : s) => External.BallGreen.cutField r L φ ((i : Site 4) - z v)) x.ofLp)) := by
  obtain ⟨G, hG, hsum⟩ := cutField_square_sum_bound hBall
  refine ⟨G, hG, ?_⟩
  intro r hr L φ hφ Q hQ hN z s
  apply lipschitzWith_crossingValue_linear_euclidean hQ hN
  intro v
  change (∑ i : s, External.BallGreen.cutField r L φ ((i : Site 4) - z v) ^ 2) ≤ Real.sqrt (G * Real.log r) ^ 2
  rw [Real.sq_sqrt (mul_nonneg hG.le (Real.log_natCast_nonneg r))]
  exact (sum_translate_sq_le_tsum (summable_cutField_sq r L φ) s (z v)).trans (hsum r hr L φ hφ)

end Sandpile
