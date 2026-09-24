/-
Nearest-neighbor edge oscillations and their expected size for
Gaussian far Green fields on finite coordinate-plane rectangles.
-/
import Sandpile.Support.GaussianIncrement
import Sandpile.Support.FarOscillation

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

noncomputable def edgeOscillation {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) : ℝ := by
  classical
  exact finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)

lemma edgeOscillation_nonneg {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) : 0 ≤ edgeOscillation G F := by
  classical
  obtain ⟨p, hp⟩ := finiteMaximum_mem (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)
  change 0 ≤ finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)
  rw [hp]
  split_ifs <;> positivity

lemma abs_sub_le_edgeOscillation {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) {v w : V} (hvw : G.Adj v w) :
    |F v - F w| ≤ edgeOscillation G F := by
  classical
  have hh := le_finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0) (v, w)
  simpa only [hvw, if_true, edgeOscillation] using hh

lemma edgeOscillation_le {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ v w, G.Adj v w → |F v - F w| ≤ a) : edgeOscillation G F ≤ a := by
  classical
  apply (finiteMaximum_le_iff _ _).mpr
  intro p
  split_ifs with hp
  · exact hF p.1 p.2 hp
  · exact ha

lemma lattice_adj_coord_abs_le {d : ℕ} {z w : Site d} (hzw : (lattice d).Adj z w) (i : Fin d) :
    |w i - z i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := hzw
  · rw [hj]
    by_cases h : j = i
    · subst j; simp [unit]
    · simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  · rw [hj]
    by_cases h : j = i
    · subst j; simp [unit]
    · simp [unit, Pi.single_eq_of_ne (Ne.symm h)]

lemma latticeNorm_planeTranslate_sub_le_of_adj {Q : Finset (Site 2)} {z w : Q}
    (hzw : (rectangleGraph Q).Adj z w) (x : Site 4) :
    External.BallGreen.latticeNorm (planeTranslate x w - planeTranslate x z) ≤ 2 := by
  have hcoords (i : Fin 2) : |((w : Site 2) i : ℝ) - ((z : Site 2) i : ℝ)| ≤ 1 := by
    have hh := lattice_adj_coord_abs_le (show (lattice 2).Adj (z : Site 2) (w : Site 2) from hzw) i
    exact_mod_cast hh
  simpa only [mul_one] using latticeNorm_planeTranslate_sub_le x z w zero_le_one hcoords

lemma exists_gaussian_rectangle_increment_bound (hBall : External.BallGreenBounds) (V : ℝ≥0) :
    ∃ C > 0, ∀ Q : Finset (Site 2), ∀ [Nonempty Q], ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → Q.card ≤ r ^ 3 →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        Integrable (fun ζ : Site 4 → ℝ => edgeOscillation (rectangleGraph Q)
          (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
            (LatticeProb.iidLaw 4 (gaussianReal 0 v)) ∧
        (∫ ζ : Site 4 → ℝ, edgeOscillation (rectangleGraph Q)
          (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
            ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) ≤ C * Real.sqrt (Real.log r) := by
  classical
  obtain ⟨C, hC, hmax⟩ := exists_gaussian_far_increment_maximum_bound hBall 1 6 le_rfl (by norm_num) V
  obtain ⟨G, _, hinc⟩ := exists_hasSubgaussianMGF_far_increment hBall
  refine ⟨C, hC, ?_⟩
  intro Q _ r L hr hL hcard φ hφ x v hv
  let z (p : Q × Q) : Site 4 := planeTranslate x p.1
  let w (p : Q × Q) : Site 4 := if (rectangleGraph Q).Adj p.1 p.2 then planeTranslate x p.2 else z p
  have hdist (p : Q × Q) : External.BallGreen.latticeNorm (w p - z p) ≤ 1 * L := by
    dsimp [w, z]
    split_ifs with hp
    · exact (latticeNorm_planeTranslate_sub_le_of_adj hp x).trans (by simpa only [one_mul] using (show (2 : ℝ) ≤ L from by exact_mod_cast hL))
    · simp [External.BallGreen.latticeNorm]
  have hN : (Fintype.card (Q × Q) : ℝ) ≤ (r : ℝ) ^ (6 : ℝ) := by
    have hh := Nat.mul_le_mul hcard hcard
    have hh' : (Q.card : ℝ) * Q.card ≤ (r : ℝ) ^ 3 * (r : ℝ) ^ 3 := by exact_mod_cast hh
    simpa only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Real.rpow_ofNat] using hh'.trans_eq (by ring)
  have he (ζ : Site 4 → ℝ) : edgeOscillation (rectangleGraph Q)
      (fun a => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x a)) =
      finiteMaximum (fun p : Q × Q =>
        |finiteKernelField (External.BallGreen.cutField r L φ) ζ (z p) -
          finiteKernelField (External.BallGreen.cutField r L φ) ζ (w p)|) := by
    unfold edgeOscillation
    congr 1
    funext p
    dsimp [w, z]
    split_ifs <;> simp
  constructor
  · have hi (p : Q × Q) := (hinc r L hr hL φ hφ 1 le_rfl (z p) (w p) (hdist p) v).integrable
    simpa only [he] using integrable_finiteMaximum_abs hi
  · have hh := hmax (Q × Q) r L hr hL hN φ hφ z w hdist v hv
    simpa only [he] using hh

end Sandpile
