import Sandpile.Support.GaussianIncrement
import Sandpile.Support.FarOscillation

/-!
# Edge oscillation and Gaussian far-field increment bounds

Nearest-neighbor edge oscillations and their expected size for Gaussian far Green fields on
finite coordinate-plane rectangles. `edgeOscillation` is the maximum absolute jump of a field
across an edge of a finite graph, and `exists_gaussian_rectangle_increment_bound` shows that,
for the far (cutoff) field under the Gaussian law, both its edge oscillation is integrable and
its expected value is `O (sqrt (log r))` uniformly over rectangles of subpolynomial size.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

/-- The edge oscillation of `F` on the finite graph `G`: the maximum of `|F p.1 - F p.2|` over
adjacent pairs `p.1, p.2`, taken as `0` when there is no edge. -/
noncomputable def edgeOscillation {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) : ℝ := by
  classical
  exact finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)

/-- `edgeOscillation G F` is nonnegative, since it is a maximum of values that are either an
absolute value or `0`. -/
lemma edgeOscillation_nonneg {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) : 0 ≤ edgeOscillation G F := by
  classical
  obtain ⟨p, hp⟩ :=
    finiteMaximum_mem (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)
  change 0 ≤ finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0)
  rw [hp]
  split_ifs <;> positivity

/-- For adjacent `v, w : V`, the increment `|F v - F w|` is at most `edgeOscillation G F`, by
definition of `edgeOscillation` as a maximum over pairs. -/
lemma abs_sub_le_edgeOscillation {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) {v w : V} (hvw : G.Adj v w) :
    |F v - F w| ≤ edgeOscillation G F := by
  classical
  have hh := le_finiteMaximum (fun p : V × V => if G.Adj p.1 p.2 then |F p.1 - F p.2| else 0) (v, w)
  simpa only [hvw, if_true, edgeOscillation] using hh

/-- If every adjacent pair `v, w` satisfies `|F v - F w| ≤ a` for some `a ≥ 0`, then
`edgeOscillation G F ≤ a`, since `a` bounds every term of the defining maximum. -/
lemma edgeOscillation_le {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (F : V → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hF : ∀ v w, G.Adj v w → |F v - F w| ≤ a) : edgeOscillation G F ≤ a := by
  classical
  apply (finiteMaximum_le_iff _ _).mpr
  intro p
  split_ifs with hp
  · exact hF p.1 p.2 hp
  · exact ha

/-- Adjacent lattice sites `z`, `w` differ by at most `1` in every coordinate `i`, since a
lattice edge changes exactly one coordinate by `±1` (via `unit i`). -/
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

/-- Translating an edge of `rectangleGraph Q` into `Site 4` via `planeTranslate x` moves each
endpoint by at most `2` in `External.BallGreen.latticeNorm`, using
`lattice_adj_coord_abs_le` on the two changed coordinates. -/
lemma latticeNorm_planeTranslate_sub_le_of_adj {Q : Finset (Site 2)} {z w : Q}
    (hzw : (rectangleGraph Q).Adj z w) (x : Site 4) :
    External.BallGreen.latticeNorm (planeTranslate x w - planeTranslate x z) ≤ 2 := by
  have hcoords (i : Fin 2) : |((w : Site 2) i : ℝ) - ((z : Site 2) i : ℝ)| ≤ 1 := by
    have hh := lattice_adj_coord_abs_le (show (lattice 2).Adj (z : Site 2) (w : Site 2) from hzw) i
    exact_mod_cast hh
  simpa only [mul_one] using latticeNorm_planeTranslate_sub_le x z w zero_le_one hcoords

/-- For rectangles `Q` with `Q.card ≤ r ^ 3`, cutoffs `φ`, and Gaussian scenery of variance
`v ≤ V`, the edge oscillation of the far (cutoff) kernel field translated onto `Q` is
integrable, and its expectation is at most `C * sqrt (log r)` for a constant `C` depending
only on `hBall` and `V`. -/
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
  obtain ⟨C, hC, hmax⟩ :=
    exists_gaussian_far_increment_maximum_bound hBall 1 6 le_rfl (by norm_num) V
  obtain ⟨G, _, hinc⟩ := exists_hasSubgaussianMGF_far_increment hBall
  refine ⟨C, hC, ?_⟩
  intro Q _ r L hr hL hcard φ hφ x v hv
  let z (p : Q × Q) : Site 4 := planeTranslate x p.1
  let w (p : Q × Q) : Site 4 := if (rectangleGraph Q).Adj p.1 p.2 then planeTranslate x p.2 else z p
  have hdist (p : Q × Q) : External.BallGreen.latticeNorm (w p - z p) ≤ 1 * L := by
    dsimp [w, z]
    split_ifs with hp
    · exact (latticeNorm_planeTranslate_sub_le_of_adj hp x).trans
        (by simpa only [one_mul] using (show (2 : ℝ) ≤ L from by exact_mod_cast hL))
    · simp [External.BallGreen.latticeNorm]
  have hN : (Fintype.card (Q × Q) : ℝ) ≤ (r : ℝ) ^ (6 : ℝ) := by
    have hh := Nat.mul_le_mul hcard hcard
    have hh' : (Q.card : ℝ) * Q.card ≤ (r : ℝ) ^ 3 * (r : ℝ) ^ 3 := by exact_mod_cast hh
    simpa only [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, Real.rpow_ofNat] using
      hh'.trans_eq (by ring)
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
