import Sandpile.Support.GaussianLinear
import Sandpile.Support.SubgaussianMaximum

/-!
# Sub-Gaussian Far-Increment Bounds

Sub-Gaussian bounds and expected finite maxima of far Green-field
increments at distances controlled by the cutoff scale.

This module shows that the increment of a cutoff Green kernel field between two
sites at least `M · L` apart in lattice norm has a sub-Gaussian moment
generating function with a variance proxy controlled by `M`
(`exists_hasSubgaussianMGF_far_increment`), and combines this with the finite
maximal inequality for sub-Gaussian families to bound the expected maximum of
finitely many such increments in terms of `log r`
(`exists_gaussian_far_increment_maximum_bound`). A logarithmic comparison lemma
(`log_two_card_le_log_scale`) converts a polynomial bound on the index set's
cardinality into the logarithmic rate needed there.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

/-- The increment `finiteKernelField (cutField r L φ) ζ z - finiteKernelField (cutField r L φ) ζ
w` of the cutoff Green field between sites `z, w` at lattice distance at most `M · L` has a
sub-Gaussian moment generating function with variance proxy `v · G · (1 + M)^4`, where `G` comes
from `External.BallGreenBounds`: the increment is a finite sum of i.i.d. coordinates weighted by
`k y = h (y - z) - h (y - w)`, whose squared sum is controlled by the ball shift bound. -/
lemma exists_hasSubgaussianMGF_far_increment (hBall : External.BallGreenBounds) :
    ∃ G : ℝ≥0, 0 < G ∧ ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ M : ℝ, 1 ≤ M → ∀ z w : Site 4, External.BallGreen.latticeNorm (w - z) ≤ M * L →
        ∀ v : ℝ≥0, HasSubgaussianMGF
          (fun ζ : Site 4 → ℝ => finiteKernelField (External.BallGreen.cutField r L φ) ζ z -
            finiteKernelField (External.BallGreen.cutField r L φ) ζ w)
          ⟨(v : ℝ) * (G : ℝ) * (1 + M) ^ 4, by positivity⟩
            (LatticeProb.iidLaw 4 (gaussianReal 0 v)) := by
  classical
  obtain ⟨G, g, hG, _, hball⟩ := hBall
  refine ⟨⟨G, hG.le⟩, (show (0 : ℝ≥0) < ⟨G, hG.le⟩ from hG), ?_⟩
  intro r L hr hL φ hφ M hM z w hzw v
  let h := External.BallGreen.cutField r L φ
  let k (y : Site 4) := h (y - z) - h (y - w)
  obtain ⟨s, hs⟩ := exists_finiteKernelField_coordinates (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (![z, w])
  have hz (y : Site 4) (hy : y ∉ s) : h (y - z) = 0 := hs 0 y hy
  have hw (y : Site 4) (hy : y ∉ s) : h (y - w) = 0 := hs 1 y hy
  have hk (y : Site 4) (hy : y ∉ s) : k y = 0 := by dsimp [k]; rw [hz y hy, hw y hy, sub_self]
  have hks : Summable (fun y : Site 4 => k y ^ 2) :=
    summable_of_ne_finset_zero (s := s) (fun y hy => by rw [hk y hy, zero_pow (by decide : 2 ≠ 0)])
  obtain ⟨_, _, hshift⟩ := (hball r hr).2.2.2.2.1 L hL φ hφ
  have he : (∑' y : Site 4, k y ^ 2) = ∑' u : Site 4, (h u - h (u - (w - z))) ^ 2 := by
    calc
      _ = ∑' y : Site 4, (h (y - z) - h ((y - z) - (w - z))) ^ 2 :=
        tsum_congr (fun y => by dsimp [k]; rw [show (y - z) - (w - z) = y - w by abel])
      _ = _ := (Equiv.subRight z).tsum_eq (fun u => (h u - h (u - (w - z))) ^ 2)
  have hsum : (∑ y ∈ s, k y ^ 2) ≤ G * (1 + M) ^ 4 := by
    calc
      _ ≤ ∑' y, k y ^ 2 := hks.sum_le_tsum s (fun _ _ => sq_nonneg _)
      _ = _ := he
      _ ≤ _ := hshift M hM (w - z) hzw
  have hh := hasSubgaussianMGF_iid_finite_sum s k v
    ⟨(v : ℝ) * G * (1 + M) ^ 4, by positivity⟩ (by
      change (v : ℝ) * (∑ y ∈ s, k y ^ 2) ≤ (v : ℝ) * G * (1 + M) ^ 4
      nlinarith [mul_le_mul_of_nonneg_left hsum v.coe_nonneg])
  have hfield (ζ : Site 4 → ℝ) : finiteKernelField h ζ z - finiteKernelField h ζ w =
      ∑ y ∈ s, k y * ζ y := by
    rw [finiteKernelField_sub_eq_tsum h z w s hz hw]
    exact tsum_eq_sum (fun y hy => by
      rw [show h (y - z) - h (y - w) = k y from rfl, hk y hy, zero_mul])
  change HasSubgaussianMGF (fun ζ : Site 4 → ℝ => finiteKernelField h ζ z - finiteKernelField h ζ w)
    ⟨(v : ℝ) * G * (1 + M) ^ 4, by positivity⟩ (LatticeProb.iidLaw 4 (gaussianReal 0 v))
  simpa only [hfield] using hh

/-- If a finite index set `I` has cardinality at most `r^m`, then `log(2 |I|) ≤ (m + 1) log r`,
by taking logs of the cardinality bound and absorbing the constant `2 ≤ r`. -/
lemma log_two_card_le_log_scale {I : Type*} [Fintype I] [Nonempty I]
    {r : ℕ} (hr : 2 ≤ r) {m : ℝ} (hcard : (Fintype.card I : ℝ) ≤ (r : ℝ) ^ m) :
    Real.log (2 * Fintype.card I) ≤ (m + 1) * Real.log r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hN : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos (α := I)
  have hh := Real.log_le_log hN hcard
  rw [Real.log_rpow hrpos] at hh
  rw [Real.log_mul (by norm_num) hN.ne']
  have htwo : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) (by exact_mod_cast hr)
  nlinarith

/-- Over a finite index set `I` of cardinality at most `r^m`, the expected maximum of the absolute
cutoff-field increments between `M · L`-far pairs `(z i, w i)`, for noise variance `v ≤ V`, is at
most `C √(log r)` for a constant `C` depending only on `M`, `m` and `V`: combine the sub-Gaussian
bound `exists_hasSubgaussianMGF_far_increment` with the finite maximal inequality
`integral_finiteMaximum_abs_le` and the cardinality-to-log conversion
`log_two_card_le_log_scale`. -/
lemma exists_gaussian_far_increment_maximum_bound (hBall : External.BallGreenBounds)
    (M m : ℝ) (hM : 1 ≤ M) (hm : 0 ≤ m) (V : ℝ≥0) :
    ∃ C > 0, ∀ (I : Type*) [Fintype I] [Nonempty I], ∀ r L : ℕ, 2 ≤ r → 2 ≤ L →
      (Fintype.card I : ℝ) ≤ (r : ℝ) ^ m →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ z w : I → Site 4,
        (∀ i, External.BallGreen.latticeNorm (w i - z i) ≤ M * L) → ∀ v : ℝ≥0, v ≤ V →
          (∫ ζ : Site 4 → ℝ, finiteMaximum (fun i =>
            |finiteKernelField (External.BallGreen.cutField r L φ) ζ (z i) -
              finiteKernelField (External.BallGreen.cutField r L φ) ζ (w i)|)
              ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) ≤ C * Real.sqrt (Real.log r) := by
  obtain ⟨G, hG, hinc⟩ := exists_hasSubgaussianMGF_far_increment hBall
  let c : ℝ≥0 := ⟨(V : ℝ) * G * (1 + M) ^ 4, by positivity⟩
  let C : ℝ := (1 + (c : ℝ) / 2) * Real.sqrt (m + 1)
  have hC : 0 < C := mul_pos (by positivity) (Real.sqrt_pos.mpr (by linarith))
  refine ⟨C, hC, ?_⟩
  intro I _ _ r L hr hL hcard φ hφ z w hzw v hv
  have hi (i : I) : HasSubgaussianMGF
      (fun ζ : Site 4 → ℝ => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z i) -
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (w i)) c
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)) := by
    apply hasSubgaussianMGF_mono (hinc r L hr hL φ hφ M hM (z i) (w i) (hzw i) v)
    change (v : ℝ) * G * (1 + M) ^ 4 ≤ (V : ℝ) * G * (1 + M) ^ 4
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (v : ℝ) ≤ V from hv) G.coe_nonneg)
      (by positivity)
  calc
    _ ≤ (1 + (c : ℝ) / 2) * Real.sqrt (Real.log (2 * Fintype.card I)) :=
      integral_finiteMaximum_abs_le hi
    _ ≤ (1 + (c : ℝ) / 2) * Real.sqrt ((m + 1) * Real.log r) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (log_two_card_le_log_scale hr hcard))
        (by positivity)
    _ = C * Real.sqrt (Real.log r) := by
      rw [Real.sqrt_mul (by linarith : 0 ≤ m + 1)]
      exact (mul_assoc _ _ _).symm

end Sandpile
