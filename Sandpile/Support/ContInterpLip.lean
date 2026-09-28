import Sandpile.Support.ContInterpBound
import LatticeProb.Support.ContSums

/-!
# Lipschitz bound for the one-dimensional mesh interpolation

The one-dimensional piecewise-linear interpolation `interp1 F u` from an integer-indexed
family `F` is affine on each interval between consecutive integers, with slope the mesh
increment `F(n+1) - F(n)`, and continuous across them; a family bounded by `M` is therefore
`2M`-Lipschitz (`abs_interp1_sub_le`), with no constraint relating the two points, by induction
on the number of mesh cells separating them. Since the multilinear interpolation `linInterp`
of the rescaled linear field is, in each variable separately, a convex combination of such
one-dimensional interpolations, this yields its Lipschitz bound in the time variable
(`abs_linInterp_sub_time_le`), needed for the tightness of the field at scales where the mesh
diameter itself is not small.
-/

open LatticeProb

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Frozen.HeatPotentialInvariance

/-- Inside one cell the interpolation is affine with slope the mesh increment. -/
theorem abs_interp1_sub_le_same (F : ℤ → ℝ) (M : ℝ) (hM : ∀ n : ℤ, |F n| ≤ M)
    {u v : ℝ} (h : ⌊u⌋ = ⌊v⌋) : |interp1 F u - interp1 F v| ≤ 2 * M * |u - v| := by
  have hfr : Int.fract u - Int.fract v = u - v := by
    rw [Int.fract, Int.fract, h]
    ring
  have hkey : interp1 F u - interp1 F v = (u - v) * (F (⌊u⌋ + 1) - F ⌊u⌋) := by
    rw [interp1, interp1, h, ← hfr]
    ring
  have hdiff : |F (⌊u⌋ + 1) - F ⌊u⌋| ≤ 2 * M := by
    have h1 := hM (⌊u⌋ + 1)
    have h2 := hM ⌊u⌋
    have := abs_sub (F (⌊u⌋ + 1)) (F ⌊u⌋)
    calc |F (⌊u⌋ + 1) - F ⌊u⌋| ≤ |F (⌊u⌋ + 1)| + |F ⌊u⌋| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [hkey, abs_mul]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (F 0)) (hM 0)
  calc |u - v| * |F (⌊u⌋ + 1) - F ⌊u⌋| ≤ |u - v| * (2 * M) :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    _ = 2 * M * |u - v| := by ring

/-- The interpolation at `u` differs from the mesh value at the right endpoint of
its cell by at most the mesh increment times the distance to that endpoint. -/
theorem abs_interp1_sub_succ (F : ℤ → ℝ) (M : ℝ) (hM : ∀ n : ℤ, |F n| ≤ M) (u : ℝ) :
    |interp1 F u - F (⌊u⌋ + 1)| ≤ 2 * M * ((⌊u⌋ : ℝ) + 1 - u) := by
  have hkey : interp1 F u - F (⌊u⌋ + 1) = (1 - Int.fract u) * (F ⌊u⌋ - F (⌊u⌋ + 1)) := by
    rw [interp1]
    ring
  have hf1 : Int.fract u < 1 := Int.fract_lt_one u
  have hfr : 1 - Int.fract u = (⌊u⌋ : ℝ) + 1 - u := by
    rw [Int.fract]
    ring
  have hdiff : |F ⌊u⌋ - F (⌊u⌋ + 1)| ≤ 2 * M := by
    have h1 := hM ⌊u⌋
    have h2 := hM (⌊u⌋ + 1)
    calc |F ⌊u⌋ - F (⌊u⌋ + 1)| ≤ |F ⌊u⌋| + |F (⌊u⌋ + 1)| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  rw [hkey, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Int.fract u), hfr]
  have hnn : (0:ℝ) ≤ (⌊u⌋ : ℝ) + 1 - u := by rw [← hfr]; linarith
  calc ((⌊u⌋ : ℝ) + 1 - u) * |F ⌊u⌋ - F (⌊u⌋ + 1)| ≤ ((⌊u⌋ : ℝ) + 1 - u) * (2 * M) :=
        mul_le_mul_of_nonneg_left hdiff hnn
    _ = 2 * M * ((⌊u⌋ : ℝ) + 1 - u) := by ring

/-- The interpolation is `2M`-Lipschitz, by induction on the number of mesh cells
separating the two points. -/
theorem abs_interp1_sub_le_aux (F : ℤ → ℝ) (M : ℝ) (hM : ∀ n : ℤ, |F n| ≤ M) :
    ∀ k : ℕ, ∀ u v : ℝ, u ≤ v → (⌊v⌋ - ⌊u⌋).toNat ≤ k →
      |interp1 F u - interp1 F v| ≤ 2 * M * (v - u) := by
  intro k
  induction k with
  | zero =>
      intro u v huv hk
      have hle : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor huv
      have hfl : ⌊u⌋ = ⌊v⌋ := by omega
      have hsame := abs_interp1_sub_le_same F M hM hfl
      rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub] at hsame
      exact hsame
  | succ k ih =>
      intro u v huv hk
      have hle : ⌊u⌋ ≤ ⌊v⌋ := Int.floor_le_floor huv
      by_cases hfl : ⌊u⌋ = ⌊v⌋
      · have hsame := abs_interp1_sub_le_same F M hM hfl
        rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub] at hsame
        exact hsame
      · have hlt : ⌊u⌋ < ⌊v⌋ := lt_of_le_of_ne hle hfl
        set w : ℝ := ((⌊u⌋ + 1 : ℤ) : ℝ) with hw
        have hfw : ⌊w⌋ = ⌊u⌋ + 1 := by rw [hw, Int.floor_intCast]
        have huw : u ≤ w := by
          have h0 := Int.lt_floor_add_one u
          rw [hw]
          push_cast
          linarith
        have hwv : w ≤ v := by
          have h1 : ((⌊u⌋ + 1 : ℤ) : ℝ) ≤ ((⌊v⌋ : ℤ) : ℝ) := by
            exact_mod_cast (by omega : (⌊u⌋ + 1 : ℤ) ≤ ⌊v⌋)
          have h2 : ((⌊v⌋ : ℤ) : ℝ) ≤ v := Int.floor_le v
          rw [hw]
          linarith
        have h1 : |interp1 F u - interp1 F w| ≤ 2 * M * (w - u) := by
          have hval : interp1 F w = F (⌊u⌋ + 1) := by rw [hw, interp1_intCast]
          have hwu : (⌊u⌋ : ℝ) + 1 - u = w - u := by rw [hw]; push_cast; ring
          rw [hval, ← hwu]
          exact abs_interp1_sub_succ F M hM u
        have h2 : |interp1 F w - interp1 F v| ≤ 2 * M * (v - w) :=
          ih w v hwv (by rw [hfw]; omega)
        calc |interp1 F u - interp1 F v|
            ≤ |interp1 F u - interp1 F w| + |interp1 F w - interp1 F v| :=
              abs_sub_le _ _ _
          _ ≤ 2 * M * (w - u) + 2 * M * (v - w) := add_le_add h1 h2
          _ = 2 * M * (v - u) := by ring

/-- **The interpolation is `2M`-Lipschitz.** -/
theorem abs_interp1_sub_le (F : ℤ → ℝ) (M : ℝ) (hM : ∀ n : ℤ, |F n| ≤ M) (u v : ℝ) :
    |interp1 F u - interp1 F v| ≤ 2 * M * |u - v| := by
  rcases le_total u v with h | h
  · rw [abs_of_nonpos (by linarith : u - v ≤ 0), neg_sub]
    exact abs_interp1_sub_le_aux F M hM (⌊v⌋ - ⌊u⌋).toNat u v h le_rfl
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ u - v)]
    exact abs_interp1_sub_le_aux F M hM (⌊u⌋ - ⌊v⌋).toNat v u h le_rfl

/-- **The interpolated field is Lipschitz in the time variable**, with constant
twice the bound on the mesh values times the mesh rate `R²`.  The `2^d` spatial
weights do not depend on the time, so the difference is a convex combination of
one-dimensional mesh interpolations in the time. -/
theorem abs_linInterp_sub_time_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (M : ℝ)
    (hM : ∀ (k : ℕ) (z : Site d), |meshValue d R ζ k z| ≤ M)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r' w| ≤ 2 * M * |R ^ 2 * r - R ^ 2 * r'| := by
  classical
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set t : Fin d → ℝ := fun i => R * w i - (b i : ℝ) with ht
  have ht0 : ∀ i, 0 ≤ t i := fun i => (fract_mem (R * w i)).1
  have ht1 : ∀ i, t i ≤ 1 := fun i => (fract_mem (R * w i)).2
  set F : (Fin d → Bool) → ℤ → ℝ := fun ε k =>
    meshValue d R ζ k.toNat (fun i => b i + if ε i then 1 else 0) with hF
  have key : ∀ u : ℝ, 0 ≤ u → ∀ ε : Fin d → Bool,
      (1 - (u - ((⌊u⌋₊ : ℕ) : ℝ))) * meshValue d R ζ ⌊u⌋₊ (fun i => b i + if ε i then 1 else 0)
        + (u - ((⌊u⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊u⌋₊ + 1) (fun i => b i + if ε i then 1 else 0)
      = interp1 (F ε) u := by
    intro u hu ε
    have hfl0 : (0:ℤ) ≤ ⌊u⌋ := Int.floor_nonneg.mpr hu
    have hfl : (⌊u⌋).toNat = ⌊u⌋₊ := Int.floor_toNat u
    have hz : ((⌊u⌋₊ : ℕ) : ℤ) = ⌊u⌋ := by
      rw [← hfl]
      exact Int.toNat_of_nonneg hfl0
    have hcast : ((⌊u⌋₊ : ℕ) : ℝ) = ((⌊u⌋ : ℤ) : ℝ) := by exact_mod_cast hz
    have hsucc : (⌊u⌋ + 1).toNat = ⌊u⌋₊ + 1 := by omega
    rw [interp1, hF]
    simp only [hfl, hsucc]
    rw [Int.fract, hcast]
  have hdiff : linInterp d R ζ r w - linInterp d R ζ r' w
      = ∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
          (interp1 (F ε) (R ^ 2 * r) - interp1 (F ε) (R ^ 2 * r')) := by
    show (∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
        ((1 - (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ)))
            * meshValue d R ζ ⌊R ^ 2 * r⌋₊ (fun i => b i + if ε i then 1 else 0) +
          (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊R ^ 2 * r⌋₊ + 1) (fun i => b i + if ε i then 1 else 0)))
        - (∑ ε : Fin d → Bool, (∏ i : Fin d, if ε i then t i else 1 - t i) *
        ((1 - (R ^ 2 * r' - ((⌊R ^ 2 * r'⌋₊ : ℕ) : ℝ)))
            * meshValue d R ζ ⌊R ^ 2 * r'⌋₊ (fun i => b i + if ε i then 1 else 0) +
          (R ^ 2 * r' - ((⌊R ^ 2 * r'⌋₊ : ℕ) : ℝ))
            * meshValue d R ζ (⌊R ^ 2 * r'⌋₊ + 1) (fun i => b i + if ε i then 1 else 0))) = _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [key _ (mul_nonneg (sq_nonneg R) hr) ε, key _ (mul_nonneg (sq_nonneg R) hr') ε]
    ring
  rw [hdiff]
  refine abs_sum_weight_mul_le _ _ (fun ε => prod_ite_nonneg t ht0 ht1 ε)
    (sum_prod_ite d t) _ ?_
  intro ε
  exact abs_interp1_sub_le (F ε) M (fun n => hM _ _) (R ^ 2 * r) (R ^ 2 * r')

end Sandpile.Support
