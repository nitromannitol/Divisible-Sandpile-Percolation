/-
The `ℓ²` modulus of the coefficient vector of the interpolated field ABOVE the
mesh spacing.

`ContCoeffL2` prices the increment of the coefficient vector by the increment of
the mesh: at two points of `[0,T] × ℝ^d` it gives
`‖c_p - c_q‖₂ ≤ R^{d/2-2}(R²|Δr| + G·R‖Δw‖₁)`, which is the right size when the
two points lie in one cell of the mesh and is too large by `(R·dist)^{(1+θ)/2}`
when they are far apart.  This module supplies the complementary estimate.  The
route is the three-point chain through the base corners of the two cells: with
`a = ⌊R²r⌋`, `b = ⌊Rw⌋` and `p̃ = (a/R², b/R)`, the coefficient vector at `p̃` is
exactly `R^{d/2-2} g_a(b, ·)`, so the middle increment is an increment of the
Green kernel in its two indices, priced by the two `L²` estimates of
`ContGreenIncrementSum` and `ContCoeffL2`, and the two outer increments are the
estimate of `ContCoeffL2` across a single cell.
-/
import Sandpile.Support.ContCoeffL2
import LatticeProb.Support.ContSums

open LatticeProb

namespace Sandpile.Support

open Sandpile Sandpile.Frozen.HeatPotentialInvariance

variable {d : ℕ} {R : ℝ}

/-- **The coefficient vector at a base corner of the mesh.**  When `R^2 r` and
every `R w_i` is an integer, the interpolation reads a single mesh point, so the
coefficient of `ζ(y)` is exactly `R^{d/2-2} g_a(b, y)`. -/
theorem interpCoeff_of_floor_eq (R r : ℝ) (w : Sandpile.Continuum.Space d)
    (a : ℕ) (b : Site d) (hr : R ^ 2 * r = (a : ℝ)) (hw : ∀ i, R * w i = (b i : ℝ))
    (y : Site d) :
    interpCoeff d R r w y
      = R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d a b y := by
  classical
  simp only [interpCoeff, hr, hw, Nat.floor_natCast, Int.floor_intCast, sub_self, sub_zero,
    one_mul, zero_mul, add_zero]
  rw [Finset.sum_eq_single (fun _ : Fin d => false)]
  · simp
  · intro ε _ hne
    have hex : ∃ i, ε i = true := by
      by_contra hc
      refine hne (funext fun i => ?_)
      by_contra hi
      exact hc ⟨i, by simpa using hi⟩
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The time coordinate of the base corner of the mesh cell of `r`. -/
noncomputable def baseTime (R r : ℝ) : ℝ := ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) / R ^ 2

/-- The space coordinate of the base corner of the mesh cell of `w`. -/
noncomputable def basePoint (R : ℝ) (w : Sandpile.Continuum.Space d) :
    Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i => ((⌊R * w i⌋ : ℤ) : ℝ) / R)

theorem basePoint_apply (R : ℝ) (w : Sandpile.Continuum.Space d) (i : Fin d) :
    basePoint R w i = ((⌊R * w i⌋ : ℤ) : ℝ) / R := rfl

theorem mul_baseTime (hR : 0 < R) (r : ℝ) :
    R ^ 2 * baseTime R r = ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) := by
  have h : R ^ 2 ≠ 0 := by positivity
  rw [baseTime]
  field_simp

theorem mul_basePoint (hR : 0 < R) (w : Sandpile.Continuum.Space d) (i : Fin d) :
    R * basePoint R w i = ((⌊R * w i⌋ : ℤ) : ℝ) := by
  rw [basePoint_apply]
  field_simp

theorem baseTime_nonneg (R r : ℝ) : 0 ≤ baseTime R r :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg R)

theorem baseTime_le (hR : 0 < R) {r : ℝ} (hr : 0 ≤ r) : baseTime R r ≤ r := by
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  have hfl : ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * r := Nat.floor_le (by positivity)
  rw [baseTime, div_le_iff₀ hR2]
  linarith

theorem abs_sub_mul_baseTime (hR : 0 < R) {r : ℝ} (hr : 0 ≤ r) :
    |R ^ 2 * r - R ^ 2 * baseTime R r| ≤ 1 := by
  rw [mul_baseTime hR]
  have h0 : (0:ℝ) ≤ R ^ 2 * r := by positivity
  have h1 : ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * r := Nat.floor_le h0
  have h2 : R ^ 2 * r < ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

theorem sum_abs_sub_mul_basePoint (hR : 0 < R) (w : Sandpile.Continuum.Space d) :
    ∑ i : Fin d, |R * w i - R * basePoint R w i| ≤ (d : ℝ) := by
  have hterm : ∀ i : Fin d, |R * w i - R * basePoint R w i| ≤ 1 := by
    intro i
    rw [mul_basePoint hR]
    have h1 : ((⌊R * w i⌋ : ℤ) : ℝ) ≤ R * w i := Int.floor_le _
    have h2 : R * w i < ((⌊R * w i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  calc ∑ i : Fin d, |R * w i - R * basePoint R w i|
      ≤ ∑ _i : Fin d, (1:ℝ) := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) := by simp

/-- **The coefficient vector at the base corner of the cell of `(r, w)`.** -/
theorem interpCoeff_basePoint (hR : 0 < R) (r : ℝ) (w : Sandpile.Continuum.Space d)
    (y : Site d) :
    interpCoeff d R (baseTime R r) (basePoint R w) y
      = R ^ ((d : ℝ) / 2 - 2)
          * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ (fun i => ⌊R * w i⌋) y :=
  interpCoeff_of_floor_eq R (baseTime R r) (basePoint R w) ⌊R ^ 2 * r⌋₊
    (fun i => ⌊R * w i⌋) (mul_baseTime hR r) (fun i => mul_basePoint hR w i) y

theorem summable_greenTime_sub_sq (k k' : ℕ) (z z' : Site d) :
    Summable (fun y : Site d =>
      (Sandpile.greenTime d k z y - Sandpile.greenTime d k' z' y) ^ 2) := by
  have s11 := Sandpile.summable_greenTime_mul_greenTime (d := d) k k z z
  have s22 := Sandpile.summable_greenTime_mul_greenTime (d := d) k' k' z' z'
  have s12 := Sandpile.summable_greenTime_mul_greenTime (d := d) k k' z z'
  have s21 := Sandpile.summable_greenTime_mul_greenTime (d := d) k' k z' z
  exact ((s11.add s22).sub (s12.add s21)).congr fun y => by ring

theorem interpCoeff_eq_zero_of_not_mem_box (R r : ℝ) (w : Sandpile.Continuum.Space d) {n : ℕ}
    (hn : ⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1) ≤ n) {y : Site d}
    (hy : y ∉ Sandpile.boxFinset (0 : Site d) n) : interpCoeff d R r w y = 0 := by
  refine interpCoeff_eq_zero_of_not_mem R r w (fun ε => ?_) hy
  refine subset_trans (interp_box_subset R ‖w‖ r w le_rfl ε) (fun x hx => ?_)
  exact Sandpile.mem_boxFinset (le_trans (Sandpile.mem_boxFinset_iff.mp hx) hn)

theorem summable_interpCoeff_sub_sq (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d) :
    Summable (fun y : Site d => (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2) := by
  classical
  refine summable_of_ne_finset_zero (s := Sandpile.boxFinset (0 : Site d)
    (max (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1))
      (⌈|R| * ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * r'⌋₊ + 1)))) fun y hy => ?_
  rw [interpCoeff_eq_zero_of_not_mem_box R r w (le_max_left _ _) hy,
    interpCoeff_eq_zero_of_not_mem_box R r' w' (le_max_right _ _) hy]
  ring

/-- The Euclidean site distance is at most the `ℓ¹` distance. -/
theorem latticeDist_le_sum_abs (x y : Site d) :
    Sandpile.External.latticeDist x y ≤ ∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| := by
  have hsq : ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2
      ≤ (∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|) ^ 2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|) (fun i _ => abs_nonneg _)
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq_abs]
    push_cast
    ring
  have hnn : (0:ℝ) ≤ ∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  calc Sandpile.External.latticeDist x y
      = Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin d, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| := Real.sqrt_sq hnn

/-- The mesh sites of two points are at Euclidean distance at most `R` times
their `ℓ¹` distance plus the dimension. -/
theorem latticeDist_baseSite_le {R : ℝ} (hR : 0 ≤ R) (w w' : Sandpile.Continuum.Space d) :
    Sandpile.External.latticeDist (fun i => ⌊R * w i⌋) (fun i => ⌊R * w' i⌋)
      ≤ R * (∑ i : Fin d, |w i - w' i|) + (d : ℝ) := by
  have hterm : ∀ i : Fin d,
      |((⌊R * w i⌋ : ℤ) : ℝ) - ((⌊R * w' i⌋ : ℤ) : ℝ)| ≤ R * |w i - w' i| + 1 := by
    intro i
    refine le_trans (abs_intFloor_sub_le (R * w i) (R * w' i)) ?_
    have : |R * w i - R * w' i| = R * |w i - w' i| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hR]
    rw [this]
  refine le_trans (latticeDist_le_sum_abs _ _) ?_
  calc ∑ i : Fin d, |((⌊R * w i⌋ : ℤ) : ℝ) - ((⌊R * w' i⌋ : ℤ) : ℝ)|
      ≤ ∑ i : Fin d, (R * |w i - w' i| + 1) := Finset.sum_le_sum fun i _ => hterm i
    _ = R * (∑ i : Fin d, |w i - w' i|) + (d : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp

/-- **The `L²` increment of the Green kernel in time, symmetrically in the two
time indices.** -/
theorem exists_tsum_greenTime_time_sub_sq_le' (hHK : Sandpile.External.HeatKernelBounds)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a a' : ℕ) (x : Site d),
      ∑' y : Site d, (Sandpile.greenTime d a x y - Sandpile.greenTime d a' x y) ^ 2
        ≤ C * (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_tsum_greenTime_time_sub_sq_le hHK hd hd3
  refine ⟨C, hC, fun a a' x => ?_⟩
  rcases le_total a' a with h | h
  · have hcast : ((a - a' : ℕ) : ℝ) = |(a : ℝ) - (a' : ℝ)| := by
      have hle : ((a' : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h, abs_of_nonneg (by linarith)]
    rw [← hcast]
    exact hb a' a h x
  · have hcast : ((a' - a : ℕ) : ℝ) = |(a : ℝ) - (a' : ℝ)| := by
      have hle : ((a : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_sub h, abs_of_nonpos (by linarith)]
      ring
    have hsym : ∑' y : Site d,
        (Sandpile.greenTime d a x y - Sandpile.greenTime d a' x y) ^ 2
        = ∑' y : Site d,
          (Sandpile.greenTime d a' x y - Sandpile.greenTime d a x y) ^ 2 :=
      tsum_congr fun y => by ring
    rw [hsym, ← hcast]
    exact hb a a' h x

/-- **The `ℓ²` increment of the coefficient vector across a single mesh cell.**
When the two points differ by at most one mesh cell in time and by at most one
mesh cell in each space coordinate, the `ℓ²` increment of the coefficient vector
is at most `C R^{-(1-θ)/2}`, with `C` free of `R` and of the two points. -/
theorem exists_sqrt_tsum_interpCoeff_one_cell
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T →
      |R ^ 2 * r - R ^ 2 * r'| ≤ 1 →
      (∑ i : Fin d, |R * w i - R * w' i|) ≤ (d : ℝ) →
      Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        ≤ C * R ^ (-((1 - θ) / 2)) := by
  obtain ⟨C₁, hC₁, hα⟩ := exists_sqrt_tsum_interpCoeff_sub_le hHK hd hd3 hθ0 hθ1
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hs0 : (0:ℝ) ≤ (3 - (d : ℝ) + θ) / 2 := by linarith
  have hK0 : (0:ℝ) ≤ Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) := Real.sqrt_nonneg _
  refine ⟨1 + (d : ℝ) * Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)), by positivity, ?_⟩
  intro R hR r r' w w' hr hr' hrT hr'T ht hw
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hbase : (2:ℝ) + R ^ 2 * T ≤ (2 + T) * R ^ 2 := by nlinarith
  have hGle : Real.sqrt (C₁ * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
      ≤ Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2) := by
    have h1 : (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2)
        ≤ ((2 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 2) :=
      Real.rpow_le_rpow (by positivity) hbase hs0
    have h2 : ((2 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 2)
        = (2 + T) ^ ((3 - (d : ℝ) + θ) / 2) * R ^ (2 * ((3 - (d : ℝ) + θ) / 2)) := by
      rw [Real.mul_rpow (by linarith) (by positivity), LatticeProb.rpow_sq_eq hR0.le]
    have h3 : Real.sqrt (C₁ * ((2 + T) ^ ((3 - (d : ℝ) + θ) / 2)
          * R ^ (2 * ((3 - (d : ℝ) + θ) / 2))))
        = Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2) := by
      rw [← mul_assoc, Real.sqrt_mul (by positivity), LatticeProb.sqrt_rpow_eq hR0.le]
      congr 2
      ring
    rw [← h3]
    refine Real.sqrt_le_sqrt ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hC₁.le
  have key := hα R T r r' w w' hr hr' hrT hr'T
  have habs : |R ^ ((d : ℝ) / 2 - 2)| = R ^ ((d : ℝ) / 2 - 2) :=
    abs_of_nonneg (Real.rpow_nonneg hR0.le _)
  rw [habs] at key
  have hexp : (d : ℝ) / 2 - 2 + (3 - (d : ℝ) + θ) / 2 = -((1 - θ) / 2) := by ring
  have hmono : R ^ ((d : ℝ) / 2 - 2) ≤ R ^ (-((1 - θ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hsum0 : (0:ℝ) ≤ ∑ i : Fin d, |R * w i - R * w' i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hrp : (0:ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := Real.rpow_nonneg hR0.le _
  refine le_trans key ?_
  have hstep : R ^ ((d : ℝ) / 2 - 2)
        * (|R ^ 2 * r - R ^ 2 * r'|
          + Real.sqrt (C₁ * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
            * ∑ i : Fin d, |R * w i - R * w' i|)
      ≤ R ^ ((d : ℝ) / 2 - 2)
        * (1 + Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
            * R ^ ((3 - (d : ℝ) + θ) / 2) * (d : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hrp
    have h4 : Real.sqrt (C₁ * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
          * ∑ i : Fin d, |R * w i - R * w' i|
        ≤ Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
            * R ^ ((3 - (d : ℝ) + θ) / 2) * (d : ℝ) := by
      refine mul_le_mul hGle hw hsum0 (by positivity)
    linarith
  refine le_trans hstep ?_
  have hprod : R ^ ((d : ℝ) / 2 - 2) * R ^ ((3 - (d : ℝ) + θ) / 2) = R ^ (-((1 - θ) / 2)) := by
    rw [← Real.rpow_add hR0, hexp]
  have hfin : R ^ ((d : ℝ) / 2 - 2)
        * (1 + Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
            * R ^ ((3 - (d : ℝ) + θ) / 2) * (d : ℝ))
      = R ^ ((d : ℝ) / 2 - 2)
        + (d : ℝ) * Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
          * (R ^ ((d : ℝ) / 2 - 2) * R ^ ((3 - (d : ℝ) + θ) / 2)) := by ring
  rw [hfin, hprod]
  have hdn : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  nlinarith [hmono, hK0, hdn, Real.rpow_nonneg hR0.le (-((1 - θ) / 2))]

/-- The time term of the coarse estimate: the power of the shifted time index,
weighted by `R^{-2e}`, splits into an `R`-decaying constant and the power of the
time increment alone. -/
theorem time_term_bound {R t : ℝ} (hR : 1 ≤ R) (ht : 0 ≤ t) {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) :
    R ^ (-(2 * e)) * (2 + R ^ 2 * t) ^ e ≤ (2:ℝ) ^ e * R ^ (-(2 * e)) + t ^ e := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (0:ℝ) ≤ R ^ 2 := sq_nonneg R
  have h1 : (2 + R ^ 2 * t) ^ e ≤ (2:ℝ) ^ e + (R ^ 2 * t) ^ e :=
    Real.rpow_add_le_add_rpow (by norm_num) (by positivity) he he1
  have h2 : (R ^ 2 * t) ^ e = R ^ (2 * e) * t ^ e := by
    rw [Real.mul_rpow hR2 ht, LatticeProb.rpow_sq_eq hR0.le]
  have h3 : R ^ (-(2 * e)) * (R ^ (2 * e) * t ^ e) = t ^ e := by
    rw [← mul_assoc, ← Real.rpow_add hR0, neg_add_cancel, Real.rpow_zero, one_mul]
  have hpow : (0:ℝ) ≤ R ^ (-(2 * e)) := Real.rpow_nonneg hR0.le _
  calc R ^ (-(2 * e)) * (2 + R ^ 2 * t) ^ e
      ≤ R ^ (-(2 * e)) * ((2:ℝ) ^ e + R ^ (2 * e) * t ^ e) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 hpow
    _ = (2:ℝ) ^ e * R ^ (-(2 * e)) + t ^ e := by
        rw [mul_add, h3]
        ring

/-- The space term of the coarse estimate: the power of the shifted lattice
distance times the power of the time index, weighted by `R^{-(f+2g)}`, splits
into the power of the space increment alone and an `R`-decaying constant. -/
theorem space_term_bound {R u c K : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u) (hc : 0 ≤ c) (hK : 0 ≤ K)
    {f g : ℝ} (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    R ^ (-(f + 2 * g)) * ((R * u + c) ^ f * (K * R ^ 2) ^ g)
      ≤ K ^ g * (u ^ f + c ^ f * R ^ (-f)) := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have h1 : (R * u + c) ^ f ≤ (R * u) ^ f + c ^ f :=
    Real.rpow_add_le_add_rpow (by positivity) hc hf hf1
  have h2 : (R * u) ^ f = R ^ f * u ^ f := Real.mul_rpow hR0.le hu
  have h3 : (K * R ^ 2) ^ g = K ^ g * R ^ (2 * g) := by
    rw [Real.mul_rpow hK (sq_nonneg R), LatticeProb.rpow_sq_eq hR0.le]
  have hg0 : (0:ℝ) ≤ (K * R ^ 2) ^ g := Real.rpow_nonneg (by positivity) _
  have hpow : (0:ℝ) ≤ R ^ (-(f + 2 * g)) := Real.rpow_nonneg hR0.le _
  have e1 : R ^ (-(f + 2 * g)) * R ^ (2 * g) = R ^ (-f) := by
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  have e2 : R ^ (-f) * R ^ f = 1 := by
    rw [← Real.rpow_add hR0, neg_add_cancel, Real.rpow_zero]
  calc R ^ (-(f + 2 * g)) * ((R * u + c) ^ f * (K * R ^ 2) ^ g)
      ≤ R ^ (-(f + 2 * g)) * ((R ^ f * u ^ f + c ^ f) * (K ^ g * R ^ (2 * g))) := by
        rw [← h2, ← h3]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hg0) hpow
    _ = R ^ (-(f + 2 * g)) * R ^ (2 * g) * (R ^ f * u ^ f + c ^ f) * K ^ g := by ring
    _ = R ^ (-f) * (R ^ f * u ^ f + c ^ f) * K ^ g := by rw [e1]
    _ = R ^ (-f) * R ^ f * u ^ f * K ^ g + R ^ (-f) * c ^ f * K ^ g := by ring
    _ = K ^ g * (u ^ f + c ^ f * R ^ (-f)) := by rw [e2]; ring

/-- The `ℓ²` norm of the coefficient increment between two base corners is the
`ℓ²` norm of the increment of the Green kernel, scaled by `R^{d/2-2}`. -/
theorem tsum_interpCoeff_base_sub_sq (hR : 0 < R) (r r' : ℝ)
    (w w' : Sandpile.Continuum.Space d) :
    ∑' y : Site d, (interpCoeff d R (baseTime R r) (basePoint R w) y
        - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2
      = (R ^ ((d : ℝ) / 2 - 2)) ^ 2 * ∑' y : Site d,
          (Sandpile.greenTime d ⌊R ^ 2 * r⌋₊ (fun i => ⌊R * w i⌋) y
            - Sandpile.greenTime d ⌊R ^ 2 * r'⌋₊ (fun i => ⌊R * w' i⌋) y) ^ 2 := by
  rw [← tsum_mul_left]
  refine tsum_congr fun y => ?_
  rw [interpCoeff_basePoint hR, interpCoeff_basePoint hR]
  ring

/-- The increment of the Green kernel in both indices, split into the time
increment at the site `b` and the space increment at the time `a'`. -/
theorem tsum_greenTime_two_index_le (a a' : ℕ) (b b' : Site d) :
    ∑' y : Site d, (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2
      ≤ 2 * (∑' y : Site d,
            (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b y) ^ 2)
        + 2 * (∑' y : Site d,
            (Sandpile.greenTime d a' b y - Sandpile.greenTime d a' b' y) ^ 2) := by
  have h1 := summable_greenTime_sub_sq (d := d) a a' b b
  have h2 := summable_greenTime_sub_sq (d := d) a' a' b b'
  have h3 := summable_greenTime_sub_sq (d := d) a a' b b'
  have hpt : ∀ y : Site d,
      (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2
        ≤ 2 * (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b y) ^ 2
          + 2 * (Sandpile.greenTime d a' b y - Sandpile.greenTime d a' b' y) ^ 2 := by
    intro y
    nlinarith [sq_nonneg ((Sandpile.greenTime d a b y - Sandpile.greenTime d a' b y)
      - (Sandpile.greenTime d a' b y - Sandpile.greenTime d a' b' y))]
  calc ∑' y : Site d, (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2
      ≤ ∑' y : Site d,
          (2 * (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b y) ^ 2
            + 2 * (Sandpile.greenTime d a' b y - Sandpile.greenTime d a' b' y) ^ 2) :=
        h3.tsum_le_tsum hpt ((h1.mul_left 2).add (h2.mul_left 2))
    _ = 2 * (∑' y : Site d,
            (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b y) ^ 2)
          + 2 * (∑' y : Site d,
            (Sandpile.greenTime d a' b y - Sandpile.greenTime d a' b' y) ^ 2) := by
        rw [Summable.tsum_add (h1.mul_left 2) (h2.mul_left 2), tsum_mul_left, tsum_mul_left]

/-- The three-point split of the `ℓ²` increment of the coefficient vector. -/
theorem tsum_interpCoeff_three_point_le (R r r' s s' : ℝ)
    (w w' v v' : Sandpile.Continuum.Space d) :
    ∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2
      ≤ 3 * (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R s v y) ^ 2)
        + 3 * (∑' y : Site d, (interpCoeff d R s v y - interpCoeff d R s' v' y) ^ 2)
        + 3 * (∑' y : Site d, (interpCoeff d R s' v' y - interpCoeff d R r' w' y) ^ 2) := by
  have h1 := summable_interpCoeff_sub_sq (d := d) R r s w v
  have h2 := summable_interpCoeff_sub_sq (d := d) R s s' v v'
  have h3 := summable_interpCoeff_sub_sq (d := d) R s' r' v' w'
  have h0 := summable_interpCoeff_sub_sq (d := d) R r r' w w'
  have hpt : ∀ y : Site d,
      (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2
        ≤ 3 * (interpCoeff d R r w y - interpCoeff d R s v y) ^ 2
          + 3 * (interpCoeff d R s v y - interpCoeff d R s' v' y) ^ 2
          + 3 * (interpCoeff d R s' v' y - interpCoeff d R r' w' y) ^ 2 := by
    intro y
    nlinarith [sq_nonneg ((interpCoeff d R r w y - interpCoeff d R s v y)
        - (interpCoeff d R s v y - interpCoeff d R s' v' y)),
      sq_nonneg ((interpCoeff d R s v y - interpCoeff d R s' v' y)
        - (interpCoeff d R s' v' y - interpCoeff d R r' w' y)),
      sq_nonneg ((interpCoeff d R r w y - interpCoeff d R s v y)
        - (interpCoeff d R s' v' y - interpCoeff d R r' w' y))]
  calc ∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2
      ≤ ∑' y : Site d, (3 * (interpCoeff d R r w y - interpCoeff d R s v y) ^ 2
          + 3 * (interpCoeff d R s v y - interpCoeff d R s' v' y) ^ 2
          + 3 * (interpCoeff d R s' v' y - interpCoeff d R r' w' y) ^ 2) :=
        h0.tsum_le_tsum hpt (((h1.mul_left 3).add (h2.mul_left 3)).add (h3.mul_left 3))
    _ = 3 * (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R s v y) ^ 2)
          + 3 * (∑' y : Site d, (interpCoeff d R s v y - interpCoeff d R s' v' y) ^ 2)
          + 3 * (∑' y : Site d, (interpCoeff d R s' v' y - interpCoeff d R r' w' y) ^ 2) := by
        rw [Summable.tsum_add ((h1.mul_left 3).add (h2.mul_left 3)) (h3.mul_left 3),
          Summable.tsum_add (h1.mul_left 3) (h2.mul_left 3), tsum_mul_left, tsum_mul_left,
          tsum_mul_left]

/-- **The `L²` increment of the Green kernel in BOTH indices.**  The route runs
through the site `(a', b)`: the time increment at the site `b` and the space
increment at the time `a'`. -/
theorem exists_tsum_greenTime_two_index_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a a' : ℕ) (b b' : Site d),
      ∑' y : Site d, (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2
        ≤ C * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2)
              + (Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
                * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)) := by
  obtain ⟨C₂, hC₂, htime⟩ := exists_tsum_greenTime_time_sub_sq_le' hHK hd hd3
  obtain ⟨C₃, hC₃, hspace⟩ := exists_tsum_greenTime_sub_sq_bound hHK hd hd3 hθ0 hθ1
  refine ⟨2 * C₂ + 2 * C₃, by linarith, ?_⟩
  intro a a' b b'
  have h1 := tsum_greenTime_two_index_le (d := d) a a' b b'
  have h2 := htime a a' b
  have h3 := hspace a' b b'
  rw [mul_assoc] at h3
  have hX : (0:ℝ) ≤ (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hL : (0:ℝ) ≤ Sandpile.External.latticeDist b b' + 1 := by
    have := Real.sqrt_nonneg (∑ i : Fin d, ((b i - b' i : ℤ) : ℝ) ^ 2)
    have hlat : Sandpile.External.latticeDist b b'
        = Real.sqrt (∑ i : Fin d, ((b i - b' i : ℤ) : ℝ) ^ 2) := rfl
    rw [hlat]
    linarith
  have hY : (0:ℝ) ≤ (Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
      * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg (by positivity) _)
  have hgoal : (2 * C₂ + 2 * C₃)
      * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2)
        + (Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2))
      = 2 * (C₂ * (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2))
        + 2 * (C₃ * ((Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
            * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)))
        + 2 * (C₂ * ((Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
            * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)))
        + 2 * (C₃ * (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2)) := by ring
  rw [hgoal]
  have e3 : (0:ℝ) ≤ C₂ * ((Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
      * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)) := mul_nonneg hC₂.le hY
  have e4 : (0:ℝ) ≤ C₃ * (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2) := mul_nonneg hC₃.le hX
  linarith

/-- The four terms of the coarse estimate against the three terms of the
modulus, with the constant that dominates every coefficient. -/
theorem sum_coeff_le {A B Dc P1 P2 P3 Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hDc : 0 ≤ Dc)
    (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hP3 : 0 ≤ P3) (hQ : Q ≤ A * P3) :
    Q + P1 + B * (P2 + Dc * P3) ≤ (A + B * (1 + Dc) + 1) * (P1 + P2 + P3) := by
  nlinarith [mul_nonneg hA hP1, mul_nonneg hA hP2, mul_nonneg hB hP1, mul_nonneg hB hP2,
    mul_nonneg hB hP3, mul_nonneg (mul_nonneg hB hDc) hP1, mul_nonneg (mul_nonneg hB hDc) hP2]

/-- **The `ℓ²` increment of the coefficient vector between the two base corners,
with a bound free of `R` apart from one decaying term.**  This is the middle link
of the three-point chain, and it is where the coarse estimate is earned: the
coefficient vector at a base corner is exactly `R^{d/2-2} g_a(b, ·)`, so the
increment is an increment of the Green kernel in its two indices. -/
theorem exists_sqrt_tsum_interpCoeff_base_sub_le
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T →
      Real.sqrt (∑' y : Site d, (interpCoeff d R (baseTime R r) (basePoint R w) y
          - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2)
        ≤ C * (|r - r'| ^ (1 - (d : ℝ) / 4)
              + (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)
              + R ^ (-((1 - θ) / 2))) := by
  obtain ⟨C₄, hC₄, hg⟩ := exists_tsum_greenTime_two_index_bound hHK hd hd3 hθ0 hθ1
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hα0 : (0:ℝ) ≤ 1 - (d : ℝ) / 4 := by linarith
  have hα1 : (1 - (d : ℝ) / 4) ≤ 1 := by linarith
  have hf0 : (0:ℝ) ≤ (1 - θ) / 2 := by linarith
  have hf1 : ((1 - θ) / 2) ≤ 1 := by linarith
  have hgg : (0:ℝ) ≤ (3 - (d : ℝ) + θ) / 4 := by linarith
  have hsC : (0:ℝ) < Real.sqrt C₄ := Real.sqrt_pos.mpr hC₄
  have hTpos : (0:ℝ) < 1 + T := by linarith
  refine ⟨Real.sqrt C₄ * ((2:ℝ) ^ (1 - (d : ℝ) / 4)
      + (1 + T) ^ ((3 - (d : ℝ) + θ) / 4) * (1 + ((d : ℝ) + 1) ^ ((1 - θ) / 2)) + 1),
    by positivity, ?_⟩
  intro R hR r r' w w' hr hr' hrT hr'T
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hRe : (0:ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := Real.rpow_nonneg hR0.le _
  have hΔt : (0:ℝ) ≤ |r - r'| := abs_nonneg _
  have hΔs : (0:ℝ) ≤ ∑ i : Fin d, |w i - w' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [tsum_interpCoeff_base_sub_sq hR0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hRe]
  set a : ℕ := ⌊R ^ 2 * r⌋₊ with ha
  set a' : ℕ := ⌊R ^ 2 * r'⌋₊ with ha'
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set b' : Site d := fun i => ⌊R * w' i⌋ with hb'
  have hLnn : (0:ℝ) ≤ Sandpile.External.latticeDist b b' :=
    Real.sqrt_nonneg (∑ i : Fin d, ((b i - b' i : ℤ) : ℝ) ^ 2)
  have hXnn : (0:ℝ) ≤ (1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hYnn : (0:ℝ) ≤ (Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
      * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)
  -- the square root of the two-index bound
  have hsqrtS : Real.sqrt (∑' y : Site d,
        (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2)
      ≤ Real.sqrt C₄ * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4)
          + (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
            * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4)) := by
    have h1 : Real.sqrt (∑' y : Site d,
          (Sandpile.greenTime d a b y - Sandpile.greenTime d a' b' y) ^ 2)
        ≤ Real.sqrt (C₄ * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2)
            + (Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
              * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2))) :=
      Real.sqrt_le_sqrt (hg a a' b b')
    refine le_trans h1 ?_
    rw [Real.sqrt_mul hC₄.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    refine le_trans (sqrt_add_le hXnn hYnn) ?_
    have e1 : Real.sqrt ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (2 - (d : ℝ) / 2))
        = (1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4) := by
      rw [LatticeProb.sqrt_rpow_eq (by positivity)]
      congr 1
      ring
    have e2 : Real.sqrt ((Sandpile.External.latticeDist b b' + 1) ^ (1 - θ)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2))
        = (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4) := by
      rw [Real.sqrt_mul (Real.rpow_nonneg (by linarith) _), LatticeProb.sqrt_rpow_eq (by linarith),
        LatticeProb.sqrt_rpow_eq (by positivity)]
      congr 2
      ring
    rw [e1, e2]
  have hAle : (1 : ℝ) + |(a : ℝ) - (a' : ℝ)| ≤ 2 + R ^ 2 * |r - r'| := by
    have h := abs_natFloor_sub_le (u := R ^ 2 * r) (v := R ^ 2 * r')
      (by positivity) (by positivity)
    have habs : |R ^ 2 * r - R ^ 2 * r'| = R ^ 2 * |r - r'| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg R)]
    rw [habs] at h
    rw [ha, ha']
    linarith
  have hXle : (1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4)
      ≤ (2 + R ^ 2 * |r - r'|) ^ (1 - (d : ℝ) / 4) :=
    Real.rpow_le_rpow (by positivity) hAle hα0
  have hLle : Sandpile.External.latticeDist b b' + 1
      ≤ R * (∑ i : Fin d, |w i - w' i|) + ((d : ℝ) + 1) := by
    have h := latticeDist_baseSite_le (R := R) hR0.le w w'
    rw [hb, hb']
    linarith
  have hA'le : 1 + (a' : ℝ) ≤ (1 + T) * R ^ 2 := by
    have h1 : ((a' : ℕ) : ℝ) ≤ R ^ 2 * r' := by rw [ha']; exact Nat.floor_le (by positivity)
    have h2 : R ^ 2 * r' ≤ R ^ 2 * T := mul_le_mul_of_nonneg_left hr'T (sq_nonneg R)
    nlinarith
  have hYle : (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
        * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4)
      ≤ (R * (∑ i : Fin d, |w i - w' i|) + ((d : ℝ) + 1)) ^ ((1 - θ) / 2)
        * ((1 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 4) :=
    mul_le_mul (Real.rpow_le_rpow (by linarith) hLle hf0)
      (Real.rpow_le_rpow (by positivity) hA'le hgg)
      (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hA1 := time_term_bound (R := R) (t := |r - r'|) hR hΔt (e := 1 - (d : ℝ) / 4) hα0 hα1
  have he2 : -(2 * (1 - (d : ℝ) / 4)) = (d : ℝ) / 2 - 2 := by ring
  rw [he2] at hA1
  have hA2 := space_term_bound (R := R) (u := ∑ i : Fin d, |w i - w' i|) (c := (d : ℝ) + 1)
    (K := 1 + T) hR hΔs (by positivity) (by linarith)
    (f := (1 - θ) / 2) (g := (3 - (d : ℝ) + θ) / 4) hf0 hf1
  have he3 : -((1 - θ) / 2 + 2 * ((3 - (d : ℝ) + θ) / 4)) = (d : ℝ) / 2 - 2 := by ring
  rw [he3] at hA2
  have hRf : R ^ ((d : ℝ) / 2 - 2) ≤ R ^ (-((1 - θ) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hP1 : (0:ℝ) ≤ |r - r'| ^ (1 - (d : ℝ) / 4) := Real.rpow_nonneg hΔt _
  have hP2 : (0:ℝ) ≤ (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2) := Real.rpow_nonneg hΔs _
  have hP3 : (0:ℝ) ≤ R ^ (-((1 - θ) / 2)) := Real.rpow_nonneg hR0.le _
  have hAc : (0:ℝ) ≤ (2:ℝ) ^ (1 - (d : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
  have hBg : (0:ℝ) ≤ (1 + T) ^ ((3 - (d : ℝ) + θ) / 4) := Real.rpow_nonneg (by linarith) _
  have hDc : (0:ℝ) ≤ ((d : ℝ) + 1) ^ ((1 - θ) / 2) := Real.rpow_nonneg (by linarith) _
  have hstep1 : R ^ ((d : ℝ) / 2 - 2) * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4)
        + (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4))
      ≤ R ^ ((d : ℝ) / 2 - 2) * ((2 + R ^ 2 * |r - r'|) ^ (1 - (d : ℝ) / 4)
        + (R * (∑ i : Fin d, |w i - w' i|) + ((d : ℝ) + 1)) ^ ((1 - θ) / 2)
          * ((1 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 4)) :=
    mul_le_mul_of_nonneg_left (add_le_add hXle hYle) hRe
  have hstep2 : R ^ ((d : ℝ) / 2 - 2) * ((2 + R ^ 2 * |r - r'|) ^ (1 - (d : ℝ) / 4)
        + (R * (∑ i : Fin d, |w i - w' i|) + ((d : ℝ) + 1)) ^ ((1 - θ) / 2)
          * ((1 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 4))
      ≤ ((2:ℝ) ^ (1 - (d : ℝ) / 4) * R ^ ((d : ℝ) / 2 - 2) + |r - r'| ^ (1 - (d : ℝ) / 4))
        + (1 + T) ^ ((3 - (d : ℝ) + θ) / 4)
          * ((∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)
            + ((d : ℝ) + 1) ^ ((1 - θ) / 2) * R ^ (-((1 - θ) / 2))) := by
    rw [mul_add]
    exact add_le_add hA1 hA2
  refine le_trans (mul_le_mul_of_nonneg_left hsqrtS hRe) ?_
  have hcomb : R ^ ((d : ℝ) / 2 - 2) * (Real.sqrt C₄ * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4)
        + (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4)))
      = Real.sqrt C₄ * (R ^ ((d : ℝ) / 2 - 2) * ((1 + |(a : ℝ) - (a' : ℝ)|) ^ (1 - (d : ℝ) / 4)
        + (Sandpile.External.latticeDist b b' + 1) ^ ((1 - θ) / 2)
          * (1 + (a' : ℝ)) ^ ((3 - (d : ℝ) + θ) / 4))) := by ring
  rw [hcomb]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hstep1 hstep2) (Real.sqrt_nonneg _)) ?_
  rw [mul_assoc (Real.sqrt C₄)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hRfm : (2:ℝ) ^ (1 - (d : ℝ) / 4) * R ^ ((d : ℝ) / 2 - 2)
      ≤ (2:ℝ) ^ (1 - (d : ℝ) / 4) * R ^ (-((1 - θ) / 2)) :=
    mul_le_mul_of_nonneg_left hRf hAc
  exact sum_coeff_le hAc hBg hDc hP1 hP2 hP3 hRfm

theorem abs_sub_mul_baseTime' (hR : 0 < R) {r : ℝ} (hr : 0 ≤ r) :
    |R ^ 2 * baseTime R r - R ^ 2 * r| ≤ 1 := by
  rw [abs_sub_comm]
  exact abs_sub_mul_baseTime hR hr

theorem sum_abs_sub_mul_basePoint' (hR : 0 < R) (w : Sandpile.Continuum.Space d) :
    ∑ i : Fin d, |R * basePoint R w i - R * w i| ≤ (d : ℝ) := by
  have hcongr : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      |R * basePoint R w i - R * w i| = |R * w i - R * basePoint R w i| :=
    fun i _ => abs_sub_comm _ _
  rw [Finset.sum_congr rfl hcongr]
  exact sum_abs_sub_mul_basePoint hR w

/-- **The `ℓ²` modulus of the coefficient vector ABOVE the mesh spacing.**  The
three-point chain through the base corners of the two cells: the two outer links
are single-cell increments, priced by `R^{-(1-θ)/2}`, and the middle link is an
increment of the Green kernel in its two indices, priced by the increments of
the point alone.  Every constant is free of `R`. -/
theorem exists_sqrt_tsum_interpCoeff_sub_coarse
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T →
      Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        ≤ C * (|r - r'| ^ (1 - (d : ℝ) / 4)
              + (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)
              + R ^ (-((1 - θ) / 2))) := by
  obtain ⟨C₅, hC₅, hone⟩ := exists_sqrt_tsum_interpCoeff_one_cell hHK hd hd3 hθ0 hθ1 T hT
  obtain ⟨C₆, hC₆, hmid⟩ := exists_sqrt_tsum_interpCoeff_base_sub_le hHK hd hd3 hθ0 hθ1 T hT
  refine ⟨Real.sqrt 3 * (2 * C₅ + C₆),
    mul_pos (Real.sqrt_pos.mpr (by norm_num)) (by linarith), ?_⟩
  intro R hR r r' w w' hr hr' hrT hr'T
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hbr : baseTime R r ≤ T := le_trans (baseTime_le hR0 hr) hrT
  have hbr' : baseTime R r' ≤ T := le_trans (baseTime_le hR0 hr') hr'T
  have hA := hone R hR r (baseTime R r) w (basePoint R w) hr (baseTime_nonneg R r) hrT hbr
    (abs_sub_mul_baseTime hR0 hr) (sum_abs_sub_mul_basePoint hR0 w)
  have hB := hmid R hR r r' w w' hr hr' hrT hr'T
  have hC := hone R hR (baseTime R r') r' (basePoint R w') w' (baseTime_nonneg R r') hr' hbr' hr'T
    (abs_sub_mul_baseTime' hR0 hr') (sum_abs_sub_mul_basePoint' hR0 w')
  have hsplit := tsum_interpCoeff_three_point_le (d := d) R r r' (baseTime R r) (baseTime R r')
    w w' (basePoint R w) (basePoint R w')
  have hnnA : (0:ℝ) ≤ ∑' y : Site d,
      (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2 :=
    tsum_nonneg fun y => sq_nonneg _
  have hnnB : (0:ℝ) ≤ ∑' y : Site d,
      (interpCoeff d R (baseTime R r) (basePoint R w) y
        - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2 :=
    tsum_nonneg fun y => sq_nonneg _
  have hnnC : (0:ℝ) ≤ ∑' y : Site d,
      (interpCoeff d R (baseTime R r') (basePoint R w') y - interpCoeff d R r' w' y) ^ 2 :=
    tsum_nonneg fun y => sq_nonneg _
  have hsq3 : Real.sqrt (3 * (∑' y : Site d,
        (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2)
      + 3 * (∑' y : Site d,
        (interpCoeff d R (baseTime R r) (basePoint R w) y
          - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2)
      + 3 * (∑' y : Site d,
        (interpCoeff d R (baseTime R r') (basePoint R w') y - interpCoeff d R r' w' y) ^ 2))
      ≤ Real.sqrt 3 * (Real.sqrt (∑' y : Site d,
            (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2)
          + Real.sqrt (∑' y : Site d,
            (interpCoeff d R (baseTime R r) (basePoint R w) y
              - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2)
          + Real.sqrt (∑' y : Site d,
            (interpCoeff d R (baseTime R r') (basePoint R w') y
              - interpCoeff d R r' w' y) ^ 2)) := by
    have h1 := sqrt_add_le (a := 3 * (∑' y : Site d,
        (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2)
      + 3 * (∑' y : Site d,
        (interpCoeff d R (baseTime R r) (basePoint R w) y
          - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2))
      (b := 3 * (∑' y : Site d,
        (interpCoeff d R (baseTime R r') (basePoint R w') y - interpCoeff d R r' w' y) ^ 2))
      (by positivity) (by positivity)
    have h2 := sqrt_add_le (a := 3 * (∑' y : Site d,
        (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2))
      (b := 3 * (∑' y : Site d,
        (interpCoeff d R (baseTime R r) (basePoint R w) y
          - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2))
      (by positivity) (by positivity)
    have e1 : ∀ x : ℝ, Real.sqrt (3 * x) = Real.sqrt 3 * Real.sqrt x :=
      fun x => Real.sqrt_mul (by norm_num) x
    have hgoal : Real.sqrt 3 * (Real.sqrt (∑' y : Site d,
            (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2)
          + Real.sqrt (∑' y : Site d,
            (interpCoeff d R (baseTime R r) (basePoint R w) y
              - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2)
          + Real.sqrt (∑' y : Site d,
            (interpCoeff d R (baseTime R r') (basePoint R w') y
              - interpCoeff d R r' w' y) ^ 2))
        = Real.sqrt (3 * (∑' y : Site d,
            (interpCoeff d R r w y - interpCoeff d R (baseTime R r) (basePoint R w) y) ^ 2))
          + Real.sqrt (3 * (∑' y : Site d,
            (interpCoeff d R (baseTime R r) (basePoint R w) y
              - interpCoeff d R (baseTime R r') (basePoint R w') y) ^ 2))
          + Real.sqrt (3 * (∑' y : Site d,
            (interpCoeff d R (baseTime R r') (basePoint R w') y
              - interpCoeff d R r' w' y) ^ 2)) := by
      rw [e1, e1, e1]
      ring
    rw [hgoal]
    linarith
  refine le_trans (le_trans (Real.sqrt_le_sqrt hsplit) hsq3) ?_
  have hP1 : (0:ℝ) ≤ |r - r'| ^ (1 - (d : ℝ) / 4) := Real.rpow_nonneg (abs_nonneg _) _
  have hP2 : (0:ℝ) ≤ (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2) :=
    Real.rpow_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) _
  have hP3 : (0:ℝ) ≤ R ^ (-((1 - θ) / 2)) := Real.rpow_nonneg hR0.le _
  have hs3 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hs3
  nlinarith [hA, hB, hC, hP1, hP2, hP3, hC₅.le, hC₆.le]

theorem sum_abs_mul_sub {R : ℝ} (hR : 0 ≤ R) (w w' : Sandpile.Continuum.Space d) :
    ∑ i : Fin d, |R * w i - R * w' i| = R * ∑ i : Fin d, |w i - w' i| := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hR]

/-- **The `ℓ²` modulus of the coefficient vector BELOW the mesh spacing, with a
constant free of `R`.**  When the two points lie within one mesh cell, the
estimate of `ContCoeffL2` already has the exponents of the finished modulus: the
factor `R^{d/2}` of the time direction is `(R^2|Δr|)^{d/4}`, and the factor
`R^{(1+θ)/2}` of the space direction is `(R‖Δw‖₁)^{(1+θ)/2}`, and both of those
are at most one below the mesh spacing. -/
theorem exists_sqrt_tsum_interpCoeff_sub_fine
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T →
      R ^ 2 * (|r - r'| + ∑ i : Fin d, |w i - w' i|) ≤ 1 →
      Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        ≤ C * (|r - r'| ^ (1 - (d : ℝ) / 4)
              + (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)) := by
  obtain ⟨C₁, hC₁, hα⟩ := exists_sqrt_tsum_interpCoeff_sub_le hHK hd hd3 hθ0 hθ1
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hs0 : (0:ℝ) ≤ (3 - (d : ℝ) + θ) / 2 := by linarith
  have hK0 : (0:ℝ) ≤ Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) := Real.sqrt_nonneg _
  refine ⟨1 + Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)), by positivity, ?_⟩
  intro R hR r r' w w' hr hr' hrT hr'T hfine
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hR2 : (1:ℝ) ≤ R ^ 2 := by nlinarith
  have hΔt : (0:ℝ) ≤ |r - r'| := abs_nonneg _
  have hΔs : (0:ℝ) ≤ ∑ i : Fin d, |w i - w' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hbase : (2:ℝ) + R ^ 2 * T ≤ (2 + T) * R ^ 2 := by nlinarith
  have hGle : Real.sqrt (C₁ * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
      ≤ Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2) := by
    have h1 : (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2)
        ≤ ((2 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 2) :=
      Real.rpow_le_rpow (by positivity) hbase hs0
    have h2 : ((2 + T) * R ^ 2) ^ ((3 - (d : ℝ) + θ) / 2)
        = (2 + T) ^ ((3 - (d : ℝ) + θ) / 2) * R ^ (2 * ((3 - (d : ℝ) + θ) / 2)) := by
      rw [Real.mul_rpow (by linarith) (by positivity), LatticeProb.rpow_sq_eq hR0.le]
    have h3 : Real.sqrt (C₁ * ((2 + T) ^ ((3 - (d : ℝ) + θ) / 2)
          * R ^ (2 * ((3 - (d : ℝ) + θ) / 2))))
        = Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2) := by
      rw [← mul_assoc, Real.sqrt_mul (by positivity), LatticeProb.sqrt_rpow_eq hR0.le]
      congr 2
      ring
    rw [← h3]
    refine Real.sqrt_le_sqrt ?_
    rw [← h2]
    exact mul_le_mul_of_nonneg_left h1 hC₁.le
  have key := hα R T r r' w w' hr hr' hrT hr'T
  rw [abs_of_nonneg (Real.rpow_nonneg hR0.le ((d : ℝ) / 2 - 2)),
    sum_abs_mul_sub hR0.le] at key
  have habs : |R ^ 2 * r - R ^ 2 * r'| = R ^ 2 * |r - r'| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg R)]
  rw [habs] at key
  have hRe : (0:ℝ) ≤ R ^ ((d : ℝ) / 2 - 2) := Real.rpow_nonneg hR0.le _
  -- replace the coefficient of the space term
  have hstep1 : R ^ ((d : ℝ) / 2 - 2)
        * (R ^ 2 * |r - r'|
          + Real.sqrt (C₁ * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
            * (R * ∑ i : Fin d, |w i - w' i|))
      ≤ R ^ ((d : ℝ) / 2 - 2)
        * (R ^ 2 * |r - r'|
          + Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2)
            * (R * ∑ i : Fin d, |w i - w' i|)) := by
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hRe
    exact mul_le_mul_of_nonneg_right hGle (by positivity)
  -- the two exponent identities
  have het : R ^ ((d : ℝ) / 2 - 2) * (R ^ 2 * |r - r'|)
      = (R ^ 2) ^ (1 - (1 - (d : ℝ) / 4)) * |r - r'| := by
    rw [LatticeProb.rpow_sq_eq hR0.le]
    rw [show (2:ℝ) * (1 - (1 - (d : ℝ) / 4)) = (d : ℝ) / 2 by ring]
    have : R ^ ((d : ℝ) / 2) = R ^ ((d : ℝ) / 2 - 2) * R ^ (2:ℝ) := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    rw [this]
    have h2 : R ^ (2:ℝ) = R ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    ring
  have hes : R ^ ((d : ℝ) / 2 - 2)
        * (Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2)
          * (R * ∑ i : Fin d, |w i - w' i|))
      = Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
        * (R ^ (1 - (1 - θ) / 2) * ∑ i : Fin d, |w i - w' i|) := by
    have h1 : R ^ ((d : ℝ) / 2 - 2) * R ^ ((3 - (d : ℝ) + θ) / 2) = R ^ (-((1 - θ) / 2)) := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    have h2 : R ^ (-((1 - θ) / 2)) * R = R ^ (1 - (1 - θ) / 2) := by
      have hR1 : R = R ^ (1:ℝ) := (Real.rpow_one R).symm
      nth_rewrite 2 [hR1]
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    calc R ^ ((d : ℝ) / 2 - 2)
          * (Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2)) * R ^ ((3 - (d : ℝ) + θ) / 2)
            * (R * ∑ i : Fin d, |w i - w' i|))
        = Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
            * ((R ^ ((d : ℝ) / 2 - 2) * R ^ ((3 - (d : ℝ) + θ) / 2)) * R
              * ∑ i : Fin d, |w i - w' i|) := by ring
      _ = Real.sqrt (C₁ * (2 + T) ^ ((3 - (d : ℝ) + θ) / 2))
            * (R ^ (1 - (1 - θ) / 2) * ∑ i : Fin d, |w i - w' i|) := by rw [h1, h2]
  have hsplit1 : (R ^ 2) ^ (1 - (1 - (d : ℝ) / 4)) * |r - r'| ≤ |r - r'| ^ (1 - (d : ℝ) / 4) := by
    refine rpow_one_sub_mul_le (sq_nonneg R) hΔt (by linarith) ?_
    nlinarith
  have hsplit2 : R ^ (1 - (1 - θ) / 2) * (∑ i : Fin d, |w i - w' i|)
      ≤ (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2) := by
    refine rpow_one_sub_mul_le hR0.le hΔs (by linarith) ?_
    nlinarith
  refine le_trans key (le_trans hstep1 ?_)
  rw [mul_add, het, hes]
  have hP1 : (0:ℝ) ≤ |r - r'| ^ (1 - (d : ℝ) / 4) := Real.rpow_nonneg hΔt _
  have hP2 : (0:ℝ) ≤ (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2) := Real.rpow_nonneg hΔs _
  nlinarith [hsplit1, hsplit2, hK0, hP1, hP2]

/-- Above the mesh spacing the decaying factor `R^{-f}` is itself a power of the
distance. -/
theorem rpow_neg_le_rpow_of_one_le_mul {R δ f : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ) (hf : 0 ≤ f)
    (h : 1 ≤ R ^ 2 * δ) : R ^ (-f) ≤ δ ^ (f / 2) := by
  have h1 : (1:ℝ) ≤ (R ^ 2 * δ) ^ (f / 2) := by
    have hx := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) h (by linarith : (0:ℝ) ≤ f / 2)
    rwa [Real.one_rpow] at hx
  have h2 : (R ^ 2 * δ) ^ (f / 2) = R ^ f * δ ^ (f / 2) := by
    rw [Real.mul_rpow (sq_nonneg R) hδ, LatticeProb.rpow_sq_eq hR.le,
      show (2:ℝ) * (f / 2) = f by ring]
  have h3 : R ^ (-f) * R ^ f = 1 := by
    rw [← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  have h4 : (0:ℝ) ≤ R ^ (-f) := Real.rpow_nonneg hR.le _
  calc R ^ (-f) = R ^ (-f) * 1 := (mul_one _).symm
    _ ≤ R ^ (-f) * (R ^ 2 * δ) ^ (f / 2) := mul_le_mul_of_nonneg_left h1 h4
    _ = R ^ (-f) * R ^ f * δ ^ (f / 2) := by rw [h2]; ring
    _ = δ ^ (f / 2) := by rw [h3, one_mul]

/-- **The `ℓ²` modulus of the coefficient vector of the interpolated field, with
a single exponent and a constant free of `R`.**  Below the mesh spacing the
estimate of `ContCoeffL2` supplies it, above the mesh spacing the three-point
chain does, and the crossover is at `R^{-2}`.  The exponent is
`β = min(1 - d/4, (1-θ)/4)`, which is positive for `d ≤ 3` and `θ < 1`. -/
theorem exists_sqrt_tsum_interpCoeff_sub_modulus
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (T S : ℝ) (hT : 0 ≤ T) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ (r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T → (∑ i : Fin d, |w i - w' i|) ≤ S →
      Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        ≤ C * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
            ^ (min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := by
  obtain ⟨C₇, hC₇, hcoarse⟩ :=
    exists_sqrt_tsum_interpCoeff_sub_coarse hHK hd hd3 hθ0 hθ1.le T hT
  obtain ⟨C₈, hC₈, hfine⟩ := exists_sqrt_tsum_interpCoeff_sub_fine hHK hd hd3 hθ0 hθ1.le T hT
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hβ0 : (0:ℝ) < min (1 - (d : ℝ) / 4) ((1 - θ) / 4) :=
    lt_min (by linarith) (by linarith)
  have hβα : min (1 - (d : ℝ) / 4) ((1 - θ) / 4) ≤ 1 - (d : ℝ) / 4 := min_le_left _ _
  have hβf : min (1 - (d : ℝ) / 4) ((1 - θ) / 4) ≤ (1 - θ) / 2 :=
    le_trans (min_le_right _ _) (by linarith)
  have hβh : min (1 - (d : ℝ) / 4) ((1 - θ) / 4) ≤ ((1 - θ) / 2) / 2 :=
    le_trans (min_le_right _ _) (by linarith)
  have hD : (0:ℝ) ≤ T + S + 1 := by linarith
  have hK1 : (0:ℝ) ≤ (T + S + 1)
      ^ ((1 - (d : ℝ) / 4) - min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := Real.rpow_nonneg hD _
  have hK2 : (0:ℝ) ≤ (T + S + 1)
      ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := Real.rpow_nonneg hD _
  have hK3 : (0:ℝ) ≤ (T + S + 1)
      ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4)) := Real.rpow_nonneg hD _
  refine ⟨(C₇ + C₈) * ((T + S + 1) ^ ((1 - (d : ℝ) / 4)
        - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
      + (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
      + (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))) + 1,
    by positivity, ?_⟩
  intro R hR r r' w w' hr hr' hrT hr'T hws
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hΔt : (0:ℝ) ≤ |r - r'| := abs_nonneg _
  have hΔs : (0:ℝ) ≤ ∑ i : Fin d, |w i - w' i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hΔtT : |r - r'| ≤ T := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hδ0 : (0:ℝ) ≤ |r - r'| + ∑ i : Fin d, |w i - w' i| := by linarith
  have hδD : |r - r'| + (∑ i : Fin d, |w i - w' i|) ≤ T + S + 1 := by linarith
  have hδβ : (0:ℝ) ≤ (|r - r'| + ∑ i : Fin d, |w i - w' i|)
      ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := Real.rpow_nonneg hδ0 _
  -- the first two terms, in both regimes
  have hP1 : |r - r'| ^ (1 - (d : ℝ) / 4)
      ≤ (T + S + 1) ^ ((1 - (d : ℝ) / 4) - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        * (|r - r'| + ∑ i : Fin d, |w i - w' i|) ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by
    refine le_trans (rpow_le_mul_rpow_of_le (D := T + S + 1) hΔt (by linarith) hβ0 hβα) ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hΔt (by linarith) hβ0.le) hK1
  have hP2 : (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)
      ≤ (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        * (|r - r'| + ∑ i : Fin d, |w i - w' i|) ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by
    refine le_trans (rpow_le_mul_rpow_of_le (D := T + S + 1) hΔs (by linarith) hβ0 hβf) ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hΔs (by linarith) hβ0.le) hK2
  rcases le_or_gt 1 (R ^ 2 * (|r - r'| + ∑ i : Fin d, |w i - w' i|)) with hcase | hcase
  · have hmain := hcoarse R hR r r' w w' hr hr' hrT hr'T
    have hP3 : R ^ (-((1 - θ) / 2))
        ≤ (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
          * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
            ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by
      refine le_trans (rpow_neg_le_rpow_of_one_le_mul hR0 hδ0 (by linarith) hcase) ?_
      exact rpow_le_mul_rpow_of_le hδ0 hδD hβ0 hβh
    refine le_trans hmain ?_
    have hsum : |r - r'| ^ (1 - (d : ℝ) / 4)
          + (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2) + R ^ (-((1 - θ) / 2))
        ≤ ((T + S + 1) ^ ((1 - (d : ℝ) / 4) - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
            + (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
            + (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4)))
          * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
            ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by
      rw [add_mul, add_mul]
      linarith
    refine le_trans (mul_le_mul_of_nonneg_left hsum hC₇.le) ?_
    have hprod : (0:ℝ) ≤ C₈ * ((T + S + 1) ^ ((1 - (d : ℝ) / 4)
          - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        + (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        + (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))) := by
      positivity
    nlinarith [hδβ, hprod]
  · have hmain := hfine R hR r r' w w' hr hr' hrT hr'T hcase.le
    refine le_trans hmain ?_
    have hsum : |r - r'| ^ (1 - (d : ℝ) / 4)
          + (∑ i : Fin d, |w i - w' i|) ^ ((1 - θ) / 2)
        ≤ ((T + S + 1) ^ ((1 - (d : ℝ) / 4) - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
            + (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
            + (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4)))
          * (|r - r'| + ∑ i : Fin d, |w i - w' i|)
            ^ min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := by
      rw [add_mul, add_mul]
      nlinarith [hP1, hP2, mul_nonneg hK3 hδβ]
    refine le_trans (mul_le_mul_of_nonneg_left hsum hC₈.le) ?_
    have hprod : (0:ℝ) ≤ C₇ * ((T + S + 1) ^ ((1 - (d : ℝ) / 4)
          - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        + (T + S + 1) ^ ((1 - θ) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
        + (T + S + 1) ^ (((1 - θ) / 2) / 2 - min (1 - (d : ℝ) / 4) ((1 - θ) / 4))) := by
      positivity
    nlinarith [hδβ, hprod]

end Sandpile.Support
