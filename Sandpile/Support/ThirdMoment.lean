import Sandpile.Support.EventBridge

/-!
# The third absolute moment of the standardized coefficients

`sandpile.tex:1784-1790` bounds `∑_x |a(x)|³` by `m^{1/2}` times the sum over the scales of
`∑_x |a_j(x)|³`, and each of those by the supremum of the Green kernel against its own square
sum. The first step is the `ℓ²`-`ℓ³` comparison `(∑ c_j²)³ ≤ m (∑ c_j³)²` (`sum_sq_cube_le`),
which follows from two applications of the Cauchy-Schwarz inequality after the substitution
`c_j = e_j²`, so that every exponent is a natural number. The variance of the one-site law
cancels out of the whole estimate, as `third_moment_bound` shows.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.External.BerryEsseen

namespace Sandpile

variable {d : ℕ}

/-- **The `ℓ²`-`ℓ³` comparison.** For nonnegative reals `c_j`, `(∑ c_j²)³ ≤ m (∑ c_j³)²`: apply
Cauchy-Schwarz twice after substituting `c_j = e_j²` so that every exponent is a natural number,
first to compare `∑ e_j⁴` with `√(∑ e_j²) · √(∑ e_j⁶)` and then to compare `∑ e_j²` with
`√m · √(∑ e_j⁴)`. -/
theorem sum_sq_cube_le {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∑ j, c j ^ 2) ^ 3 ≤ (m : ℝ) * (∑ j, c j ^ 3) ^ 2 := by
  set e : Fin m → ℝ := fun j => Real.sqrt (c j) with hedef
  have he : ∀ j, e j ^ 2 = c j := fun j => Real.sq_sqrt (hc j)
  have h2 : (∑ j, c j ^ 2) = ∑ j, e j ^ 4 :=
    Finset.sum_congr rfl fun j _ => by rw [← he j]; ring
  have h3 : (∑ j, c j ^ 3) = ∑ j, e j ^ 6 :=
    Finset.sum_congr rfl fun j _ => by rw [← he j]; ring
  have hA : (0 : ℝ) ≤ ∑ j, e j ^ 4 := Finset.sum_nonneg fun j _ => by positivity
  have hB : (0 : ℝ) ≤ ∑ j, e j ^ 6 := Finset.sum_nonneg fun j _ => by positivity
  have hC : (0 : ℝ) ≤ ∑ j, e j ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hcs1 : (∑ j, e j ^ 4) ^ 2 ≤ (∑ j, e j ^ 2) * (∑ j, e j ^ 6) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => e j) (fun j => e j ^ 3)
    have hl : ∀ j : Fin m, e j * e j ^ 3 = e j ^ 4 := fun j => by ring
    have hr : ∀ j : Fin m, (e j ^ 3) ^ 2 = e j ^ 6 := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hl j), Finset.sum_congr rfl (fun j _ => hr j)] at h
    exact h
  have hcs2 : (∑ j, e j ^ 2) ^ 2 ≤ (m : ℝ) * (∑ j, e j ^ 4) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1 : ℝ))
      (fun j => e j ^ 2)
    have hl : ∀ j : Fin m, (1 : ℝ) * e j ^ 2 = e j ^ 2 := fun j => by ring
    have hr : ∀ j : Fin m, (e j ^ 2) ^ 2 = e j ^ 4 := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hl j), Finset.sum_congr rfl (fun j _ => hr j)] at h
    simpa using h
  rw [h2, h3]
  rcases eq_or_lt_of_le hA with hzero | hpos
  · rw [← hzero]
    have : (0 : ℝ) ≤ (m : ℝ) * (∑ j, e j ^ 6) ^ 2 := by positivity
    simpa using this
  · have hfour : (∑ j, e j ^ 4) ^ 4 ≤ (m : ℝ) * (∑ j, e j ^ 4) * (∑ j, e j ^ 6) ^ 2 := by
      have h1 : ((∑ j, e j ^ 4) ^ 2) ^ 2
          ≤ ((∑ j, e j ^ 2) * (∑ j, e j ^ 6)) ^ 2 := by
        have hq : (0 : ℝ) ≤ (∑ j, e j ^ 4) ^ 2 := sq_nonneg _
        nlinarith [hcs1, hq]
      have h2' : ((∑ j, e j ^ 2) * (∑ j, e j ^ 6)) ^ 2
          = (∑ j, e j ^ 2) ^ 2 * (∑ j, e j ^ 6) ^ 2 := by ring
      nlinarith [h1, h2', hcs2, sq_nonneg (∑ j, e j ^ 6)]
    nlinarith [hfour, hpos]

/-- The cube sum `∑_i g_n(x, siteEnum s i)³` over an enumeration of a finite set `s` containing
`boxFinset x n` equals the full infinite sum `∑'_z g_n(x, z)³`, since `greenTime` vanishes outside
the box `boxFinset x n` and hence outside `s`. -/
theorem sum_siteEnum_greenTime_cube {s : Finset (Site d)} {n : ℕ} {x : Site d}
    (hsub : boxFinset x n ⊆ s) :
    ∑ i : Fin s.card, greenTime d n x (siteEnum s i) ^ 3
      = ∑' z : Site d, greenTime d n x z ^ 3 := by
  classical
  rw [sum_siteEnum s fun z => greenTime d n x z ^ 3]
  refine (tsum_eq_sum ?_).symm
  intro z hz
  have hg : greenTime d n x z = 0 := by
    by_contra hne
    exact hz (hsub (mem_boxFinset (greenTime_support n x hne)))
  simp [hg]

/-- The Green cube sum `∑'_x g_n(0,x)³` is bounded by the supremum `M` of the Green kernel times
`greenSq d n = ∑'_x g_n(0,x)²`: bound each `g_n(0,x)³ ≤ M · g_n(0,x)²` termwise and sum over the
finite support box. -/
theorem tsum_greenTime_cube_le (n : ℕ) (M : ℝ) (hM : ∀ x : Site d, greenTime d n 0 x ≤ M) :
    (∑' x : Site d, greenTime d n 0 x ^ 3) ≤ M * greenSq d n := by
  rw [greenSq, tsum_greenTime_sq_eq_sum]
  have hcube : (∑' x : Site d, greenTime d n 0 x ^ 3)
      = ∑ x ∈ boxFinset (0 : Site d) n, greenTime d n 0 x ^ 3 := by
    refine tsum_eq_sum fun z hz => ?_
    have hg : greenTime d n 0 z = 0 := by
      by_contra hne
      exact hz (mem_boxFinset (greenTime_support n 0 hne))
    simp [hg]
  rw [hcube, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h0 := greenTime_nonneg n (0 : Site d) x
  nlinarith [hM x, sq_nonneg (greenTime d n 0 x)]

/-- The cube of a coefficient's Euclidean norm, `coeffNorm a i ^ 3`, is bounded by `√m` times the
sum of the cubed absolute values of its `m` entries: apply `sum_sq_cube_le` to `|a i j|` and take
square roots. -/
theorem coeffNorm_cube_le {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) :
    coeffNorm a i ^ 3 ≤ Real.sqrt (m : ℝ) * ∑ j, |a i j| ^ 3 := by
  set S : ℝ := ∑ j, a i j ^ 2 with hS
  set T : ℝ := ∑ j, |a i j| ^ 3 with hT
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j _ => by positivity
  have hkey : S ^ 3 ≤ (m : ℝ) * T ^ 2 := by
    have h := sum_sq_cube_le (fun j => |a i j|) (fun j => abs_nonneg _)
    have h2 : ∑ j, |a i j| ^ 2 = S := Finset.sum_congr rfl fun j _ => sq_abs _
    rw [h2] at h
    exact h
  have hcube : coeffNorm a i ^ 3 = Real.sqrt (S ^ 3) := by
    rw [coeffNorm, ← hS]
    rw [show S ^ 3 = S * S * S from by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_mul hS0]
    ring
  rw [hcube]
  have hrhs : Real.sqrt (m : ℝ) * T = Real.sqrt ((m : ℝ) * T ^ 2) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hT0]
  rw [hrhs]
  exact Real.sqrt_le_sqrt hkey

end Sandpile

namespace Sandpile

variable {d : ℕ}

/-- The real power identity `x ^ (3/2) = x · √x` for positive `x`, used to expand
`variance ν ^ (3/2)` and `membraneSd d ν (ns j) ^ 3` in `third_moment_bound`. -/
theorem rpow_three_half {x : ℝ} (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by ring,
    Real.rpow_add hx, Real.rpow_one]

/-- **The third absolute moment of the standardized coefficients.** -/
theorem third_moment_bound (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {s : Finset (Site d)} {m : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s)
    (Msup : Fin m → ℝ) (hMsup : ∀ (j : Fin m) (x : Site d), greenTime d (ns j) 0 x ≤ Msup j) :
    variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
        ∑ i : Fin s.card, coeffNorm (stdCoeff d ν s ns) i ^ 3
      ≤ Real.sqrt (m : ℝ) * ∑ j, Msup j / Real.sqrt (greenSq d (ns j)) := by
  have hV32 : variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2)
      = variance (id : ℝ → ℝ) ν * Real.sqrt (variance (id : ℝ → ℝ) ν) := rpow_three_half hvar
  have hV32pos : 0 < variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) := by
    rw [hV32]; positivity
  -- step one: the Euclidean cube against the sum of cubes
  have hstep1 : ∑ i : Fin s.card, coeffNorm (stdCoeff d ν s ns) i ^ 3
      ≤ Real.sqrt (m : ℝ) * ∑ j : Fin m, ∑ i : Fin s.card, |stdCoeff d ν s ns i j| ^ 3 := by
    have h := Finset.sum_le_sum (fun (i : Fin s.card) (_ : i ∈ Finset.univ) =>
      coeffNorm_cube_le (stdCoeff d ν s ns) i)
    rw [← Finset.mul_sum] at h
    rw [Finset.sum_comm] at h
    exact h
  -- step two: each scale
  have hstep2 : ∀ j : Fin m,
      variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
          ∑ i : Fin s.card, |stdCoeff d ν s ns i j| ^ 3
        ≤ Msup j / Real.sqrt (greenSq d (ns j)) := by
    intro j
    have hQ : 0 < greenSq d (ns j) := greenSq_pos (hns j)
    have hsQ : 0 < Real.sqrt (greenSq d (ns j)) := Real.sqrt_pos.mpr hQ
    have hM : 0 < membraneSd d ν (ns j) := membraneSd_pos ν hvar (hns j)
    have hcube : ∑ i : Fin s.card, |stdCoeff d ν s ns i j| ^ 3
        = (∑' x : Site d, greenTime d (ns j) 0 x ^ 3) / membraneSd d ν (ns j) ^ 3 := by
      rw [← sum_siteEnum_greenTime_cube (hsub j), Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [stdCoeff, abs_div, abs_of_nonneg (greenTime_nonneg _ _ _),
        abs_of_pos hM, div_pow]
    have hMcube : membraneSd d ν (ns j) ^ 3
        = variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
            (greenSq d (ns j) * Real.sqrt (greenSq d (ns j))) := by
      rw [membraneSd_eq ν hvar.le, hV32, mul_pow]
      have h1 : Real.sqrt (variance (id : ℝ → ℝ) ν) ^ 3
          = variance (id : ℝ → ℝ) ν * Real.sqrt (variance (id : ℝ → ℝ) ν) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Real.sq_sqrt hvar.le]
      have h2 : Real.sqrt (greenSq d (ns j)) ^ 3
          = greenSq d (ns j) * Real.sqrt (greenSq d (ns j)) := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Real.sq_sqrt hQ.le]
      rw [h1, h2]
    have hnum := tsum_greenTime_cube_le (d := d) (ns j) (Msup j) (hMsup j)
    rw [hcube, hMcube]
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) hsQ]
    have hQsq : Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns j))
        = greenSq d (ns j) := Real.mul_self_sqrt hQ.le
    nlinarith [mul_nonneg (mul_nonneg hV32pos.le hsQ.le) (sub_nonneg.mpr hnum)]
  have hsum2 := Finset.sum_le_sum (fun (j : Fin m) (_ : j ∈ Finset.univ) => hstep2 j)
  rw [← Finset.mul_sum] at hsum2
  calc variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
        ∑ i : Fin s.card, coeffNorm (stdCoeff d ν s ns) i ^ 3
      ≤ variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
          (Real.sqrt (m : ℝ) * ∑ j : Fin m, ∑ i : Fin s.card, |stdCoeff d ν s ns i j| ^ 3) :=
        mul_le_mul_of_nonneg_left hstep1 hV32pos.le
    _ = Real.sqrt (m : ℝ) * (variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
          ∑ j : Fin m, ∑ i : Fin s.card, |stdCoeff d ν s ns i j| ^ 3) := by ring
    _ ≤ Real.sqrt (m : ℝ) * ∑ j, Msup j / Real.sqrt (greenSq d (ns j)) :=
        mul_le_mul_of_nonneg_left hsum2 (Real.sqrt_nonneg _)

end Sandpile
