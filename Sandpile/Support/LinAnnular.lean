import Sandpile.Support.Kernel
import Sandpile.Support.IncrementBall
import Sandpile.External.GreenBoundsHigh

/-!
# Annular summation of the intersection kernel

Annular summation of the intersection kernel.

`lem:dgt4-linearization-from-survival` uses at `sandpile.tex:5703-5709` the
tested intersection moments

  "Compact support, annular summation, and
   \eqref{eq:dgt4-intersection-first-moment}--\eqref{eq:dgt4-intersection-second-moment}
   give that for $k=1,2$,
   $\sum_{x,y\in\Z^d}a_R(x)a_R(y)\mathbf E_x\mathbf E_y[\mathcal I(X,Y)^k]\leq C(\varphi)$",

and the paper's "annular summation, already used throughout this subsection"
(`sandpile.tex:1341-1342`) is the estimate proved here: over a box of radius `K`
the intersection kernel `(1+|u|)^{4-d}` sums to at most a constant times `K^4`,
because the sphere of radius `k` in the supremum norm carries at most
`2d(2k+1)^{d-1}` sites and `(1+k)^{d-1}(1+k)^{4-d} = (1+k)^3`.
-/

open Finset

namespace Sandpile

variable {d : ℕ}

/-- `a^{n+1} - b^{n+1} ≤ (n+1) a^n (a-b)` for `0 ≤ b ≤ a`. -/
theorem pow_succ_sub_pow_le (n : ℕ) (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    a ^ (n + 1) - b ^ (n + 1) ≤ ((n : ℝ) + 1) * a ^ n * (a - b) := by
  have ha : 0 ≤ a := le_trans hb hab
  have hab0 : 0 ≤ a - b := sub_nonneg.mpr hab
  rw [← geom_sum₂_mul a b (n + 1)]
  simp only [Nat.add_sub_cancel]
  refine mul_le_mul_of_nonneg_right ?_ hab0
  have hterm : ∀ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) ≤ a ^ n := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : b ^ (n - i) ≤ a ^ (n - i) := pow_le_pow_left₀ hb hab _
    have h2 : a ^ i * a ^ (n - i) = a ^ n := by
      rw [← pow_add]
      congr 1
      omega
    calc a ^ i * b ^ (n - i) ≤ a ^ i * a ^ (n - i) :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg ha i)
      _ = a ^ n := h2
  have hcount := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hcount
  push_cast at hcount
  linarith [hcount]

/-- `∑_{k=0}^{K}(k+1)^3 ≤ (K+1)^4`. -/
theorem sum_range_cube_le (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (((k : ℝ)) + 1) ^ 3 ≤ ((K : ℝ) + 1) ^ 4 := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      push_cast
      nlinarith [ih, hK, sq_nonneg ((K : ℝ) + 1), pow_nonneg hK 2, pow_nonneg hK 3]

/-- The supremum-norm distance to the origin is at most the Euclidean norm. -/
theorem boxDist_le_latticeNorm (hd : 1 ≤ d) (u : Site d) :
    ((boxDist (0 : Site d) u : ℕ) : ℝ) ≤ Sandpile.External.latticeNorm u := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) hne
    (fun i => ((0 : Site d) i - u i).natAbs)
  have hbd : boxDist (0 : Site d) u = ((0 : Site d) i - u i).natAbs := hi
  have hcast : (((0 : Site d) i - u i).natAbs : ℝ) = |((u i : ℤ) : ℝ)| := by
    have h0 : ((0 : Site d) i - u i) = -u i := by simp
    have habs : ((u i).natAbs : ℤ) = |u i| := (Int.abs_eq_natAbs (u i)).symm
    rw [h0, Int.natAbs_neg]
    have : (((u i).natAbs : ℤ) : ℝ) = ((|u i| : ℤ) : ℝ) := by rw [habs]
    rw [← Int.cast_natCast, this, Int.cast_abs]
  rw [hbd, hcast, Sandpile.External.latticeNorm]
  have hle : ((u i : ℤ) : ℝ) ^ 2 ≤ ∑ j : Fin d, ((u j : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin d => ((u j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |((u i : ℤ) : ℝ)| = Real.sqrt (((u i : ℤ) : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j : Fin d, ((u j : ℤ) : ℝ) ^ 2) := Real.sqrt_le_sqrt hle

/-- Splitting a box sum of a radial function into the smaller box and the
sphere of the supremum norm. -/
theorem sum_boxFinset_succ (K : ℕ) (f : ℕ → ℝ) :
    ∑ u ∈ boxFinset (0 : Site d) (K + 1), f (boxDist 0 u)
      = ∑ u ∈ boxFinset (0 : Site d) K, f (boxDist 0 u)
        + (((boxFinset (0 : Site d) (K + 1)).card - (boxFinset (0 : Site d) K).card : ℕ) : ℝ)
            * f (K + 1) := by
  classical
  have hsub : boxFinset (0 : Site d) K ⊆ boxFinset (0 : Site d) (K + 1) := by
    intro z hz
    exact mem_boxFinset (le_trans (mem_boxFinset_iff.mp hz) (by omega))
  have hshell : ∀ u ∈ boxFinset (0 : Site d) (K + 1) \ boxFinset (0 : Site d) K,
      f (boxDist 0 u) = f (K + 1) := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    have h1 : boxDist (0 : Site d) u ≤ K + 1 := mem_boxFinset_iff.mp hu.1
    have h2 : ¬ (boxDist (0 : Site d) u ≤ K) := fun h => hu.2 (mem_boxFinset h)
    have : boxDist (0 : Site d) u = K + 1 := by omega
    rw [this]
  have hsdiff := Finset.sum_sdiff (f := fun u : Site d => f (boxDist 0 u)) hsub
  rw [Finset.sum_congr rfl hshell, Finset.sum_const, nsmul_eq_mul,
    Finset.card_sdiff_of_subset hsub] at hsdiff
  linarith [hsdiff]

/-- The intersection kernel at a site, through the supremum norm: the exponent
is negative, so enlarging the base decreases the value. -/
theorem interKernel_le_boxDist (hd : 5 ≤ d) (u : Site d) :
    (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ))
      ≤ (1 + ((boxDist (0 : Site d) u : ℕ) : ℝ)) ^ (4 - (d : ℝ)) := by
  have hbox := boxDist_le_latticeNorm (by omega : 1 ≤ d) u
  have ht : (0 : ℝ) < (d : ℝ) - 4 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hb0 : (0 : ℝ) < 1 + ((boxDist (0 : Site d) u : ℕ) : ℝ) := by positivity
  have hu0 : (0 : ℝ) < 1 + Sandpile.External.latticeNorm u := by
    have : 0 ≤ Sandpile.External.latticeNorm u := Real.sqrt_nonneg _
    linarith
  have hle : (1 + ((boxDist (0 : Site d) u : ℕ) : ℝ)) ^ ((d : ℝ) - 4)
      ≤ (1 + Sandpile.External.latticeNorm u) ^ ((d : ℝ) - 4) :=
    Real.rpow_le_rpow hb0.le (by linarith) ht.le
  have hexp : (4 - (d : ℝ)) = -((d : ℝ) - 4) := by ring
  rw [hexp, Real.rpow_neg hu0.le, Real.rpow_neg hb0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hle

/-- The sphere of radius `K+1` in the supremum norm carries at most
`2d(2K+3)^{d-1}` sites. -/
theorem card_shell_le (hd : 1 ≤ d) (K : ℕ) :
    ((((boxFinset (0 : Site d) (K + 1)).card - (boxFinset (0 : Site d) K).card : ℕ)) : ℝ)
      ≤ 2 * (d : ℝ) * (2 * (K : ℝ) + 3) ^ (d - 1) := by
  have hcard1 : (boxFinset (0 : Site d) (K + 1)).card = (2 * (K + 1) + 1) ^ d :=
    card_boxFinset (0 : Site d) (K + 1)
  have hcard0 : (boxFinset (0 : Site d) K).card = (2 * K + 1) ^ d := card_boxFinset (0 : Site d) K
  have hmono : (2 * K + 1) ^ d ≤ (2 * (K + 1) + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  rw [hcard1, hcard0, Nat.cast_sub hmono]
  have hd1 : d - 1 + 1 = d := by omega
  have hkey := pow_succ_sub_pow_le (d - 1) (2 * (K : ℝ) + 3) (2 * (K : ℝ) + 1)
    (by positivity) (by linarith)
  rw [hd1] at hkey
  have hcast1 : (((2 * (K + 1) + 1) ^ d : ℕ) : ℝ) = (2 * (K : ℝ) + 3) ^ d := by
    push_cast
    ring_nf
  have hcast0 : (((2 * K + 1) ^ d : ℕ) : ℝ) = (2 * (K : ℝ) + 1) ^ d := by
    push_cast
    ring_nf
  rw [hcast1, hcast0]
  have hdcast : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      have : (1 : ℕ) ≤ d := hd
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; ring
  calc (2 * (K : ℝ) + 3) ^ d - (2 * (K : ℝ) + 1) ^ d
      ≤ (((d - 1 : ℕ) : ℝ) + 1) * (2 * (K : ℝ) + 3) ^ (d - 1) *
          ((2 * (K : ℝ) + 3) - (2 * (K : ℝ) + 1)) := hkey
    _ = 2 * (d : ℝ) * (2 * (K : ℝ) + 3) ^ (d - 1) := by
        rw [hdcast]; ring

/-- The radial kernel is at most one. -/
theorem kernel_le_one (hd : 5 ≤ d) (k : ℕ) :
    (1 + (k : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 := by
  have hb : (1 : ℝ) ≤ 1 + (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hexp : (4 : ℝ) - (d : ℝ) ≤ 0 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  simpa using Real.rpow_le_rpow_of_exponent_le hb hexp

/-- One step of the annular estimate: the sphere of radius `K+1` contributes at
most `d 2^d (K+2)^3`. -/
theorem shell_contribution_le (hd : 5 ≤ d) (K : ℕ) :
    ((((boxFinset (0 : Site d) (K + 1)).card - (boxFinset (0 : Site d) K).card : ℕ)) : ℝ)
        * (1 + ((K + 1 : ℕ) : ℝ)) ^ (4 - (d : ℝ))
      ≤ ((d : ℝ) * 2 ^ d) * ((K : ℝ) + 2) ^ 3 := by
  have hd1 : 1 ≤ d := by omega
  have hcard := card_shell_le (d := d) hd1 K
  have hpos : (0 : ℝ) < (1 + ((K + 1 : ℕ) : ℝ)) ^ (4 - (d : ℝ)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hbase : (1 + ((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 2 := by push_cast; ring
  have hshell : (2 * (K : ℝ) + 3) ^ (d - 1) ≤ 2 ^ (d - 1) * ((K : ℝ) + 2) ^ (d - 1) := by
    have h1 : (2 * (K : ℝ) + 3) ≤ 2 * ((K : ℝ) + 2) := by linarith
    calc (2 * (K : ℝ) + 3) ^ (d - 1) ≤ (2 * ((K : ℝ) + 2)) ^ (d - 1) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = 2 ^ (d - 1) * ((K : ℝ) + 2) ^ (d - 1) := by rw [mul_pow]
  have hcastd : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have h : (1 : ℕ) ≤ d := hd1
    push_cast [Nat.cast_sub h]
    ring
  have hpowsplit : ((K : ℝ) + 2) ^ (d - 1) * ((K : ℝ) + 2) ^ (4 - (d : ℝ))
      = ((K : ℝ) + 2) ^ (3 : ℕ) := by
    have hb : (0 : ℝ) < (K : ℝ) + 2 := by positivity
    rw [← Real.rpow_natCast ((K : ℝ) + 2) (d - 1), hcastd, ← Real.rpow_add hb]
    rw [show ((d : ℝ) - 1 + (4 - (d : ℝ))) = ((3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have htwo : 2 * (d : ℝ) * (2 ^ (d - 1) * ((K : ℝ) + 2) ^ (d - 1)) * ((K : ℝ) + 2) ^ (4 - (d : ℝ))
      = ((d : ℝ) * (2 * 2 ^ (d - 1))) * ((K : ℝ) + 2) ^ (3 : ℕ) := by
    rw [← hpowsplit]; ring
  have hpow2 : (2 : ℝ) * 2 ^ (d - 1) = 2 ^ d := by
    have hdd : d - 1 + 1 = d := by omega
    calc (2 : ℝ) * 2 ^ (d - 1) = 2 ^ (d - 1) * 2 := by ring
      _ = 2 ^ (d - 1 + 1) := (pow_succ 2 (d - 1)).symm
      _ = 2 ^ d := by rw [hdd]
  calc ((((boxFinset (0 : Site d) (K + 1)).card - (boxFinset (0 : Site d) K).card : ℕ)) : ℝ)
        * (1 + ((K + 1 : ℕ) : ℝ)) ^ (4 - (d : ℝ))
      ≤ (2 * (d : ℝ) * (2 * (K : ℝ) + 3) ^ (d - 1)) * (1 + ((K + 1 : ℕ) : ℝ)) ^ (4 - (d : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hpos.le
    _ ≤ (2 * (d : ℝ) * (2 ^ (d - 1) * ((K : ℝ) + 2) ^ (d - 1))) *
          (1 + ((K + 1 : ℕ) : ℝ)) ^ (4 - (d : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hpos.le
        exact mul_le_mul_of_nonneg_left hshell (by positivity)
    _ = ((d : ℝ) * (2 * 2 ^ (d - 1))) * ((K : ℝ) + 2) ^ (3 : ℕ) := by
        rw [hbase]; exact htwo
    _ = ((d : ℝ) * 2 ^ d) * ((K : ℝ) + 2) ^ 3 := by rw [hpow2]

/-- **Annular summation** (`sandpile.tex:1341-1342`): over the box of radius `K`
the intersection kernel `(1+|u|)^{4-d}` sums to at most `d 2^d (K+1)^4`. -/
theorem sum_boxFinset_interKernel_le (hd : 5 ≤ d) (K : ℕ) :
    ∑ u ∈ boxFinset (0 : Site d) K, (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ))
      ≤ ((d : ℝ) * 2 ^ d) * ((K : ℝ) + 1) ^ 4 := by
  classical
  have hC : (1 : ℝ) ≤ (d : ℝ) * 2 ^ d := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith
  have hmain : ∀ N : ℕ,
      ∑ u ∈ boxFinset (0 : Site d) N, (1 + ((boxDist (0 : Site d) u : ℕ) : ℝ)) ^ (4 - (d : ℝ))
        ≤ ((d : ℝ) * 2 ^ d) * ((N : ℝ) + 1) ^ 4 := by
    intro N
    induction N with
    | zero =>
        have hbound : ∀ u ∈ boxFinset (0 : Site d) 0,
            (1 + ((boxDist (0 : Site d) u : ℕ) : ℝ)) ^ (4 - (d : ℝ)) ≤ 1 :=
          fun u _ => kernel_le_one hd _
        have hcard : (boxFinset (0 : Site d) 0).card = 1 := by
          rw [card_boxFinset]
          simp
        calc ∑ u ∈ boxFinset (0 : Site d) 0,
              (1 + ((boxDist (0 : Site d) u : ℕ) : ℝ)) ^ (4 - (d : ℝ))
            ≤ ∑ _u ∈ boxFinset (0 : Site d) 0, (1 : ℝ) := Finset.sum_le_sum hbound
          _ = 1 := by rw [Finset.sum_const, hcard]; simp
          _ ≤ ((d : ℝ) * 2 ^ d) * ((0 : ℕ) + 1 : ℝ) ^ 4 := by
              norm_num
              exact hC
    | succ N ih =>
        rw [sum_boxFinset_succ N (fun k => (1 + (k : ℝ)) ^ (4 - (d : ℝ)))]
        have hstep := shell_contribution_le (d := d) hd N
        have hfinal : ((d : ℝ) * 2 ^ d) * ((N : ℝ) + 1) ^ 4 + ((d : ℝ) * 2 ^ d) * ((N : ℝ) + 2) ^ 3
            ≤ ((d : ℝ) * 2 ^ d) * (((N : ℕ) : ℝ) + 1 + 1) ^ 4 := by
          have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          have hCpos : (0 : ℝ) ≤ (d : ℝ) * 2 ^ d := by positivity
          nlinarith [hN, hCpos, sq_nonneg ((N : ℝ) + 1), pow_nonneg hN 2, pow_nonneg hN 3]
        push_cast
        push_cast at ih hstep hfinal
        linarith [ih, hstep, hfinal]
  refine le_trans (Finset.sum_le_sum fun u _ => interKernel_le_boxDist hd u) (hmain K)

end Sandpile
