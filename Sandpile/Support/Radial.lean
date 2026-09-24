/-
Radial sums with a real exponent.  The split of space in the proof of
`lem:dgt4-stretched-green-scenery-tail` (`sandpile.tex:4385-4390`) needs the
number of sites in a ball weighted by a power of the radius, which the shell
decomposition of the shared library turns into a one-dimensional sum of real
powers.  The two elementary sums are `LatticeProb.sum_rpow_bound` and its
companions; the ball bound they give is here.
-/
import Sandpile.Walk
import LatticeProb.Walk.Ball
import LatticeProb.Support.ContSums

open LatticeProb

open MeasureTheory

namespace Sandpile

/-- **The weighted volume of a box.**  For `0 ≤ a < d` the sum of
`(1+|y|_∞)^{-a}` over the box of radius `n` is at most `C (1+n)^{d-a}`.  The
shell decomposition of the shared library turns it into the one-dimensional sum
above. -/
theorem exists_sum_box_rpow_bound (d : ℕ) (hd : 1 ≤ d) (a : ℝ) (ha : 0 ≤ a)
    (had : a < (d : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∑ y ∈ LatticeProb.boxFinset (0 : LatticeProb.Site d) n,
          (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) ≤ C * (1 + (n : ℝ)) ^ ((d : ℝ) - a) := by
  set b : ℝ := (d : ℝ) - 1 - a with hbdef
  have hb : -1 < b := by rw [hbdef]; linarith
  have hda : 0 < (d : ℝ) - a := by linarith
  set C : ℝ := 1 + 2 * (d : ℝ) * 3 ^ (d - 1) * (1 / ((d : ℝ) - a) + 1) with hCdef
  have hC0 : 0 < C := by
    rw [hCdef]
    have h1 : (0 : ℝ) < 1 / ((d : ℝ) - a) + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (d : ℝ) * 3 ^ (d - 1) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    nlinarith
  refine ⟨C, hC0, fun n => ?_⟩
  have hf : ∀ k : ℕ, (0 : ℝ) ≤ (1 + (k : ℝ)) ^ (-a) := fun k => by positivity
  have hshell := LatticeProb.sum_box_radial_le (d := d) (fun k => (1 + (k : ℝ)) ^ (-a)) hf n
  have hf0 : (1 + ((0 : ℕ) : ℝ)) ^ (-a) = 1 := by norm_num
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have : (d - 1 : ℕ) + 1 = d := by omega
    have := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at this
    linarith
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-a) ≤
        2 * (d : ℝ) * 3 ^ (d - 1) * (1 + (k : ℝ)) ^ b := by
    intro k _
    have hk0 : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have hstep : (2 * (k : ℝ) + 1) ^ (d - 1) ≤ 3 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hrw : (1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-a) = (1 + (k : ℝ)) ^ b := by
      rw [show ((1 + (k : ℝ)) ^ (d - 1) : ℝ) = (1 + (k : ℝ)) ^ (((d - 1 : ℕ) : ℝ)) from
        (Real.rpow_natCast _ _).symm, ← Real.rpow_add hk0, hd1, hbdef]
      ring_nf
    calc 2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-a)
        ≤ 2 * (d : ℝ) * (3 ^ (d - 1) * (1 + (k : ℝ)) ^ (d - 1)) * (1 + (k : ℝ)) ^ (-a) := by
          have hnn : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ (-a) := hf k
          refine mul_le_mul_of_nonneg_right ?_ hnn
          refine mul_le_mul_of_nonneg_left hstep ?_
          have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) *
            ((1 + (k : ℝ)) ^ (d - 1) * (1 + (k : ℝ)) ^ (-a)) := by ring
      _ = 2 * (d : ℝ) * 3 ^ (d - 1) * (1 + (k : ℝ)) ^ b := by rw [hrw]
  have hsum1 : ∑ k ∈ Finset.Icc 1 n,
      2 * (d : ℝ) * (2 * (k : ℝ) + 1) ^ (d - 1) * (1 + (k : ℝ)) ^ (-a) ≤
      2 * (d : ℝ) * 3 ^ (d - 1) * ∑ k ∈ Finset.Icc 1 n, (1 + (k : ℝ)) ^ b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum2 := sum_rpow_bound b hb n
  have hbig : (1 : ℝ) ≤ (1 + (n : ℝ)) ^ ((d : ℝ) - a) := by
    refine Real.one_le_rpow ?_ hda.le
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hb1 : b + 1 = (d : ℝ) - a := by rw [hbdef]; ring
  rw [hb1] at hsum2
  have hpos : (0 : ℝ) ≤ 2 * (d : ℝ) * 3 ^ (d - 1) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  rw [hf0] at hshell
  have hchain : ∑ y ∈ LatticeProb.boxFinset (0 : LatticeProb.Site d) n,
      (1 + (LatticeProb.supNorm y : ℝ)) ^ (-a) ≤
      1 + 2 * (d : ℝ) * 3 ^ (d - 1) * ((1 / ((d : ℝ) - a) + 1) * (1 + (n : ℝ)) ^ ((d : ℝ) - a)) := by
    refine le_trans hshell ?_
    have := mul_le_mul_of_nonneg_left hsum2 hpos
    linarith
  refine le_trans hchain ?_
  rw [hCdef]
  nlinarith [hbig, hpos]

end Sandpile
