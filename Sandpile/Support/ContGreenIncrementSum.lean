import Sandpile.Support.ContGreenIncrement
import Sandpile.Support.Radial
import Sandpile.Support.TightKernel
import LatticeProb.Support.ContSums

/-!
# The double time sum of the squared Green increment

The double time sum of the squared Green increment, summed.

`ContGreenIncrement` bounds the summand `Γ_s(x,x')` of the identity

  `∑_z (g_k(x,z) - g_k(x',z))^2 = ∑_{a<k} ∑_{b<k} Γ_{a+b}(x,x')`

in two ways: crudely, `|Γ_s| ≤ C s^{-d/2}`, and paired over two consecutive times,
`|Γ_s + Γ_{s+1}| ≤ C (|x-x'|+1)^{1-θ} s^{-(d+1-θ)/2}` for any `θ` in the unit interval. This
module carries out the summation.

For each fixed `a` the inner sum over `b` is split into consecutive pairs, so that every pair is
an instance of the paired bound at the time `a+2j`, with one unpaired term left over when `k` is
odd. The resulting double sum of `(1+a+2j)^{-(d+1-θ)/2}` is bounded by counting the square
`[0,k)^2` by the larger of the two indices: the diagonal shell `max(a,j) = s` has `2s+1` cells, so
the double sum is at most `2 ∑_{s<k} (1+s)^{1-(d+1-θ)/2}`, which the telescoping power sum of
`Radial` bounds by a multiple of `(1+k)^{(3-d+θ)/2}`. The exponent condition for that sum to
converge is `(d+1-θ)/2 < 2`, that is `d < 3 + θ`, which is why the argument runs in every
dimension at most three and needs a strictly positive `θ` only at `d = 3`.

The exponent is the one the scaling demands: with the prefactor `R^{d-4}` of the rescaled field,
the lattice separation `R|w-w'|` and the time `R^2 r`,

  `R^{d-4} (R|w-w'|)^{1-θ} (R^2 r)^{(3-d+θ)/2} = |w-w'|^{1-θ} r^{(3-d+θ)/2}` ,

the power of `R` cancelling identically for every `d` and every `θ`.
-/

open LatticeProb

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- A transition probability lies in the unit interval, so the summand is at most two. -/
theorem abs_greenSummand_le_two (hd : 1 ≤ d) (s : ℕ) (x x' : Site d) :
    |greenSummand d s x x'| ≤ 2 := by
  have h1 := Sandpile.heatKernel_le_one (d := d) hd s x x
  have h2 := Sandpile.heatKernel_le_one (d := d) hd s x' x
  have h3 := Sandpile.heatKernel_le_one (d := d) hd s x' x'
  have h4 := Sandpile.heatKernel_le_one (d := d) hd s x x'
  have n1 := heatKernel_nonneg (d := d) s x x
  have n2 := heatKernel_nonneg (d := d) s x' x
  have n3 := heatKernel_nonneg (d := d) s x' x'
  have n4 := heatKernel_nonneg (d := d) s x x'
  rw [greenSummand, abs_le]
  constructor
  · linarith
  · linarith

/-- The crude bound rewritten with the shifted time, valid at every time
including zero. -/
theorem exists_greenSummand_bound_shift
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℕ) (x x' : Site d),
      |greenSummand d s x x'| ≤ A * (1 + (s : ℝ)) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_greenSummand_bound hHK hd
  refine ⟨C * 2 ^ ((d : ℝ) / 2) + 2, by positivity, ?_⟩
  intro s x x'
  set e : ℝ := -(d : ℝ) / 2 with he
  have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  have he0 : e ≤ 0 := by rw [he]; linarith
  have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
  have hpos : (0:ℝ) < 1 + (s:ℝ) := by linarith
  have hshift : (0:ℝ) < (1 + (s:ℝ)) ^ e := Real.rpow_pos_of_pos hpos e
  have hshift1 : (1 + (s:ℝ)) ^ e ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he0
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have h2 := abs_greenSummand_le_two (d := d) hd 0 x x'
    have hone : (1 + ((0:ℕ):ℝ)) ^ e = 1 := by norm_num
    rw [hone]
    nlinarith [Real.rpow_nonneg (le_of_lt (by norm_num : (0:ℝ) < 2)) ((d:ℝ)/2),
      Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ (d:ℝ)/2)]
  · have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
    have hsp : (0:ℝ) < (s:ℝ) := by linarith
    have h := hb s hs x x'
    have hmul : ((2:ℝ) * (s:ℝ)) ^ e = (2:ℝ) ^ e * (s:ℝ) ^ e :=
      Real.mul_rpow (by norm_num) hs0
    have hcmp : ((2:ℝ) * (s:ℝ)) ^ e ≤ (1 + (s:ℝ)) ^ e :=
      Real.rpow_le_rpow_of_nonpos hpos (by linarith) he0
    have h2e : (0:ℝ) < (2:ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
    have hinv : (2:ℝ) ^ e * (2:ℝ) ^ ((d:ℝ)/2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      have hz : e + (d:ℝ)/2 = 0 := by rw [he]; ring
      rw [hz, Real.rpow_zero]
    have hkey : (s:ℝ) ^ e ≤ (2:ℝ) ^ ((d:ℝ)/2) * (1 + (s:ℝ)) ^ e := by
      nlinarith [hmul, hcmp, h2e, hinv, Real.rpow_nonneg hs0 e,
        Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) ((d:ℝ)/2)]
    nlinarith [h, hkey, hC, hshift, hshift1]

/-- Replacing the time by the shifted time in a power with exponent in `[-2,0]`
costs a factor four. -/
theorem rpow_shift_le {e : ℝ} (he : e ≤ 0) (he2 : -2 ≤ e) {s : ℕ} (hs : 1 ≤ s) :
    (s : ℝ) ^ e ≤ 4 * (1 + (s : ℝ)) ^ e := by
  have hs1 : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hs0 : (0:ℝ) < (s:ℝ) := by linarith
  have hpos : (0:ℝ) < 1 + (s:ℝ) := by linarith
  have hmul : ((2:ℝ) * (s:ℝ)) ^ e = (2:ℝ) ^ e * (s:ℝ) ^ e :=
    Real.mul_rpow (by norm_num) hs0.le
  have hcmp : ((2:ℝ) * (s:ℝ)) ^ e ≤ (1 + (s:ℝ)) ^ e :=
    Real.rpow_le_rpow_of_nonpos hpos (by linarith) he
  have h2e : (0:ℝ) < (2:ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) e
  have hlow : (1:ℝ)/4 ≤ (2:ℝ) ^ e := by
    have hstep : (2:ℝ) ^ (-2:ℝ) ≤ (2:ℝ) ^ e :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
    have hval : (2:ℝ) ^ (-2:ℝ) = 1/4 := by
      rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num),
        Real.rpow_natCast]
      norm_num
    rw [hval] at hstep
    exact hstep
  have hse : (0:ℝ) ≤ (s:ℝ) ^ e := Real.rpow_nonneg hs0.le e
  nlinarith [hmul, hcmp, hlow, hse, h2e]

/-- At the two smallest times a power of the shifted time with exponent in
`[-2,0]` is at least a quarter. -/
theorem one_le_four_mul_rpow {e : ℝ} (he : e ≤ 0) (he2 : -2 ≤ e) {s : ℕ} (hs : s ≤ 1) :
    (1 : ℝ) ≤ 4 * (1 + (s : ℝ)) ^ e := by
  have hs1 : (s:ℝ) ≤ 1 := by exact_mod_cast hs
  have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
  have hpos : (0:ℝ) < 1 + (s:ℝ) := by linarith
  have hcmp : (2:ℝ) ^ e ≤ (1 + (s:ℝ)) ^ e :=
    Real.rpow_le_rpow_of_nonpos hpos (by linarith) he
  have hstep : (2:ℝ) ^ (-2:ℝ) ≤ (2:ℝ) ^ e :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
  have hval : (2:ℝ) ^ (-2:ℝ) = 1/4 := by
    rw [show (-2:ℝ) = -((2:ℕ):ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [hval] at hstep
  linarith [hcmp, hstep]

/-- The paired bound rewritten with the shifted time, valid at every time
including the two smallest. -/
theorem exists_greenSummand_pair_shift
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (s : ℕ) (x x' : Site d),
      |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (s : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2) := by
  obtain ⟨C, hC, hI⟩ := exists_greenSummand_pair_interp hHK hd hθ0 hθ1
  refine ⟨4 * C + 16, by positivity, ?_⟩
  intro s x x'
  set e : ℝ := -((d : ℝ) + 1 - θ) / 2 with hedef
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hd3' : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : e ≤ 0 := by rw [hedef]; linarith
  have he2 : (-2:ℝ) ≤ e := by rw [hedef]; linarith
  have hs0 : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
  have hpos : (0:ℝ) < 1 + (s:ℝ) := by linarith
  have hshift : (0:ℝ) < (1 + (s:ℝ)) ^ e := Real.rpow_pos_of_pos hpos e
  have hDnn : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  have hD1 : (1:ℝ) ≤ Sandpile.External.latticeDist x x' + 1 := by linarith
  have hDp : (1:ℝ) ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) :=
    Real.one_le_rpow hD1 (by linarith)
  by_cases hs : 2 ≤ s
  · have h := hI s hs x x'
    have hsh := rpow_shift_le he he2 (s := s) (by omega)
    have hDnn' : (0:ℝ) ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) := by linarith
    set P : ℝ := (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) with hP
    calc |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ C * P * (s:ℝ) ^ e := h
      _ ≤ C * P * (4 * (1 + (s:ℝ)) ^ e) :=
          mul_le_mul_of_nonneg_left hsh (by positivity)
      _ = 4 * C * (P * (1 + (s:ℝ)) ^ e) := by ring
      _ ≤ (4 * C + 16) * (P * (1 + (s:ℝ)) ^ e) := by
          have hnn : (0:ℝ) ≤ P * (1 + (s:ℝ)) ^ e :=
            mul_nonneg (by rw [hP]; exact hDnn') hshift.le
          nlinarith [hnn, hC]
      _ = (4 * C + 16) * P * (1 + (s:ℝ)) ^ e := by ring
  · have hs1 : s ≤ 1 := by omega
    have hA := abs_greenSummand_le_two (d := d) hd s x x'
    have hB := abs_greenSummand_le_two (d := d) hd (s + 1) x x'
    have htri : |greenSummand d s x x' + greenSummand d (s + 1) x x'| ≤ 4 := by
      have := abs_add_le (greenSummand d s x x') (greenSummand d (s + 1) x x')
      linarith
    have hq := one_le_four_mul_rpow he he2 (s := s) hs1
    set P : ℝ := (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) with hP
    calc |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ 4 := htri
      _ ≤ 16 * (1 + (s:ℝ)) ^ e := by linarith
      _ ≤ 16 * (P * (1 + (s:ℝ)) ^ e) := by
          have hstep : (1:ℝ) * (1 + (s:ℝ)) ^ e ≤ P * (1 + (s:ℝ)) ^ e :=
            mul_le_mul_of_nonneg_right hDp hshift.le
          linarith [hstep]
      _ ≤ (4 * C + 16) * (P * (1 + (s:ℝ)) ^ e) := by
          have hnn : (0:ℝ) ≤ P * (1 + (s:ℝ)) ^ e :=
            mul_nonneg (by linarith) hshift.le
          nlinarith [hnn, hC]
      _ = (4 * C + 16) * P * (1 + (s:ℝ)) ^ e := by ring

/-- **The inner time sum at a fixed outer time.**  Splitting the sum over `b`
into consecutive pairs makes every pair an instance of the paired bound at the
time `a + 2j`, with one unpaired term left when `k` is odd; that term is bounded
crudely, and its time is at least `k`. -/
theorem exists_abs_sum_range_greenSummand_le
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ (k a : ℕ), 1 ≤ k → ∀ x x' : Site d,
      |∑ b ∈ Finset.range k, greenSummand d (a + b) x x'|
        ≤ A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (∑ j ∈ Finset.range (k / 2),
                (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
          + A * (k : ℝ) ^ (-(d : ℝ) / 2) := by
  obtain ⟨A₁, hA₁, hpair⟩ := exists_greenSummand_pair_shift hHK hd hd3 hθ0 hθ1
  obtain ⟨A₂, hA₂, hcrude⟩ := exists_greenSummand_bound_shift hHK hd
  refine ⟨A₁ + A₂, by positivity, ?_⟩
  intro k a hk x x'
  have hdnn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  have hDnn : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  have hDp : (1:ℝ) ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hkpow : (0:ℝ) < (k:ℝ) ^ (-(d:ℝ) / 2) := Real.rpow_pos_of_pos hk0 _
  have hsplit := sum_range_pairs (fun b => greenSummand d (a + b) x x') k
  have hpairsum : |∑ j ∈ Finset.range (k / 2),
        (greenSummand d (a + 2 * j) x x' + greenSummand d (a + (2 * j + 1)) x x')|
      ≤ A₁ * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
          * ∑ j ∈ Finset.range (k / 2),
              (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2) := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro j _
    exact hpair (a + 2 * j) x x'
  have hodd : |if k % 2 = 1 then greenSummand d (a + (k - 1)) x x' else 0|
      ≤ A₂ * (k:ℝ) ^ (-(d:ℝ) / 2) := by
    split_ifs with hkk
    · have h := hcrude (a + (k - 1)) x x'
      have hnat : k ≤ 1 + (a + (k - 1)) := by omega
      have hge : (k:ℝ) ≤ 1 + ((a + (k - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      have hmono : (1 + ((a + (k - 1) : ℕ) : ℝ)) ^ (-(d:ℝ) / 2) ≤ (k:ℝ) ^ (-(d:ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos hk0 hge (by linarith)
      calc |greenSummand d (a + (k - 1)) x x'|
          ≤ A₂ * (1 + ((a + (k - 1) : ℕ) : ℝ)) ^ (-(d:ℝ) / 2) := h
        _ ≤ A₂ * (k:ℝ) ^ (-(d:ℝ) / 2) := mul_le_mul_of_nonneg_left hmono hA₂.le
    · simpa using mul_nonneg hA₂.le hkpow.le
  have hS : (0:ℝ) ≤ ∑ j ∈ Finset.range (k / 2),
      (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2) := by
    refine Finset.sum_nonneg ?_
    intro j _
    positivity
  have hPS : (0:ℝ) ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
      * ∑ j ∈ Finset.range (k / 2),
          (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2) :=
    mul_nonneg (by linarith) hS
  rw [hsplit]
  calc |(∑ j ∈ Finset.range (k / 2),
          (greenSummand d (a + 2 * j) x x' + greenSummand d (a + (2 * j + 1)) x x'))
        + (if k % 2 = 1 then greenSummand d (a + (k - 1)) x x' else 0)|
      ≤ |∑ j ∈ Finset.range (k / 2),
          (greenSummand d (a + 2 * j) x x' + greenSummand d (a + (2 * j + 1)) x x')|
        + |if k % 2 = 1 then greenSummand d (a + (k - 1)) x x' else 0| := abs_add_le _ _
    _ ≤ A₁ * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
          * (∑ j ∈ Finset.range (k / 2),
              (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
        + A₂ * (k:ℝ) ^ (-(d:ℝ) / 2) := by linarith [hpairsum, hodd]
    _ ≤ (A₁ + A₂) * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
          * (∑ j ∈ Finset.range (k / 2),
              (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
        + (A₁ + A₂) * (k:ℝ) ^ (-(d:ℝ) / 2) := by nlinarith [hPS, hkpow, hA₁, hA₂]

/-- The unpaired remainder, summed over the outer time, is dominated by the
exponent the paired sum produces. -/
theorem mul_rpow_neg_half_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hd3 : d ≤ 3) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * (k : ℝ) ^ (-(d : ℝ) / 2)
      ≤ (1 + (k : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) := by
  have hd3' : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hk0 : (0:ℝ) < (k:ℝ) := by linarith
  have hcollect : (k:ℝ) * (k:ℝ) ^ (-(d:ℝ) / 2) = (k:ℝ) ^ (1 + -(d:ℝ) / 2) := by
    rw [Real.rpow_add hk0, Real.rpow_one]
  have hexp : (1:ℝ) + -(d:ℝ) / 2 ≤ (3 - (d:ℝ) + θ) / 2 := by linarith
  have hstep1 : (k:ℝ) ^ (1 + -(d:ℝ) / 2) ≤ (k:ℝ) ^ ((3 - (d:ℝ) + θ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hk1 hexp
  have hstep2 : (k:ℝ) ^ ((3 - (d:ℝ) + θ) / 2) ≤ (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
  rw [hcollect]
  linarith [hstep1, hstep2]

/-- **The `L²` increment of the truncated Green kernel at two sites.**  For every
`θ` in the unit interval and every dimension at most three,

  `∑_z (g_k(x,z) - g_k(x',z))^2 ≤ C (|x-x'|+1)^{1-θ} (1+k)^{(3-d+θ)/2}` ,

the constant depending on the dimension, on the exponent `θ` and on the
constants of the Gaussian heat-kernel bounds, and on nothing else.  A strictly
positive `θ` is needed only at `d = 3`, where it is what makes the double time
sum converge. -/
theorem exists_tsum_greenTime_sub_sq_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (x x' : Site d),
      ∑' z : Site d,
          (Sandpile.greenTime d k x z - Sandpile.greenTime d k x' z) ^ 2
        ≤ C * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) := by
  obtain ⟨A, hA, hinner⟩ := exists_abs_sum_range_greenSummand_le hHK hd hd3 hθ0.le hθ1
  have hdnn : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
  have hd3' : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have hepos : (0:ℝ) < (3 - (d : ℝ) + θ) / 2 := by linarith
  have hc0 : (0:ℝ) < 2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2) := by
    have hrec : (0:ℝ) < 1 / ((3 - (d : ℝ) + θ) / 2) := one_div_pos.mpr hepos
    linarith
  refine ⟨A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2)) + A, by nlinarith [hA, hc0], ?_⟩
  intro k x x'
  have hDnn : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  have hDp : (1:ℝ) ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  have hkpow : (0:ℝ) ≤ (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) := by
    have hb : (0:ℝ) ≤ 1 + (k:ℝ) := by positivity
    exact Real.rpow_nonneg hb _
  have hCnn : (0:ℝ) ≤ A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2)) + A := by
    nlinarith [hA, hc0]
  rw [tsum_greenTime_sub_sq']
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    simp only [Finset.range_zero, Finset.sum_empty]
    have h1 : (0:ℝ) ≤ (A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2)) + A)
        * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) :=
      mul_nonneg hCnn (by linarith)
    exact mul_nonneg h1 hkpow
  · have hS := sum_sum_shift_rpow_le (e := -((d : ℝ) + 1 - θ) / 2) (by linarith) (by linarith)
      k (k / 2) (by omega)
    have heq : (-((d : ℝ) + 1 - θ) / 2) + 2 = (3 - (d:ℝ) + θ) / 2 := by ring
    rw [heq] at hS
    have hstep : ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, greenSummand d (a + b) x x'
        ≤ ∑ a ∈ Finset.range k,
            (A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
                * (∑ j ∈ Finset.range (k / 2),
                    (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
              + A * (k:ℝ) ^ (-(d : ℝ) / 2)) := by
      refine le_trans (le_abs_self _) ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum ?_
      intro a _
      exact hinner k a hk x x'
    have hsplit : ∑ a ∈ Finset.range k,
          (A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
              * (∑ j ∈ Finset.range (k / 2),
                  (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
            + A * (k:ℝ) ^ (-(d : ℝ) / 2))
        = A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (∑ a ∈ Finset.range k, ∑ j ∈ Finset.range (k / 2),
                (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
          + (k:ℝ) * (A * (k:ℝ) ^ (-(d : ℝ) / 2)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    have hrem : (k:ℝ) * (A * (k:ℝ) ^ (-(d : ℝ) / 2))
        ≤ A * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) := by
      have h := mul_rpow_neg_half_le (d := d) (θ := θ) hθ0.le hd3 hk
      nlinarith [h, hA]
    have hmain : A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
          * (∑ a ∈ Finset.range k, ∑ j ∈ Finset.range (k / 2),
              (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
        ≤ A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2))
            * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) := by
      have hfac : (0:ℝ) ≤ A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ) :=
        mul_nonneg hA.le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hS hfac]
    have hfinal : A * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2)
        ≤ A * ((Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2)) := by
      have hstep2 : (1:ℝ) * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2)
          ≤ (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) :=
        mul_le_mul_of_nonneg_right hDp hkpow
      nlinarith [hstep2, hA]
    calc ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, greenSummand d (a + b) x x'
        ≤ A * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (∑ a ∈ Finset.range k, ∑ j ∈ Finset.range (k / 2),
                (1 + ((a + 2 * j : ℕ) : ℝ)) ^ (-((d : ℝ) + 1 - θ) / 2))
          + (k:ℝ) * (A * (k:ℝ) ^ (-(d : ℝ) / 2)) := by rw [← hsplit]; exact hstep
      _ ≤ A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2))
            * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2)
          + A * ((Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2)) := by
          linarith [hmain, hrem, hfinal]
      _ = (A * (2 * (1 / ((3 - (d : ℝ) + θ) / 2) + 2)) + A)
            * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (1 + (k:ℝ)) ^ ((3 - (d:ℝ) + θ) / 2) := by ring

end Sandpile.Support
