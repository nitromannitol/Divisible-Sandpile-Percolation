/-
The `L²` increment of the truncated Green coefficients at two lattice sites, term
by term.

`ContHeatGradient.tsum_greenTime_sub_sq` writes

  `∑_z (g_k(x,z) - g_k(x',z))² = ∑_{a<k}∑_{b<k} Γ_{a+b}(x,x')`,
  `Γ_s(x,x') = (p_s(x,x) - p_s(x',x)) + (p_s(x',x') - p_s(x,x'))`,

so the increment is a double time sum of the summand `greenSummand` defined here.
Two estimates of that summand are proved.

The first is the crude one: all four kernels obey the Gaussian upper bound, so
`|Γ_s| ≤ C s^{-d/2}` with no reference to the distance between the two sites.
It is the only bound available at a single time when the two sites have opposite
parity, and then it is sharp: one of `p_s(x,x)` and `p_s(x',x)` vanishes and the
other is of order `s^{-d/2}`, so no factor of `|x-x'|` can appear.

The second is the pairing.  Summed over two consecutive times, `Γ` is built from
the paired kernel of `ContPairedGradient`, whose gradient bound needs no parity
hypothesis, and then

  `|Γ_s + Γ_{s+1}| ≤ C (|x-x'|+1) s^{-(d+1)/2}` .

The two together are what the two-regime split of the time sum uses: the crude
bound at the times below `|x-x'|²` and the paired bound above them, interpolated
by `min_le_rpow_mul_rpow`, which is what removes the logarithm that the paired
bound alone leaves in dimension three.
-/
import Sandpile.Support.ContPairedGradient

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The summand of the double time sum of the `L²` increment,
`Γ_s(x,x') = (p_s(x,x) - p_s(x',x)) + (p_s(x',x') - p_s(x,x'))`. -/
noncomputable def greenSummand (d : ℕ) (s : ℕ) (x x' : Site d) : ℝ :=
  (Sandpile.heatKernel d s x x - Sandpile.heatKernel d s x' x) +
    (Sandpile.heatKernel d s x' x' - Sandpile.heatKernel d s x x')

/-- The `L²` increment of the truncated Green kernel at two sites, as a double
time sum of `greenSummand`. -/
theorem tsum_greenTime_sub_sq' (k : ℕ) (x x' : Site d) :
    ∑' z : Site d, (Sandpile.greenTime d k x z - Sandpile.greenTime d k x' z) ^ 2
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, greenSummand d (a + b) x x' :=
  tsum_greenTime_sub_sq k x x'

/-- The crude bound on the summand: every one of its four kernels obeys the
Gaussian upper bound. -/
theorem exists_greenSummand_bound (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 1 ≤ s → ∀ x x' : Site d,
      |greenSummand d s x x'| ≤ C * (s : ℝ) ^ (-(d : ℝ) / 2) := by
  obtain ⟨⟨C₁, c₁, hC₁, hc₁, hgauss⟩, -, -⟩ := hHK d hd
  refine ⟨4 * C₁, by positivity, ?_⟩
  intro s hs x x'
  have hs0 : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hb : ∀ z w : Site d,
      Sandpile.heatKernel d s z w ≤ C₁ * (s : ℝ) ^ (-(d : ℝ) / 2) := by
    intro z w
    have hg := hgauss s hs z w
    have hexp : Real.exp (-c₁ * Sandpile.External.latticeDist z w ^ 2 / (s : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hnum : 0 ≤ c₁ * Sandpile.External.latticeDist z w ^ 2 := by positivity
      rw [div_nonpos_iff]
      exact Or.inr ⟨by linarith, hs0.le⟩
    have hfac : 0 ≤ C₁ * (s : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    calc Sandpile.heatKernel d s z w
        ≤ C₁ * (s : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (-c₁ * Sandpile.External.latticeDist z w ^ 2 / (s : ℝ)) := hg
      _ ≤ C₁ * (s : ℝ) ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hexp hfac
      _ = C₁ * (s : ℝ) ^ (-(d : ℝ) / 2) := by rw [mul_one]
  have h1 := hb x x
  have h2 := hb x' x
  have h3 := hb x' x'
  have h4 := hb x x'
  have n1 := heatKernel_nonneg (d := d) s x x
  have n2 := heatKernel_nonneg (d := d) s x' x
  have n3 := heatKernel_nonneg (d := d) s x' x'
  have n4 := heatKernel_nonneg (d := d) s x x'
  rw [greenSummand, abs_le]
  constructor
  · linarith
  · linarith

/-- **The summand paired over two consecutive times.**  The pairing turns the four
kernels into paired kernels, whose gradient bound needs no parity hypothesis. -/
theorem exists_greenSummand_pair_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 2 ≤ s → ∀ x x' : Site d,
      |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ C * (Sandpile.External.latticeDist x x' + 1)
            * (s : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
  obtain ⟨C, hC, hpt⟩ := exists_paired_pointwise_gradient hHK hd
  refine ⟨2 * C, by positivity, ?_⟩
  intro s hs x x'
  have hrw : greenSummand d s x x' + greenSummand d (s + 1) x x'
      = (pairedKernel d s x x - pairedKernel d s x' x)
        + (pairedKernel d s x' x' - pairedKernel d s x x') := by
    simp only [greenSummand, pairedKernel]
    ring
  have h1 := hpt s hs x x' x
  have h2 := hpt s hs x x' x'
  have h2' : |pairedKernel d s x' x' - pairedKernel d s x x'|
      ≤ C * (Sandpile.External.latticeDist x x' + 1)
          * (s : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    rw [abs_sub_comm]
    exact h2
  rw [hrw]
  calc |(pairedKernel d s x x - pairedKernel d s x' x)
        + (pairedKernel d s x' x' - pairedKernel d s x x')|
      ≤ |pairedKernel d s x x - pairedKernel d s x' x|
          + |pairedKernel d s x' x' - pairedKernel d s x x'| := abs_add_le _ _
    _ ≤ 2 * (C * (Sandpile.External.latticeDist x x' + 1)
          * (s : ℝ) ^ (-((d : ℝ) + 1) / 2)) := by linarith
    _ = 2 * C * (Sandpile.External.latticeDist x x' + 1)
          * (s : ℝ) ^ (-((d : ℝ) + 1) / 2) := by ring

/-- The minimum of two nonnegative reals is at most any geometric mean of them. -/
theorem min_le_rpow_mul_rpow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : min a b ≤ a ^ θ * b ^ (1 - θ) := by
  have hm0 : 0 ≤ min a b := le_min ha hb
  rcases eq_or_lt_of_le hm0 with hzero | hpos
  · rw [← hzero]
    positivity
  · have hma : min a b ≤ a := min_le_left a b
    have hmb : min a b ≤ b := min_le_right a b
    have hsplit : min a b = (min a b) ^ θ * (min a b) ^ (1 - θ) := by
      rw [← Real.rpow_add hpos]
      norm_num
    have h1 : (min a b) ^ θ ≤ a ^ θ := Real.rpow_le_rpow hm0 hma hθ0
    have h2 : (min a b) ^ (1 - θ) ≤ b ^ (1 - θ) := Real.rpow_le_rpow hm0 hmb (by linarith)
    calc min a b = (min a b) ^ θ * (min a b) ^ (1 - θ) := hsplit
      _ ≤ a ^ θ * b ^ (1 - θ) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg ha _)

/-- **The two-regime bound on the paired summand.**  Interpolating the crude
Gaussian bound with the paired gradient bound at the exponent `θ` replaces the
factor `|x-x'|+1` by its power `1-θ` and improves the decay in the time by
`θ/2`.  It is what makes the double time sum converge without a logarithm in
dimension three. -/
theorem exists_greenSummand_pair_interp
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, 2 ≤ s → ∀ x x' : Site d,
      |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ C * (Sandpile.External.latticeDist x x' + 1) ^ (1 - θ)
            * (s : ℝ) ^ (-((d : ℝ) + 1 - θ) / 2) := by
  obtain ⟨Cg, hCg, hcrude⟩ := exists_greenSummand_bound hHK hd
  obtain ⟨Cp, hCp, hpair⟩ := exists_greenSummand_pair_bound hHK hd
  refine ⟨(2 * Cg) ^ θ * Cp ^ (1 - θ), by positivity, ?_⟩
  intro s hs x x'
  have hs1 : 1 ≤ s := by omega
  have hs0 : (0:ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hdnn : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hld : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  set D : ℝ := Sandpile.External.latticeDist x x' + 1 with hD
  have hD0 : (0:ℝ) < D := by rw [hD]; linarith
  have ha : |greenSummand d s x x' + greenSummand d (s + 1) x x'|
      ≤ 2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2) := by
    have h1 := hcrude s hs1 x x'
    have h2 := hcrude (s + 1) (by omega) x x'
    have hcast : (((s + 1 : ℕ)) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h2
    have hmono : ((s : ℝ) + 1) ^ (-(d : ℝ) / 2) ≤ (s : ℝ) ^ (-(d : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by linarith)
    have h2' : |greenSummand d (s + 1) x x'| ≤ Cg * (s : ℝ) ^ (-(d : ℝ) / 2) :=
      le_trans h2 (mul_le_mul_of_nonneg_left hmono hCg.le)
    calc |greenSummand d s x x' + greenSummand d (s + 1) x x'|
        ≤ |greenSummand d s x x'| + |greenSummand d (s + 1) x x'| := abs_add_le _ _
      _ ≤ 2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2) := by linarith
  have hb : |greenSummand d s x x' + greenSummand d (s + 1) x x'|
      ≤ Cp * D * (s : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    have h := hpair s hs x x'
    rwa [← hD] at h
  have hmin := le_min ha hb
  have hgeom := min_le_rpow_mul_rpow
    (a := 2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2))
    (b := Cp * D * (s : ℝ) ^ (-((d : ℝ) + 1) / 2))
    (by positivity) (by positivity) hθ0 hθ1
  have hA : (2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2)) ^ θ
      = (2 * Cg) ^ θ * (s : ℝ) ^ ((-(d : ℝ) / 2) * θ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hs0.le]
  have hB : (Cp * D * (s : ℝ) ^ (-((d : ℝ) + 1) / 2)) ^ (1 - θ)
      = Cp ^ (1 - θ) * D ^ (1 - θ) * (s : ℝ) ^ ((-((d : ℝ) + 1) / 2) * (1 - θ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hs0.le,
      Real.mul_rpow hCp.le hD0.le]
  have hsmul : (s : ℝ) ^ ((-(d : ℝ) / 2) * θ) * (s : ℝ) ^ ((-((d : ℝ) + 1) / 2) * (1 - θ))
      = (s : ℝ) ^ (-((d : ℝ) + 1 - θ) / 2) := by
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  calc |greenSummand d s x x' + greenSummand d (s + 1) x x'|
      ≤ min (2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2))
          (Cp * D * (s : ℝ) ^ (-((d : ℝ) + 1) / 2)) := hmin
    _ ≤ (2 * Cg * (s : ℝ) ^ (-(d : ℝ) / 2)) ^ θ
          * (Cp * D * (s : ℝ) ^ (-((d : ℝ) + 1) / 2)) ^ (1 - θ) := hgeom
    _ = (2 * Cg) ^ θ * Cp ^ (1 - θ) * D ^ (1 - θ)
          * (s : ℝ) ^ (-((d : ℝ) + 1 - θ) / 2) := by
        rw [hA, hB, ← hsmul]
        ring

/-- A sum over an even range is the sum of its consecutive pairs. -/
theorem sum_range_two_mul (f : ℕ → ℝ) (q : ℕ) :
    ∑ b ∈ Finset.range (2 * q), f b
      = ∑ j ∈ Finset.range q, (f (2 * j) + f (2 * j + 1)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have h2 : 2 * (q + 1) = 2 * q + 1 + 1 := by omega
      rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring

/-- A sum over any range is the sum of its consecutive pairs, plus the last term
when the length is odd. -/
theorem sum_range_pairs (f : ℕ → ℝ) (k : ℕ) :
    ∑ b ∈ Finset.range k, f b
      = (∑ j ∈ Finset.range (k / 2), (f (2 * j) + f (2 * j + 1)))
        + (if k % 2 = 1 then f (k - 1) else 0) := by
  rcases Nat.even_or_odd k with hk | hk
  · have hmod : k % 2 = 0 := Nat.even_iff.mp hk
    have hk2 : k = 2 * (k / 2) := by omega
    rw [if_neg (by omega : ¬ k % 2 = 1), add_zero]
    calc ∑ b ∈ Finset.range k, f b
        = ∑ b ∈ Finset.range (2 * (k / 2)), f b := by rw [← hk2]
      _ = ∑ j ∈ Finset.range (k / 2), (f (2 * j) + f (2 * j + 1)) := sum_range_two_mul f (k / 2)
  · have hmod : k % 2 = 1 := Nat.odd_iff.mp hk
    have hk2 : k = 2 * (k / 2) + 1 := by omega
    have hlast : 2 * (k / 2) = k - 1 := by omega
    rw [if_pos hmod]
    calc ∑ b ∈ Finset.range k, f b
        = ∑ b ∈ Finset.range (2 * (k / 2) + 1), f b := by rw [← hk2]
      _ = (∑ b ∈ Finset.range (2 * (k / 2)), f b) + f (2 * (k / 2)) := Finset.sum_range_succ _ _
      _ = (∑ j ∈ Finset.range (k / 2), (f (2 * j) + f (2 * j + 1))) + f (k - 1) := by
          rw [sum_range_two_mul f (k / 2), hlast]

end Sandpile.Support
