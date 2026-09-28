import Sandpile.Support.Iterate
import Sandpile.External.HeatKernelBounds

/-!
# Small-Power Heat Kernel Bounds

The small-power decay of the doubled heat kernel in dimension four, the input
that `prop:d4-diffusive-tightness` (`sandpile.tex:3288-3316`) feeds to the
tightness criterion.  The paper's chain is

  `\sum_{a,b<t} p_{a+b}(x,y) \leq C(\varepsilon)(t/(1+|x-y|^2))^{\varepsilon}`,

from the Gaussian upper bound `eq:rw-gaussian-upper` and `e^{-q}\leq
C(\varepsilon)q^{-\varepsilon}`.  Here the exponential bound is proved with the
constant one, and the double time sum is factored: for `a+b\geq1` the weight
`(a+b)^{\varepsilon-2}` is at most `4(a+1)^{\varepsilon/2-1}(b+1)^{\varepsilon/2-1}`,
because `(a+1)(b+1)\leq4(a+b)^2`, so the double sum splits into the square of a
one-dimensional sum, and `\sum_{m<M}(m+1)^{\delta-1}\leq M^{\delta}/\delta` by
induction from the weighted arithmetic-geometric mean inequality.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The heat kernel is invariant under negating both endpoints:
`heatKernel d k (-x) (-y) = heatKernel d k x y`, proved by induction on `k` using the
symmetry of the one-step recursion under `x ↦ -x`. -/
theorem heatKernel_neg : ∀ (k : ℕ) (x y : Site d),
    heatKernel d k (-x) (-y) = heatKernel d k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      show (if -x = -y then (1 : ℝ) else 0) = if x = y then 1 else 0
      by_cases h : x = y
      · simp [h]
      · simp [h, neg_inj]
  | succ j ih =>
      intro x y
      show (∑ i : Fin d, (heatKernel d j (-x + unit i) (-y)
              + heatKernel d j (-x - unit i) (-y))) / (2 * d)
          = (∑ i : Fin d, (heatKernel d j (x + unit i) y
              + heatKernel d j (x - unit i) y)) / (2 * d)
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : -x + unit i = -(x - unit i) := by abel
      have h2 : -x - unit i = -(x + unit i) := by abel
      rw [h1, h2, ih (x - unit i) y, ih (x + unit i) y]
      ring

/-- The heat kernel is symmetric in its two sites: `heatKernel d k x y = heatKernel d k y x`,
obtained by translating both sides to be based at `0` via `heatKernel_add_right` and then
applying `heatKernel_neg`. -/
theorem heatKernel_symm (k : ℕ) (x y : Site d) :
    heatKernel d k x y = heatKernel d k y x := by
  have h1 : heatKernel d k x y = heatKernel d k (x - y) 0 := by
    have := heatKernel_add_right k (x - y) 0 y
    simpa using this
  have h2 : heatKernel d k y x = heatKernel d k (y - x) 0 := by
    have := heatKernel_add_right k (y - x) 0 x
    simpa using this
  have h3 : heatKernel d k (y - x) 0 = heatKernel d k (x - y) 0 := by
    have := heatKernel_neg k (y - x) 0
    rw [show -(y - x) = x - y by abel, neg_zero] at this
    exact this.symm
  rw [h1, h2, h3]

/-- The finite-time Green function is symmetric: `greenTime d t x y = greenTime d t y x`,
by summing `heatKernel_symm` over the first `t` times. -/
theorem greenTime_symm (t : ℕ) (x y : Site d) :
    greenTime d t x y = greenTime d t y x :=
  Finset.sum_congr rfl fun k _ => heatKernel_symm k x y

/-- The inner product of two finite-time Green functions decomposes as a double sum of heat
kernels: `∑'_z greenTime t x z * greenTime t y z = ∑_{a<t} ∑_{b<t} heatKernel (a+b) x y`,
obtained by expanding `greenTime` as a sum over one factor and applying the heat-kernel
convolution identity `tsum_heatKernel_mul_greenTime` to the other. -/
theorem tsum_greenTime_mul_greenTime (t : ℕ) (x y : Site d) :
    ∑' z : Site d, greenTime d t x z * greenTime d t y z
      = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel d (a + b) x y := by
  have h1 : ∀ z : Site d, greenTime d t x z * greenTime d t y z
      = ∑ a ∈ Finset.range t, heatKernel d a x z * greenTime d t z y := by
    intro z
    rw [greenTime_symm t y z]
    show (∑ a ∈ Finset.range t, heatKernel d a x z) * greenTime d t z y = _
    rw [Finset.sum_mul]
  rw [tsum_congr h1,
    Summable.tsum_finsetSum fun a (_ : a ∈ Finset.range t) => summable_heatKernel_mul a x _]
  exact Finset.sum_congr rfl fun a _ => tsum_heatKernel_mul_greenTime a t x y

end Sandpile

namespace Sandpile.Support

/-- The elementary bound `exp (-q) ≤ q ^ (-ε)` for `0 < ε ≤ 1` and `q > 0`, proved from
`q ^ ε ≤ 1 + q ≤ exp q` by taking reciprocals. -/
theorem exp_neg_le_rpow_neg (ε q : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hq : 0 < q) :
    Real.exp (-q) ≤ q ^ (-ε) := by
  have h1 : q ^ ε ≤ 1 + q := by
    rcases le_or_gt q 1 with hq1 | hq1
    · calc q ^ ε ≤ (1:ℝ) ^ ε := Real.rpow_le_rpow (le_of_lt hq) hq1 (le_of_lt hε)
        _ = 1 := Real.one_rpow ε
        _ ≤ 1 + q := by linarith
    · calc q ^ ε ≤ q ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_lt hq1) hε1
        _ = q := Real.rpow_one q
        _ ≤ 1 + q := by linarith
  have h2 : (1:ℝ) + q ≤ Real.exp q := by
    have := Real.add_one_le_exp q
    linarith
  have h3 : (0:ℝ) < q ^ ε := Real.rpow_pos_of_pos hq ε
  rw [Real.rpow_neg (le_of_lt hq), Real.exp_neg]
  exact inv_anti₀ h3 (le_trans h1 h2)

/-- The partial-sum bound `∑_{m<M} (m+1)^{ε-1} ≤ M^ε / ε` for `0 < ε ≤ 1`, proved by
induction on `M` from the weighted arithmetic-geometric mean inequality comparing
`(n+1)^ε` with `n^ε + ε (n+1)^{ε-1}`. -/
theorem sum_succ_rpow_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (M : ℕ) :
    ∑ m ∈ Finset.range M, ((m : ℝ) + 1) ^ (ε - 1) ≤ (M : ℝ) ^ ε / ε := by
  induction M with
  | zero => simp [Real.zero_rpow (ne_of_gt hε)]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hpow : (0:ℝ) < ((n : ℝ) + 1) ^ (ε - 1) := Real.rpow_pos_of_pos hn1 _
    have hkey : (n : ℝ) ^ ε + ε * ((n : ℝ) + 1) ^ (ε - 1) ≤ ((n : ℝ) + 1) ^ ε := by
      have hgm : (n : ℝ) ^ ε * ((n : ℝ) + 1) ^ (1 - ε)
          ≤ ε * (n : ℝ) + (1 - ε) * ((n : ℝ) + 1) :=
        Real.geom_mean_le_arith_mean2_weighted (le_of_lt hε) (by linarith)
          (Nat.cast_nonneg n) (le_of_lt hn1) (by ring)
      have hsplit : (n : ℝ) ^ ε
          = ((n : ℝ) ^ ε * ((n : ℝ) + 1) ^ (1 - ε)) * ((n : ℝ) + 1) ^ (ε - 1) := by
        rw [mul_assoc, ← Real.rpow_add hn1]
        norm_num
      have hstep : ((n : ℝ) + 1) ^ ε
          = ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ (ε - 1) := by
        nth_rewrite 2 [← Real.rpow_one ((n : ℝ) + 1)]
        rw [← Real.rpow_add hn1]
        ring_nf
      rw [hsplit, hstep]
      nlinarith [hpow, hgm]
    rw [le_div_iff₀ hε]
    have ih' : (∑ m ∈ Finset.range n, ((m : ℝ) + 1) ^ (ε - 1)) * ε ≤ (n : ℝ) ^ ε := by
      rw [← le_div_iff₀ hε]; exact ih
    push_cast
    nlinarith [hkey, ih']

/-- The pair factorization `(a+b)^{ε-2} ≤ 4(a+1)^{ε/2-1}(b+1)^{ε/2-1}` for `a + b ≥ 1`,
proved from the elementary inequality `(a+1)(b+1) ≤ 4(a+b)^2` by taking the `(ε-2)/2`
power of both sides. -/
theorem pair_factor (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (a b : ℕ) (hab : 1 ≤ a + b) :
    ((a : ℝ) + (b : ℝ)) ^ (ε - 2)
      ≤ 4 * ((a : ℝ) + 1) ^ (ε / 2 - 1) * ((b : ℝ) + 1) ^ (ε / 2 - 1) := by
  have ha : (0:ℝ) ≤ (a:ℝ) := Nat.cast_nonneg a
  have hb : (0:ℝ) ≤ (b:ℝ) := Nat.cast_nonneg b
  have hs : (1:ℝ) ≤ (a:ℝ) + (b:ℝ) := by
    have : (1:ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast hab
    push_cast at this; linarith
  have hs0 : (0:ℝ) < (a:ℝ) + (b:ℝ) := by linarith
  have hu : (0:ℝ) < (a:ℝ) + 1 := by linarith
  have hv : (0:ℝ) < (b:ℝ) + 1 := by linarith
  have hquot : (0:ℝ) < ((a:ℝ) + 1) * ((b:ℝ) + 1) / 4 := by positivity
  have hle : ((a:ℝ) + 1) * ((b:ℝ) + 1) / 4 ≤ ((a:ℝ) + (b:ℝ)) ^ 2 := by nlinarith
  have hexp : (ε - 2) / 2 ≤ 0 := by linarith
  have hmain := Real.rpow_le_rpow_of_nonpos hquot hle hexp
  have hL : (((a:ℝ) + (b:ℝ)) ^ 2) ^ ((ε - 2) / 2) = ((a:ℝ) + (b:ℝ)) ^ (ε - 2) := by
    rw [← Real.rpow_natCast ((a:ℝ) + (b:ℝ)) 2, ← Real.rpow_mul (le_of_lt hs0)]
    congr 1
    push_cast
    ring
  have hR : (((a:ℝ) + 1) * ((b:ℝ) + 1) / 4) ^ ((ε - 2) / 2)
      = 4 ^ ((2 - ε) / 2) * (((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1)) := by
    rw [Real.div_rpow (by positivity) (by norm_num),
      Real.mul_rpow (le_of_lt hu) (le_of_lt hv)]
    have h4 : (4:ℝ) ^ ((ε - 2) / 2) = ((4:ℝ) ^ ((2 - ε) / 2))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
      ring_nf
    have hue : ((a:ℝ) + 1) ^ ((ε - 2) / 2) = ((a:ℝ) + 1) ^ (ε / 2 - 1) := by
      congr 1; ring
    have hve : ((b:ℝ) + 1) ^ ((ε - 2) / 2) = ((b:ℝ) + 1) ^ (ε / 2 - 1) := by
      congr 1; ring
    rw [h4, hue, hve]
    field_simp
  have h4le : (4:ℝ) ^ ((2 - ε) / 2) ≤ 4 := by
    calc (4:ℝ) ^ ((2 - ε) / 2) ≤ (4:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have hpos : (0:ℝ) < ((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1) := by
    exact mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
  rw [hL, hR] at hmain
  nlinarith [hmain, hpos, h4le]

/-- The Gaussian small-power bound `exp(-c L² / m) ≤ exp(c) c^{-ε} m^ε (1 + L²)^{-ε}` for
`m ≥ 1`, proved by splitting the exponent into `c/m + -(c(1+L²)/m)` and bounding the
second term via `exp_neg_le_rpow_neg`. -/
theorem exp_gauss_small_power (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ) (hc : 0 < c)
    (m : ℕ) (hm : 1 ≤ m) (L : ℝ) :
    Real.exp (-c * L ^ 2 / (m : ℝ))
      ≤ Real.exp c * c ^ (-ε) * (m : ℝ) ^ ε * (1 + L ^ 2) ^ (-ε) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hLsq : (0:ℝ) ≤ L ^ 2 := sq_nonneg L
  have hq : 0 < c * (1 + L ^ 2) / (m:ℝ) := by positivity
  have h1 : -c * L ^ 2 / (m:ℝ) = c / (m:ℝ) + -(c * (1 + L ^ 2) / (m:ℝ)) := by
    field_simp
    ring
  have h2 : Real.exp (c / (m:ℝ)) ≤ Real.exp c := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_iff₀ hm0]
    nlinarith
  have h3 : Real.exp (-(c * (1 + L ^ 2) / (m:ℝ))) ≤ (c * (1 + L ^ 2) / (m:ℝ)) ^ (-ε) :=
    exp_neg_le_rpow_neg ε _ hε hε1 hq
  have h4 : (c * (1 + L ^ 2) / (m:ℝ)) ^ (-ε)
      = c ^ (-ε) * (m:ℝ) ^ ε * (1 + L ^ 2) ^ (-ε) := by
    rw [Real.div_rpow (by positivity) (le_of_lt hm0), Real.mul_rpow (le_of_lt hc) (by positivity),
      Real.rpow_neg (le_of_lt hm0)]
    have hne : ((m:ℝ) ^ ε) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hm0 ε)
    field_simp
  rw [h1, Real.exp_add]
  calc Real.exp (c / (m:ℝ)) * Real.exp (-(c * (1 + L ^ 2) / (m:ℝ)))
      ≤ Real.exp c * ((c * (1 + L ^ 2) / (m:ℝ)) ^ (-ε)) := by
        exact mul_le_mul h2 h3 (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    _ = Real.exp c * c ^ (-ε) * (m:ℝ) ^ ε * (1 + L ^ 2) ^ (-ε) := by rw [h4]; ring

/-- A four-dimensional heat kernel bound splitting the time and space dependence: there is
`C₂ > 0` with `heatKernel 4 (a+b) x y ≤ C₂ (1+|x-y|²)^{-ε} (a+1)^{ε/2-1} (b+1)^{ε/2-1}` for
all `a, b, x, y`, obtained by combining the Gaussian upper bound `hHK` with
`exp_gauss_small_power` and `pair_factor`, treating `a = b = 0` separately. -/
theorem exists_heatKernel_product_bound (hHK : Sandpile.External.HeatKernelBounds)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (a b : ℕ) (x y : Sandpile.Site 4),
      Sandpile.heatKernel 4 (a + b) x y
        ≤ C₂ * (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε)
            * ((a : ℝ) + 1) ^ (ε / 2 - 1) * ((b : ℝ) + 1) ^ (ε / 2 - 1) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := (hHK 4 (by norm_num)).1
  refine ⟨max 1 (4 * C * Real.exp c * c ^ (-ε)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro a b x y
  set C₂ := max 1 (4 * C * Real.exp c * c ^ (-ε)) with hC₂def
  set L := Sandpile.External.latticeDist x y with hLdef
  have hLsq : (0:ℝ) ≤ L ^ 2 := sq_nonneg L
  have hA : (0:ℝ) < (1 + L ^ 2) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hu : (0:ℝ) < ((a:ℝ) + 1) ^ (ε / 2 - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hv : (0:ℝ) < ((b:ℝ) + 1) ^ (ε / 2 - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hC₂1 : (1:ℝ) ≤ C₂ := le_max_left _ _
  have hC₂2 : 4 * C * Real.exp c * c ^ (-ε) ≤ C₂ := le_max_right _ _
  rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0
    subst hb0
    by_cases hxy : x = y
    · have hL0 : L = 0 := by
        rw [hLdef, hxy]
        simp [Sandpile.External.latticeDist]
      have hlhs : Sandpile.heatKernel 4 (0 + 0) x y = 1 := by
        simp [Sandpile.heatKernel, LatticeProb.LocalCLT.heatKernel, hxy]
      rw [hlhs, hL0]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      norm_num
      linarith [hC₂1]
    · have hlhs : Sandpile.heatKernel 4 (0 + 0) x y = 0 := by
        simp [Sandpile.heatKernel, LatticeProb.LocalCLT.heatKernel, hxy]
      rw [hlhs]
      positivity
  · have hm1 : 1 ≤ a + b := hpos
    have hcast : ((a + b : ℕ) : ℝ) = (a:ℝ) + (b:ℝ) := by push_cast; ring
    have hm0 : (0:ℝ) < ((a + b : ℕ) : ℝ) := by
      have : (1:ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast hm1
      linarith
    have hstep1 := hbd (a + b) hm1 x y
    have hstep2 := exp_gauss_small_power ε hε hε1 c hc (a + b) hm1 L
    have hstep3 := pair_factor ε hε hε1 a b hm1
    have hpowneg : ((a + b : ℕ) : ℝ) ^ (-(4:ℝ) / 2) * ((a + b : ℕ) : ℝ) ^ ε
        = ((a:ℝ) + (b:ℝ)) ^ (ε - 2) := by
      rw [← Real.rpow_add hm0, hcast]
      congr 1
      ring
    have hnn : (0:ℝ) ≤ ((a + b : ℕ) : ℝ) ^ (-(4:ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos hm0 _)
    have hexpnn : (0:ℝ) ≤ Real.exp (-c * L ^ 2 / ((a + b : ℕ) : ℝ)) := le_of_lt (Real.exp_pos _)
    have hb1 : Sandpile.heatKernel 4 (a + b) x y
        ≤ C * ((a + b : ℕ) : ℝ) ^ (-(4:ℝ) / 2) *
            (Real.exp c * c ^ (-ε) * ((a + b : ℕ) : ℝ) ^ ε * (1 + L ^ 2) ^ (-ε)) := by
      refine le_trans hstep1 ?_
      exact mul_le_mul_of_nonneg_left hstep2 (by positivity)
    have hb2 : C * ((a + b : ℕ) : ℝ) ^ (-(4:ℝ) / 2) *
        (Real.exp c * c ^ (-ε) * ((a + b : ℕ) : ℝ) ^ ε * (1 + L ^ 2) ^ (-ε))
        = C * Real.exp c * c ^ (-ε) * (((a:ℝ) + (b:ℝ)) ^ (ε - 2)) * (1 + L ^ 2) ^ (-ε) := by
      rw [← hpowneg]; ring
    have hcpos : (0:ℝ) < C * Real.exp c * c ^ (-ε) := by positivity
    have hb3 : C * Real.exp c * c ^ (-ε) * (((a:ℝ) + (b:ℝ)) ^ (ε - 2)) * (1 + L ^ 2) ^ (-ε)
        ≤ C * Real.exp c * c ^ (-ε) *
            (4 * ((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1)) * (1 + L ^ 2) ^ (-ε) := by
      have := mul_le_mul_of_nonneg_left hstep3 (le_of_lt hcpos)
      exact mul_le_mul_of_nonneg_right this (le_of_lt hA)
    refine le_trans hb1 (le_trans (le_of_eq hb2) (le_trans hb3 ?_))
    have hfinal : C * Real.exp c * c ^ (-ε) *
        (4 * ((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1)) * (1 + L ^ 2) ^ (-ε)
        = (4 * C * Real.exp c * c ^ (-ε)) *
            ((1 + L ^ 2) ^ (-ε) * (((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1))) := by
      ring
    rw [hfinal]
    have hrest : (0:ℝ) < (1 + L ^ 2) ^ (-ε) *
        (((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1)) := by positivity
    calc (4 * C * Real.exp c * c ^ (-ε)) *
          ((1 + L ^ 2) ^ (-ε) * (((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1)))
        ≤ C₂ * ((1 + L ^ 2) ^ (-ε) * (((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1))) :=
          mul_le_mul_of_nonneg_right hC₂2 (le_of_lt hrest)
      _ = C₂ * (1 + L ^ 2) ^ (-ε) * ((a:ℝ) + 1) ^ (ε / 2 - 1) * ((b:ℝ) + 1) ^ (ε / 2 - 1) := by
          ring

/-- The double-sum bound `∑_{a<t} ∑_{b<t} f(a+b) ≤ K(4/ε²) t^ε` for any `f` satisfying the
pair factorization `f(a+b) ≤ K(a+1)^{ε/2-1}(b+1)^{ε/2-1}`, proved by factoring the double
sum as a product of two one-dimensional sums and bounding each with `sum_succ_rpow_le` at
exponent `ε/2`. -/
theorem double_sum_factor_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (K : ℝ) (hK : 0 ≤ K) (f : ℕ → ℝ) (t : ℕ)
    (hf : ∀ a b : ℕ, f (a + b) ≤ K * ((a : ℝ) + 1) ^ (ε / 2 - 1) * ((b : ℝ) + 1) ^ (ε / 2 - 1)) :
    ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)
      ≤ K * (4 / ε ^ 2) * (t : ℝ) ^ ε := by
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  have hsum : ∑ a ∈ Finset.range t, ((a : ℝ) + 1) ^ (ε / 2 - 1) ≤ (t : ℝ) ^ (ε / 2) / (ε / 2) :=
    sum_succ_rpow_le (ε / 2) hε2 (by linarith) t
  have hnn : (0:ℝ) ≤ ∑ a ∈ Finset.range t, ((a : ℝ) + 1) ^ (ε / 2 - 1) :=
    Finset.sum_nonneg fun a _ => le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
  have hpow : (t : ℝ) ^ (ε / 2) * (t : ℝ) ^ (ε / 2) = (t : ℝ) ^ ε := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      rw [Nat.cast_zero, Real.zero_rpow (by positivity : (0:ℝ) < ε / 2).ne',
        Real.zero_rpow (by positivity : (0:ℝ) < ε).ne']
      ring
    · have ht : (0:ℝ) < (t : ℝ) := by exact_mod_cast h
      rw [← Real.rpow_add ht]
      congr 1
      ring
  calc ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)
      ≤ ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
          K * ((a : ℝ) + 1) ^ (ε / 2 - 1) * ((b : ℝ) + 1) ^ (ε / 2 - 1) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hf a b
    _ = K * ((∑ a ∈ Finset.range t, ((a : ℝ) + 1) ^ (ε / 2 - 1)) *
          (∑ b ∈ Finset.range t, ((b : ℝ) + 1) ^ (ε / 2 - 1))) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
    _ ≤ K * (((t : ℝ) ^ (ε / 2) / (ε / 2)) * ((t : ℝ) ^ (ε / 2) / (ε / 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hsum hnn ?_) hK
        exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (by positivity)
    _ = K * (4 / ε ^ 2) * (t : ℝ) ^ ε := by
        rw [div_mul_div_comm, hpow]
        field_simp
        ring

/-- The small-power decay of the doubled Green kernel in dimension four: for
every `0 < ε ≤ 1` there is `C` with
`∑_z g_t(x,z) g_t(y,z) ≤ C t^ε (1+|x-y|²)^{-ε}` for every time and every pair of
sites.  This is `eq:d4-covariance-decay` of `sandpile.tex:3299-3305`. -/
theorem exists_green_product_small_power (hHK : Sandpile.External.HeatKernelBounds)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (t : ℕ) (x y : Sandpile.Site 4),
      ∑' z : Sandpile.Site 4, Sandpile.greenTime 4 t x z * Sandpile.greenTime 4 t y z
        ≤ C₃ * (t : ℝ) ^ ε * (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε) := by
  obtain ⟨C₂, hC₂, hbd⟩ := exists_heatKernel_product_bound hHK ε hε hε1
  refine ⟨C₂ * (4 / ε ^ 2), by positivity, ?_⟩
  intro t x y
  set A := (1 + Sandpile.External.latticeDist x y ^ 2) ^ (-ε) with hA
  have hA0 : (0:ℝ) < A := Real.rpow_pos_of_pos (by positivity) _
  have hK : (0:ℝ) ≤ C₂ * A := by positivity
  have hstep : ∀ a b : ℕ, Sandpile.heatKernel 4 (a + b) x y
      ≤ C₂ * A * ((a : ℝ) + 1) ^ (ε / 2 - 1) * ((b : ℝ) + 1) ^ (ε / 2 - 1) := fun a b => hbd a b x y
  rw [Sandpile.tsum_greenTime_mul_greenTime]
  refine le_trans (double_sum_factor_bound ε hε hε1 (C₂ * A) hK
    (fun m => Sandpile.heatKernel 4 m x y) t hstep) ?_
  rw [hA]
  ring_nf
  rfl

end Sandpile.Support
