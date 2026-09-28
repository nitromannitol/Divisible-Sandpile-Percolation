import Sandpile.Support.LimStoppedRate
import Sandpile.Support.LimStoppedModulus
import Sandpile.Support.LimNoiseMoment
import Sandpile.Support.ContGreenIncrement

/-!
# The two `L²` inputs of the box bound for the difference field

The two `L²` inputs of the box bound for the difference field, with constants below any
threshold.

The difference of the ball field and the ball-stopped field is the white noise paired with
`f_{T,u} = 2d·ballKernel_u − ballStoppedKernel_{T,u}`. Two estimates on that kernel are available:
its `L²` norm decays geometrically in the horizon (`Sandpile.Support.LimStoppedRate`), and its
increment in the centre has a spatial modulus whose constant grows with the horizon only
polynomially (`Sandpile.Support.LimStoppedModulus`, `Sandpile.Support.LimKernelShift`). Neither
alone is what a chaining estimate needs: the first has no modulus and the second has no
smallness. Interpolating the two, `min(X,Y) ≤ X^{1/2}Y^{1/2}`, produces a modulus whose constant
is the geometric mean of a geometric sequence and a polynomial one, hence tends to zero, at the
cost of halving the exponent (`eventually_diffKernel_bounds`). That is the form the Kolmogorov box
bound consumes: both of its inputs are then below any prescribed threshold once the horizon is
large, uniformly in the Brownian model. `eventually_diffField_moment_bounds` restates the same
fact as moment bounds on the white-noise pairing itself, for a general exponent `p`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### The geometric factor beats the polynomial one -/

/-- The cube root of the geometric sequence `blockRatio ^ n` still tends to `0`, since
`blockRatio ∈ (0,1)` makes `blockRatio ^ (1/3) ∈ (0,1)` as well. -/
theorem tendsto_blockRatio_rpow_third :
    Tendsto (fun n : ℕ => (blockRatio ^ n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  have hr : (blockRatio ^ ((1 : ℝ) / 3)) ^ 1 = blockRatio ^ ((1 : ℝ) / 3) := pow_one _
  have habs : |blockRatio ^ ((1 : ℝ) / 3)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos blockRatio_pos _)]
    have h1 : blockRatio ^ ((1 : ℝ) / 3) < 1 ^ ((1 : ℝ) / 3) :=
      Real.rpow_lt_rpow blockRatio_pos.le blockRatio_lt_one (by norm_num)
    simpa using h1
  have heq : ∀ n : ℕ, (blockRatio ^ n) ^ ((1 : ℝ) / 3)
      = (blockRatio ^ ((1 : ℝ) / 3)) ^ n := by
    intro n
    rw [← Real.rpow_natCast blockRatio n, ← Real.rpow_mul blockRatio_pos.le,
      ← Real.rpow_natCast (blockRatio ^ ((1 : ℝ) / 3)) n,
      ← Real.rpow_mul blockRatio_pos.le]
    ring_nf
  simp_rw [heq]
  exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs

/-- A linear factor `n + c` does not stop `(blockRatio ^ n) ^ (1/3)` from tending to `0`: the
polynomial growth is beaten by the geometric decay. -/
theorem tendsto_linear_mul_blockRatio (c : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + c) * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  have habs : |blockRatio ^ ((1 : ℝ) / 3)| < 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos blockRatio_pos _)]
    have h1 : blockRatio ^ ((1 : ℝ) / 3) < 1 ^ ((1 : ℝ) / 3) :=
      Real.rpow_lt_rpow blockRatio_pos.le blockRatio_lt_one (by norm_num)
    simpa using h1
  have heq : ∀ n : ℕ, (blockRatio ^ n) ^ ((1 : ℝ) / 3)
      = (blockRatio ^ ((1 : ℝ) / 3)) ^ n := by
    intro n
    rw [← Real.rpow_natCast blockRatio n, ← Real.rpow_mul blockRatio_pos.le,
      ← Real.rpow_natCast (blockRatio ^ ((1 : ℝ) / 3)) n,
      ← Real.rpow_mul blockRatio_pos.le]
    ring_nf
  have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 habs
  have h2 := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs).const_mul c
  have hsum := h1.add h2
  rw [mul_zero, add_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [heq n, pow_one]
  ring

/-! ### The modulus constant is at most linear in the horizon -/

/-- A real power `T ^ b` with exponent `b ∈ [0,1]` is bounded by the linear function `1 + T`,
splitting on whether `T ≤ 1` or `T ≥ 1`. -/
theorem rpow_le_one_add {T b : ℝ} (hT : 0 ≤ T) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    T ^ b ≤ 1 + T := by
  rcases le_total T 1 with h | h
  · have := Real.rpow_le_one hT h hb0
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hb1
    rw [Real.rpow_one] at this
    linarith

/-- The coefficient of the linear bound on the Green modulus constant. -/
noncomputable def greenModulusCoeff (d : ℕ) : ℝ :=
  2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4))
    / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2

/-- The coefficient `greenModulusCoeff d` is nonnegative for `1 ≤ d ≤ 3`, since it is built from
the nonnegative `greenDiffConst d` and a positive denominator. -/
theorem greenModulusCoeff_nonneg {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    0 ≤ greenModulusCoeff d := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
  have h1 := (greenDiffConst_pos hd).le
  rw [greenModulusCoeff]
  positivity

/-- **The Green modulus constant `greenModulusConst d T` is bounded by an affine function of the
horizon `T`**, with coefficient `greenModulusCoeff d`, for `2 ≤ d ≤ 3`: its square is a power of
`T` with exponent at most `1`, which `rpow_le_one_add` bounds by `1 + T`. -/
theorem greenModulusConst_le_linear {d : ℕ} (hd : 1 ≤ d) (hd2 : 2 ≤ d) (hd3 : d ≤ 3)
    {T : ℝ} (hT : 0 ≤ T) :
    greenModulusConst d T ≤ greenModulusCoeff d * (1 + T) := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd2' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
  have hC0 : (0 : ℝ) ≤ 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) := by
    have := (greenDiffConst_pos hd).le
    positivity
  have hsq : greenModulusFactor d T ^ 2
      = T ^ (2 * (1 - (2 * (d : ℝ) + 1) / 8)) / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2 := by
    rw [greenModulusFactor, div_pow]
    congr 1
    rw [← Real.rpow_natCast (T ^ (1 - (2 * (d : ℝ) + 1) / 8)) 2, ← Real.rpow_mul hT]
    norm_num
    ring_nf
  have hexp : 2 * (1 - (2 * (d : ℝ) + 1) / 8) ≤ 1 := by linarith
  have hexp0 : (0 : ℝ) ≤ 2 * (1 - (2 * (d : ℝ) + 1) / 8) := by linarith
  have hpow : T ^ (2 * (1 - (2 * (d : ℝ) + 1) / 8)) ≤ 1 + T := rpow_le_one_add hT hexp0 hexp
  have ha2 : (0 : ℝ) < (1 - (2 * (d : ℝ) + 1) / 8) ^ 2 := by positivity
  rw [greenModulusConst, hsq, greenModulusCoeff]
  have hrw1 : 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4))
      * (T ^ (2 * (1 - (2 * (d : ℝ) + 1) / 8)) / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2)
      = (2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4))
          * T ^ (2 * (1 - (2 * (d : ℝ) + 1) / 8))) / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2 := by
    ring
  have hrw2 : 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4))
        / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2 * (1 + T)
      = (2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * (1 + T))
        / (1 - (2 * (d : ℝ) + 1) / 8) ^ 2 := by
    ring
  rw [hrw1, hrw2, div_le_div_iff_of_pos_right ha2]
  exact mul_le_mul_of_nonneg_left hpow hC0

/-- `greenModulusConst d T` is monotone nondecreasing in the horizon `T`, since the underlying
`greenModulusFactor d T` is. -/
theorem greenModulusConst_mono {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {T T' : ℝ} (hT : 0 ≤ T)
    (hTT : T ≤ T') : greenModulusConst d T ≤ greenModulusConst d T' := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
  have hC0 : (0 : ℝ) ≤ 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) := by
    have := (greenDiffConst_pos hd).le
    positivity
  have hfac : greenModulusFactor d T ≤ greenModulusFactor d T' := by
    rw [greenModulusFactor, greenModulusFactor]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hT hTT hc.le) hc.le
  have hfac0 : 0 ≤ greenModulusFactor d T := greenModulusFactor_nonneg hd3 hT
  rw [greenModulusConst, greenModulusConst]
  have hsq : greenModulusFactor d T ^ 2 ≤ greenModulusFactor d T' ^ 2 := by
    nlinarith
  nlinarith

/-! ### A square-integrable increment -/

/-- The elementary inequality `(f-g)^2 ≤ 2f^2 + 2g^2` integrated: if `f^2`, `g^2` and `(f-g)^2` are
all integrable, the integral of `(f-g)^2` is at most twice the sum of the integrals of `f^2` and
`g^2`. -/
theorem integral_sq_sub_le_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun y => f y ^ 2) μ) (hg : Integrable (fun y => g y ^ 2) μ)
    (hfg : Integrable (fun y => (f y - g y) ^ 2) μ) :
    (∫ y, (f y - g y) ^ 2 ∂μ) ≤ 2 * (∫ y, f y ^ 2 ∂μ) + 2 * ∫ y, g y ^ 2 ∂μ := by
  have hpt : ∀ y, (f y - g y) ^ 2 ≤ 2 * f y ^ 2 + 2 * g y ^ 2 := by
    intro y
    nlinarith [sq_nonneg (f y + g y)]
  have hmono := integral_mono hfg ((hf.const_mul 2).add (hg.const_mul 2)) hpt
  simp only [Pi.add_apply] at hmono
  rwa [integral_add (hf.const_mul 2) (hg.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono

/-! ### The two inputs of the box bound -/

/-- **Both `L²` inputs of the Kolmogorov box bound fall below any threshold once the
horizon is large**, uniformly in the Brownian model: the kernel of the difference field is
small in `L²` at every centre, and its increment has a spatial modulus of exponent `1/6`
whose constant is just as small. -/
theorem eventually_diffKernel_bounds (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hdd : d = 2 ∨ d = 3) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB),
      IsProbabilityMeasure PB → ∀ (B : Space d → ℝ≥0 → ΩB → Space d),
      (∀ y, IsBrownian d y (B y) PB) → (∀ y ω, Continuous fun t => B y t ω) →
      (∀ y t, StronglyMeasurable (B y t)) →
      (∀ u : Space 2, (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y) ^ 2) ≤ ε)
        ∧ (∀ u v : Space 2,
          (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
              - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
            ≤ ε * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 6)) := by
  classical
  have hd : 1 ≤ d := by rcases hdd with rfl | rfl <;> norm_num
  have hd2 : 2 ≤ d := by rcases hdd with rfl | rfl <;> norm_num
  have hd3 : d ≤ 3 := by rcases hdd with rfl | rfl <;> norm_num
  have hd0 : 0 < d := hd
  set T₀ : ℝ := (blockLen d s : ℝ) with hT₀def
  have hT₀ : 0 < T₀ := by
    rw [hT₀def, ← NNReal.coe_zero, NNReal.coe_lt_coe]
    exact blockLen_pos hd0 hs0
  set A : ℝ := 2 * (2 * (d : ℝ)) ^ 2 * kernelShiftL2Const d s with hAdef
  set gmc : ℝ := greenModulusCoeff d with hgmcdef
  have hgmc : 0 < gmc := by
    have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
    have h1 := greenDiffConst_pos hd
    rw [hgmcdef, greenModulusCoeff]
    positivity
  have hkr : 0 ≤ kernelRateConst d s := kernelRateConst_nonneg hdd hs0
  clear_value gmc
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ kernelShiftL2Const d s := by
      have h2 : (0 : ℝ) ≤ kernelShiftL1Const d s ^ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg (kernelShiftL1Const_nonneg hdd s) _
      have h3 : (0 : ℝ) ≤
          2 ^ ((7 : ℝ) / 2) * ∫ z : Space d, centredKernel d s z ^ ((5 : ℝ) / 2) := by
        have := centredKernel_rpow_nonneg_integral hdd s
        positivity
      rw [kernelShiftL2Const]
      nlinarith
    rw [hAdef]
    positivity
  clear_value A
  -- the two thresholds
  set K : ℝ := 4 * kernelRateConst d s * (8 * gmc * T₀) with hKdef
  set c₀ : ℝ := (A + 8 * gmc * (1 + T₀)) / (8 * gmc * T₀) with hc₀def
  have hlim2 : Tendsto (fun n : ℕ => K * (((n : ℝ) + c₀)
      * (blockRatio ^ n) ^ ((1 : ℝ) / 3))) atTop (𝓝 0) := by
    have := (tendsto_linear_mul_blockRatio c₀).const_mul K
    rwa [mul_zero] at this
  have hlim1 : Tendsto (fun n : ℕ => kernelRateConst d s
      * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
    have := tendsto_blockRatio_rpow_third.const_mul (kernelRateConst d s)
    rwa [mul_zero] at this
  have hs16 : (0 : ℝ) < s ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos hs0 _
  set ε' : ℝ := min ε (ε * s ^ ((1 : ℝ) / 6) / 4) with hε'def
  have hε' : 0 < ε' := by
    rw [hε'def]
    exact lt_min hε (by positivity)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hlim1.eventually_le_const hε')
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (hlim2.eventually_le_const (show (0 : ℝ) < ε ^ 2 by positivity))
  set N : ℕ := max N₁ N₂ with hNdef
  filter_upwards [eventually_ge_atTop (((N : ℝ) + 1) * T₀)] with T hT
  intro ΩB _ PB hPB B hB hBc hBm
  -- the index of the horizon
  have hTpos : 0 < T := by
    have : (0 : ℝ) < ((N : ℝ) + 1) * T₀ := by positivity
    linarith
  set n : ℕ := ⌊T / T₀⌋₊ with hndef
  have hfloor := Nat.floor_le (le_of_lt (div_pos hTpos hT₀))
  have hnT : (n : ℝ) * T₀ ≤ T := by
    have h1 : (n : ℝ) ≤ T / T₀ := hfloor
    calc (n : ℝ) * T₀ ≤ (T / T₀) * T₀ := by nlinarith
      _ = T := by field_simp
  have hnN : N ≤ n := by
    have h1 : ((N : ℝ) + 1) ≤ T / T₀ := by
      rw [le_div_iff₀ hT₀]
      linarith
    have h2 : (N : ℕ) + 1 ≤ ⌊T / T₀⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      exact h1
    omega
  have hn0 : 0 < n := by
    have : N + 1 ≤ n := by
      have h1 : ((N : ℝ) + 1) ≤ T / T₀ := by
        rw [le_div_iff₀ hT₀]
        linarith
      refine Nat.le_floor ?_
      push_cast
      exact h1
    omega
  have hTn : T ≤ ((n : ℝ) + 1) * T₀ := by
    have h1 := Nat.lt_floor_add_one (T / T₀)
    have h2 : T / T₀ < (n : ℝ) + 1 := h1
    calc T = (T / T₀) * T₀ := by field_simp
      _ ≤ ((n : ℝ) + 1) * T₀ := by nlinarith
  -- the base-point bound
  have hbase : ∀ u : Space 2, (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) ^ 2)
      ≤ kernelRateConst d s * (blockRatio ^ n) ^ ((1 : ℝ) / 3) := fun u =>
    integral_sq_ballStoppedKernel_le_geometric hOcc hdd PB hB hBc hBm hs0 u hn0 hnT
  clear_value n
  clear_value T₀
  set R : ℝ := kernelRateConst d s with hRdef
  clear_value R
  have hrateε : R * (blockRatio ^ n) ^ ((1 : ℝ) / 3) ≤ ε' :=
    hN₁ n (le_trans (le_max_left _ _) hnN)
  refine ⟨fun u => (hbase u).trans (le_trans hrateε (min_le_left _ _)), ?_⟩
  intro u v
  set h : ℝ := ‖planePoint (d := d) u - planePoint (d := d) v‖ with hhdef
  have hh0 : 0 ≤ h := norm_nonneg _
  -- the two bounds on the increment
  have hmemU : MemLp (fun y : Space d => 2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) 2 (volume : Measure (Space d)) :=
    ((memLp_ballKernel hdd hs0 u).const_mul _).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hTpos.le u)
  have hmemV : MemLp (fun y : Space d => 2 * (d : ℝ) * ballKernel d s v y
      - ballStoppedKernel d PB B s T v y) 2 (volume : Measure (Space d)) :=
    ((memLp_ballKernel hdd hs0 v).const_mul _).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hTpos.le v)
  have hUint : Integrable (fun y : Space d => (2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) ^ 2) (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemU.aestronglyMeasurable).mp hmemU
  have hVint : Integrable (fun y : Space d => (2 * (d : ℝ) * ballKernel d s v y
      - ballStoppedKernel d PB B s T v y) ^ 2) (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemV.aestronglyMeasurable).mp hmemV
  have hDint : Integrable (fun y : Space d => ((2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y)
      - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
      (volume : Measure (Space d)) := by
    have hsub : MemLp (fun y : Space d => (2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) 2
        (volume : Measure (Space d)) := hmemU.sub hmemV
    exact (memLp_two_iff_integrable_sq hsub.aestronglyMeasurable).mp hsub
  have htriv : (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y)
      - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
      ≤ 4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) := by
    have h := integral_sq_sub_le_two hUint hVint hDint
    have h1 := hbase u
    have h2 := hbase v
    linarith
  rcases le_total h s with hw | hfar
  · have hh1 : h ≤ 1 := le_trans hw hs1
    have hmodulus : (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
        ≤ (A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3) := by
      have hbound := integral_sq_diffKernel_sub_le hdd PB hB hBc hBm hs0 hTpos u v hw hh1
      have hhalf : h ^ ((1 : ℝ) / 2) ≤ h ^ ((1 : ℝ) / 3) := by
        rcases eq_or_lt_of_le hh0 with h0 | h0
        · rw [← h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
        · exact Real.rpow_le_rpow_of_exponent_ge h0 hh1 (by norm_num)
      have hgm : greenModulusConst d T ≤ gmc * (1 + ((n : ℝ) + 1) * T₀) := by
        refine le_trans (greenModulusConst_mono hd hd3 hTpos.le hTn) ?_
        rw [hgmcdef]
        refine greenModulusConst_le_linear hd hd2 hd3 ?_
        have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
        exact mul_nonneg hn1 hT₀.le
      have hgm0 : (0 : ℝ) ≤ greenModulusConst d T := greenModulusConst_nonneg hd hd3 hTpos.le
      have hh13 : (0 : ℝ) ≤ h ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hh0 _
      have hh12 : (0 : ℝ) ≤ h ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hh0 _
      refine hbound.trans ?_
      have hstep1 : 8 * greenModulusConst d T * h ^ ((1 : ℝ) / 2)
          ≤ 8 * (gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3) := by
        have h1 : 8 * greenModulusConst d T * h ^ ((1 : ℝ) / 2)
            ≤ 8 * greenModulusConst d T * h ^ ((1 : ℝ) / 3) := by
          nlinarith only [hhalf, hgm0, hh12, hh13]
        have h2 : 8 * greenModulusConst d T * h ^ ((1 : ℝ) / 3)
            ≤ 8 * (gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3) := by
          nlinarith only [hgm, hh13]
        linarith only [h1, h2]
      have hA : 2 * (2 * (d : ℝ)) ^ 2 * kernelShiftL2Const d s * h ^ ((1 : ℝ) / 3)
          = A * h ^ ((1 : ℝ) / 3) := by rw [hAdef]
      have hring : (A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3)
          = A * h ^ ((1 : ℝ) / 3)
            + 8 * (gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3) := by
        ring
      rw [hring, ← hA]
      linarith only [hstep1]
    clear_value h
    -- the interpolation
    have hX0' : (0 : ℝ) ≤ 4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) := by
      have h1 : (0 : ℝ) ≤ (blockRatio ^ n) ^ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg (pow_nonneg blockRatio_pos.le n) _
      have h2 : (0 : ℝ) ≤ R * (blockRatio ^ n) ^ ((1 : ℝ) / 3) :=
        mul_nonneg hkr h1
      linarith only [h2]
    have hC0' : (0 : ℝ) ≤ A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀) := by
      have h2 : (0 : ℝ) ≤ 1 + ((n : ℝ) + 1) * T₀ := by
        have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1) * T₀ := mul_nonneg (by positivity) hT₀.le
        linarith only [h3]
      have h3 : (0 : ℝ) ≤ 8 * gmc := by linarith only [hgmc.le]
      have h4 : (0 : ℝ) ≤ 8 * gmc * (1 + ((n : ℝ) + 1) * T₀) := mul_nonneg h3 h2
      linarith only [hA0, h4]
    have hY0' : (0 : ℝ) ≤ (A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3) :=
      mul_nonneg hC0' (Real.rpow_nonneg hh0 _)
    have hmin : min (4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3)))
        ((A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3))
        ≤ (4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3))) ^ ((1 : ℝ) / 2)
          * ((A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2) := by
      have hm := min_le_rpow_mul_rpow hX0' hY0' (θ := (1 : ℝ) / 2) (by norm_num) (by norm_num)
      rw [show (1 : ℝ) - (1 : ℝ) / 2 = (1 : ℝ) / 2 by norm_num] at hm
      exact hm
    have hle : (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
        ≤ min (4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3)))
            ((A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀)) * h ^ ((1 : ℝ) / 3)) :=
      le_min htriv hmodulus
    refine le_trans (le_trans hle hmin) ?_
    -- the algebra of the interpolated constant
    set X : ℝ := 4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) with hXdef
    set C : ℝ := A + 8 * gmc * (1 + ((n : ℝ) + 1) * T₀) with hCdef
    have hX0 : 0 ≤ X := hX0'
    have hC0 : 0 ≤ C := hC0'
    have hh13 : (0 : ℝ) ≤ h ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hh0 _
    have hsplit : (C * h ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2)
        = C ^ ((1 : ℝ) / 2) * h ^ ((1 : ℝ) / 6) := by
      rw [Real.mul_rpow hC0 hh13, ← Real.rpow_mul hh0]
      norm_num
    rw [hsplit, ← mul_assoc, ← Real.mul_rpow hX0 hC0]
    have hprod : X * C ≤ ε ^ 2 := by
      have hkey := hN₂ n (le_trans (le_max_right _ _) hnN)
      have hexp : K * (((n : ℝ) + c₀) * (blockRatio ^ n) ^ ((1 : ℝ) / 3)) = X * C := by
        rw [hKdef, hc₀def, hXdef, hCdef]
        field_simp
        ring
      rw [hexp] at hkey
      exact hkey
    have hfin : (X * C) ^ ((1 : ℝ) / 2) ≤ ε := by
      have h1 : (X * C) ^ ((1 : ℝ) / 2) ≤ (ε ^ 2) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hprod (by norm_num)
      have h2 : ((ε ^ 2) : ℝ) ^ ((1 : ℝ) / 2) = ε := by
        rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
        norm_num
      rwa [h2] at h1
    have hh16 : (0 : ℝ) ≤ h ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hh0 _
    exact mul_le_mul_of_nonneg_right hfin hh16
  · -- the two centres are far apart: the trivial bound already suffices
    refine htriv.trans ?_
    have h1 : 4 * (R * (blockRatio ^ n) ^ ((1 : ℝ) / 3))
        ≤ ε * s ^ ((1 : ℝ) / 6) := by
      have h0 := le_trans hrateε (min_le_right _ _)
      linarith
    have h2 : s ^ ((1 : ℝ) / 6) ≤ h ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow hs0.le hfar (by norm_num)
    have h3 : ε * s ^ ((1 : ℝ) / 6) ≤ ε * h ^ ((1 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_left h2 hε.le
    linarith

/-! ### The moment form -/

/-- The white noise applied to the zero test function is almost surely zero, since
`IsWhiteNoise.smul` applied with scalar `0` collapses `W (0 • 0) = W 0` to the zero random
variable. -/
theorem ae_whiteNoise_zero {ΩW : Type*} [MeasurableSpace ΩW] {d : ℕ} {PW : Measure ΩW}
    {W : (Space d → ℝ) → ΩW → ℝ} (hW : IsWhiteNoise d W PW) :
    W (fun _ => (0 : ℝ)) =ᵐ[PW] fun _ => (0 : ℝ) := by
  have hmem : MemLp (fun _ : Space d => (0 : ℝ)) 2 (volume : Measure (Space d)) :=
    MemLp.zero'
  have h := hW.smul 0 (fun _ : Space d => (0 : ℝ)) hmem
  have hzero : (0 : ℝ) • (fun _ : Space d => (0 : ℝ)) = fun _ : Space d => (0 : ℝ) := by
    funext y
    simp
  rw [hzero] at h
  filter_upwards [h] with ω hω
  rw [hω]
  ring

/-- **The two moment inputs of the Kolmogorov box bound for the difference field**, below
any prescribed threshold once the horizon is large. -/
theorem eventually_diffField_moment_bounds (hOcc : Sandpile.External.BallOccupationDensity)
    {d : ℕ} (hdd : d = 2 ∨ d = 3) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {p : ℝ} (hp : 0 < p)
    {M₀ : ℝ} (hM₀ : 0 < M₀) :
    ∀ᶠ T : ℝ in atTop, ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW),
      IsProbabilityMeasure PW → ∀ (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB), IsProbabilityMeasure PB →
      ∀ (B : Space d → ℝ≥0 → ΩB → Space d), (∀ y, IsBrownian d y (B y) PB) →
      (∀ y ω, Continuous fun t => B y t ω) → (∀ y t, StronglyMeasurable (B y t)) →
      (∀ u : Space 2, (∫ ω, |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y) ω| ^ p ∂PW) ≤ M₀)
        ∧ (∀ u v : Space 2, (∫ ω, |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
              - ballStoppedKernel d PB B s T u y) ω
            - W (fun y => 2 * (d : ℝ) * ballKernel d s v y
              - ballStoppedKernel d PB B s T v y) ω| ^ p ∂PW)
          ≤ M₀ * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ (p / 12)) := by
  have hd : 1 ≤ d := by rcases hdd with rfl | rfl <;> norm_num
  have hd3 : d ≤ 3 := by rcases hdd with rfl | rfl <;> norm_num
  have hm0 : 0 ≤ gaussAbsMoment p := gaussAbsMoment_nonneg p
  set ε : ℝ := min 1 ((M₀ / (gaussAbsMoment p + 1)) ^ (2 / p)) with hεdef
  have hε : 0 < ε := by
    refine lt_min one_pos (Real.rpow_pos_of_pos ?_ _)
    positivity
  have hεp : ε ^ (p / 2) * gaussAbsMoment p ≤ M₀ := by
    have h1 : ε ^ (p / 2) ≤ ((M₀ / (gaussAbsMoment p + 1)) ^ (2 / p)) ^ (p / 2) :=
      Real.rpow_le_rpow hε.le (min_le_right _ _) (by positivity)
    have h2 : ((M₀ / (gaussAbsMoment p + 1)) ^ (2 / p)) ^ (p / 2)
        = M₀ / (gaussAbsMoment p + 1) := by
      rw [← Real.rpow_mul (by positivity)]
      rw [show 2 / p * (p / 2) = 1 by field_simp]
      exact Real.rpow_one _
    rw [h2] at h1
    have h3 : M₀ / (gaussAbsMoment p + 1) * gaussAbsMoment p ≤ M₀ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have h4 : ε ^ (p / 2) * gaussAbsMoment p
        ≤ M₀ / (gaussAbsMoment p + 1) * gaussAbsMoment p :=
      mul_le_mul_of_nonneg_right h1 hm0
    linarith
  filter_upwards [eventually_diffKernel_bounds hOcc hdd hs0 hs1 hε,
    eventually_gt_atTop (0 : ℝ)] with T hT hTpos
  intro ΩW _ PW hPW W hW ΩB _ PB hPB B hB hBc hBm
  obtain ⟨hbase, hmod⟩ := hT ΩB PB hPB B hB hBc hBm
  have hmem : ∀ u : Space 2, MemLp (fun y : Space d => 2 * (d : ℝ) * ballKernel d s u y
      - ballStoppedKernel d PB B s T u y) 2 (volume : Measure (Space d)) := by
    intro u
    exact ((memLp_ballKernel hdd hs0 u).const_mul _).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hTpos.le u)
  constructor
  · intro u
    have hzero := ae_whiteNoise_zero hW
    have hval := integral_abs_rpow_whiteNoise_sub PW W hW
      (fun y : Space d => 2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
      (fun _ => (0 : ℝ)) (hmem u) MemLp.zero' hp.le
    have hrw : (∫ ω, |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ω| ^ p ∂PW)
        = ∫ ω, |W (fun y => 2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y) ω - W (fun _ => (0 : ℝ)) ω| ^ p ∂PW := by
      refine integral_congr_ae ?_
      filter_upwards [hzero] with ω hω
      rw [hω]
      simp
    rw [hrw, hval]
    have hsub : (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) - 0) ^ 2)
        = ∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y) ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      ring_nf
    rw [hsub]
    have h0 : (0 : ℝ) ≤ ∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ^ 2 := integral_nonneg fun y => sq_nonneg _
    have h1 : (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y) ^ 2) ^ (p / 2) ≤ ε ^ (p / 2) :=
      Real.rpow_le_rpow h0 (hbase u) (by positivity)
    calc (∫ y : Space d, (2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y) ^ 2) ^ (p / 2) * gaussAbsMoment p
        ≤ ε ^ (p / 2) * gaussAbsMoment p := mul_le_mul_of_nonneg_right h1 hm0
      _ ≤ M₀ := hεp
  · intro u v
    set h : ℝ := ‖planePoint (d := d) u - planePoint (d := d) v‖ with hhdef
    have hh0 : 0 ≤ h := norm_nonneg _
    have hval := integral_abs_rpow_whiteNoise_sub PW W hW
      (fun y : Space d => 2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
      (fun y : Space d => 2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)
      (hmem u) (hmem v) hp.le
    rw [hval]
    have h0 : (0 : ℝ) ≤ ∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2 :=
      integral_nonneg fun y => sq_nonneg _
    have h1 : (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
        - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2) ^ (p / 2)
        ≤ (ε * h ^ ((1 : ℝ) / 6)) ^ (p / 2) :=
      Real.rpow_le_rpow h0 (hmod u v) (by positivity)
    have h2 : (ε * h ^ ((1 : ℝ) / 6)) ^ (p / 2)
        = ε ^ (p / 2) * h ^ (p / 12) := by
      rw [Real.mul_rpow hε.le (Real.rpow_nonneg hh0 _), ← Real.rpow_mul hh0]
      congr 2
      ring
    rw [h2] at h1
    have hh12 : (0 : ℝ) ≤ h ^ (p / 12) := Real.rpow_nonneg hh0 _
    calc (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y
          - ballStoppedKernel d PB B s T u y)
          - (2 * (d : ℝ) * ballKernel d s v y
            - ballStoppedKernel d PB B s T v y)) ^ 2) ^ (p / 2) * gaussAbsMoment p
        ≤ (ε ^ (p / 2) * h ^ (p / 12)) * gaussAbsMoment p :=
          mul_le_mul_of_nonneg_right h1 hm0
      _ = (ε ^ (p / 2) * gaussAbsMoment p) * h ^ (p / 12) := by ring
      _ ≤ M₀ * h ^ (p / 12) := mul_le_mul_of_nonneg_right hεp hh12

end Sandpile.Support
