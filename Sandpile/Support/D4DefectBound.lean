/-
The `ℓ²` bound on the truncation defect of Step 1 of
`prop:d4-superdiffusive-limit`.

The defect at a site `y` is the `ω`-representative of the pairing of
`g_t(·,y) - a(·,y)` with a test function.  Over the cells of the mesh this is a
finite sum `∑_x (G(0,y) - ∑_{j≥t}p_j(x,y))m_R(x)`, and the `ω`-shift has total
mass zero, so both the site-free term `G(0,y)` and the site-free subtraction
`∑_{j≥t}p_j(0,y)` drop out: the defect is the pairing of the CENTRED tail
`Δ_t(x,y) = ∑_{j≥t}(p_j(x,y)-p_j(0,y))`.  Cauchy-Schwarz over the cells and the
uniform `ℓ²` bound on `Δ_t(x,·)` for `|x| ≤ CR` then give
`∑_y (defect)² ≤ A R t^{-1/2}`, which vanishes at `t = ⌊R^α⌋` exactly when
`α > 2`.
-/
import Sandpile.Support.D4DefectOmega
import Sandpile.Support.ContRiemann
import Sandpile.External.MembraneScalingFour

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum

/-- **The truncation defect is the pairing of the centred tail.** -/
theorem membraneDefect_eq_neg_sum {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ)
    {L : ℝ} (hL : ∀ z, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ L)
    (hint : Integrable (omegaShift D w φ))
    (R : ℝ) (t : ℕ) (y : Site 4) :
    Sandpile.External.membraneDefect R t D w φ y =
      -∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
        (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) *
          cellMass R (omegaShift D w φ) x := by
  classical
  set s := Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1) with hs_def
  have hs : ∀ z : Space 4, omegaShift D w φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s :=
    fun z hz => floor_mem_boxFinset R z (hL z hz)
  -- the total cell mass is the integral of the shift, which vanishes
  have hmass : ∑ x ∈ s, cellMass R (omegaShift D w φ) x = 0 := by
    have h1 : Sandpile.Continuum.latticePairing R (fun _ : Site 4 => (1 : ℝ))
        (omegaShift D w φ) = ∑ x ∈ s, (1 : ℝ) * cellMass R (omegaShift D w φ) x :=
      latticePairing_eq_sum R _ _ hint s hs
    have h2 : Sandpile.Continuum.latticePairing R (fun _ : Site 4 => (1 : ℝ))
        (omegaShift D w φ) = ∫ z, omegaShift D w φ z := by
      show ∫ z : Space 4, Sandpile.Continuum.embed R (fun _ : Site 4 => (1 : ℝ)) z *
        omegaShift D w φ z = _
      simp [Sandpile.Continuum.embed]
    rw [h2, integral_omegaShift_eq_zero hw hφ] at h1
    simpa using h1.symm
  -- the pairing over the cells
  have hpair : Sandpile.External.membraneDefect R t D w φ y =
      ∑ x ∈ s, (greenTime 4 t x y - potentialKernel 4 x y) *
        cellMass R (omegaShift D w φ) x :=
    latticePairing_eq_sum R _ _ hint s hs
  rw [hpair]
  have hterm : ∀ x : Site 4, (greenTime 4 t x y - potentialKernel 4 x y) =
      green 4 0 y - ∑' j : ℕ, heatKernel 4 (t + j) x y := by
    intro x
    rw [greenTime_sub_potentialKernel (by norm_num) t x y]
    congr 1
    exact tsum_congr fun j => by rw [Nat.add_comm]
  have hsum0 : ∑ x ∈ s, (∑' j : ℕ, heatKernel 4 (t + j) 0 y) *
      cellMass R (omegaShift D w φ) x = 0 := by
    rw [← Finset.mul_sum, hmass, mul_zero]
  have hsumG : ∑ x ∈ s, green 4 0 y * cellMass R (omegaShift D w φ) x = 0 := by
    rw [← Finset.mul_sum, hmass, mul_zero]
  have hsplit : ∀ x : Site 4,
      (greenTime 4 t x y - potentialKernel 4 x y) * cellMass R (omegaShift D w φ) x =
        green 4 0 y * cellMass R (omegaShift D w φ) x -
          (∑' j : ℕ, heatKernel 4 (t + j) 0 y) * cellMass R (omegaShift D w φ) x -
          (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) *
            cellMass R (omegaShift D w φ) x := by
    intro x
    have hsub : ∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y) =
        (∑' j : ℕ, heatKernel 4 (t + j) x y) - ∑' j : ℕ, heatKernel 4 (t + j) 0 y :=
      Summable.tsum_sub (summable_heatKernel_shift (by norm_num) t x y)
        (summable_heatKernel_shift (by norm_num) t 0 y)
    rw [hterm x, hsub]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hsplit x), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hsumG, hsum0]
  ring

/-- **The `ℓ²` bound on the truncation defect.**  For every test function there
is a constant `A` with `∑_y (defect at scale R and time t)² ≤ A R t^{-1/2}`,
uniformly for `R ≥ 1` and `t ≥ 1`. -/
theorem exists_tsum_sq_membraneDefect_le (hHK : Sandpile.External.HeatKernelBounds)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ t : ℕ, 1 ≤ t →
      ∑' y : Site 4, ENNReal.ofReal (Sandpile.External.membraneDefect R t D w φ y ^ 2) ≤
        ENNReal.ofReal (A * R * (t : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C3, hC3, hall⟩ := exists_heatKernel_tail_l2_four_all hHK
  obtain ⟨Cb, L, hCb0, hL0, hbnd, hLsupp, hint⟩ :=
    exists_bound_of_isTestFn (isTestFn_univ_omegaShift hw.1 hφ)
  set M := ∫ z : Space 4, |omegaShift D w φ z| with hM_def
  have hM0 : (0 : ℝ) ≤ M := integral_nonneg fun z => abs_nonneg _
  refine ⟨M * M * C3 * (2 * L + 5), by positivity, fun R hR t ht => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have habsR : |R| = R := abs_of_pos hR0
  have hpow : (0 : ℝ) ≤ (t : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg t) _
  set s := Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1) with hs_def
  set B := C3 * ((2 * L + 5) * R) * (t : ℝ) ^ (-(1 : ℝ) / 2) with hB_def
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hMsum : ∑ x ∈ s, |cellMass R (omegaShift D w φ) x| ≤ M :=
    Sandpile.Support.sum_abs_cellMass_le R _ hint s
  have hsqrt4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hBx : ∀ x ∈ s, ∑' y : Site 4, ENNReal.ofReal
      ((∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) ^ 2) ≤
      ENNReal.ofReal B := by
    intro x hx
    refine le_trans (hall t ht x) (ENNReal.ofReal_le_ofReal ?_)
    have hdx : Sandpile.External.latticeDist x 0 ≤ 2 * ((⌈|R| * L⌉₊ : ℝ) + 1) := by
      have h := Sandpile.Support.latticeDist_le_of_mem_boxFinset (d := 4) hx
      rw [hsqrt4] at h
      calc Sandpile.External.latticeDist x 0 ≤ 2 * ((⌈|R| * L⌉₊ + 1 : ℕ) : ℝ) := h
        _ = 2 * ((⌈|R| * L⌉₊ : ℝ) + 1) := by push_cast; ring
    have hceil : (⌈|R| * L⌉₊ : ℝ) ≤ R * L + 1 := by
      rw [habsR]
      have := Nat.ceil_lt_add_one (a := R * L) (by positivity)
      linarith
    have hfin : Sandpile.External.latticeDist x 0 + 1 ≤ (2 * L + 5) * R := by
      nlinarith [hdx, hceil, hR, hL0, hR0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfin hC3.le) hpow
  have hkey := tsum_sq_finset_pairing_le (d := 4) s (cellMass R (omegaShift D w φ))
    (fun x y => ∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y))
    hM0 hMsum hB0 hBx
  have hid : ∀ y : Site 4, Sandpile.External.membraneDefect R t D w φ y ^ 2 =
      (∑ x ∈ s, (∑' j : ℕ, (heatKernel 4 (t + j) x y - heatKernel 4 (t + j) 0 y)) *
        cellMass R (omegaShift D w φ) x) ^ 2 := by
    intro y
    rw [membraneDefect_eq_neg_sum hw hφ hLsupp hint R t y]
    ring
  rw [tsum_congr fun y => congrArg ENNReal.ofReal (hid y)]
  refine le_trans hkey (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hB_def]
  ring

/-- **The truncation defect vanishes at superdiffusive times.**  This is the
`ℓ²` hypothesis of `Sandpile.External.MembraneScalingLimitFour`, discharged at
`t_R = ⌊R^α⌋` for `α > 2`: the bound `A R t^{-1/2}` at `t = ⌊R^α⌋` is the square
of `R^{1/2}⌊R^α⌋^{-1/4}`, which vanishes exactly when `α > 2`. -/
theorem tendsto_tsum_sq_membraneDefect (hHK : Sandpile.External.HeatKernelBounds)
    {D : Set (Space 4)} {w φ : Space 4 → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ) {α : ℝ} (hα : 2 < α) :
    Tendsto (fun R : ℝ => ∑' y : Site 4,
        ENNReal.ofReal (Sandpile.External.membraneDefect R ⌊R ^ α⌋₊ D w φ y ^ 2))
      atTop (nhds 0) := by
  obtain ⟨A, hA0, hbound⟩ := exists_tsum_sq_membraneDefect_le hHK hw hφ
  have hsq : Tendsto
      (fun R : ℝ => A * (R ^ (2⁻¹ : ℝ) * ((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ))) ^ 2)
      atTop (nhds 0) := by
    have h := (tendsto_superdiffusive_defect_scale hα).pow 2
    simpa using h.const_mul A
  have hscale : Tendsto (fun R : ℝ => A * (R * ((⌊R ^ α⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2)))
      atTop (nhds 0) := by
    refine hsq.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have hR0 : (0 : ℝ) < R := by linarith
    have h1 : (R ^ (2⁻¹ : ℝ)) ^ 2 = R := by
      rw [← Real.rpow_natCast (R ^ (2⁻¹ : ℝ)) 2, ← Real.rpow_mul hR0.le]
      norm_num
    have h2 : (((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ))) ^ 2 = ((⌊R ^ α⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ))) 2,
        ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    rw [mul_pow, h1, h2]
  have hup : Tendsto (fun R : ℝ => ENNReal.ofReal
      (A * (R * ((⌊R ^ α⌋₊ : ℝ)) ^ (-(1 : ℝ) / 2)))) atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hscale
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Filter.Eventually.of_forall fun R => zero_le) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRa : (2 : ℝ) ≤ R ^ α := by
    calc (2 : ℝ) ≤ R := hR
      _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R ^ α := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hfl : 1 ≤ ⌊R ^ α⌋₊ := by
    have : (1 : ℝ) ≤ R ^ α := by linarith
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro hc
      have := Nat.floor_eq_zero.mp hc
      linarith)
  refine le_trans (hbound R hR1 _ hfl) (le_of_eq ?_)
  congr 1
  ring

end Sandpile
