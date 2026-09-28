import Sandpile.Support.D4SCellL2
import Sandpile.Support.D4SPlancherel
import Sandpile.Support.D4DefectOmega
import Sandpile.Support.TightNegSobolev

/-!
# The `H^{-s}(D)` norm of the `ω`-representative of a rescaled lattice field

This file bounds the `H^{-s}(D)` norm of the `ω`-representative of a rescaled lattice field,
in the form Steps 2 and 3 of `prop:d4-superdiffusive-limit` use it (`sandpile.tex:3368-3404`).
The norm is the supremum of `|f^{(R)}(φ̃)|` over test functions with `‖φ‖_{H^s}≤1`, and
`φ̃ = φ-ω∫_Dφ` is supported in `D` for every one of them. Two facts make the supremum
computable. First, the `H^s` unit ball sits inside the `L²` unit ball (Plancherel), so `∫φ̃²`
is bounded by a constant of `D` and `ω` alone. Second, Cauchy-Schwarz over the cells of the
mesh separates the field from the test function. Together they bound the norm by
`K√(R^{-d}∑_x f(x)^2)` over the cells that `D` meets, a finite sum of the field's values and
hence a random variable whose expectation is controlled by the uniform second moment of the
field.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- **The `L²` norm of the `ω`-shift is bounded on the `H^s` unit ball.**  For
`s ≥ 0` and a test function `φ` with `‖φ‖_{H^s}\leq1`, the shifted function
`φ̃ = φ-ω∫_Dφ` has `∫φ̃²` at most a constant of `D` and `ω` alone. -/
theorem exists_integral_sq_omegaShift_le {s : ℝ} (hs : 0 ≤ s)
    {D : Set (Space d)} (hD : IsDomain D) {w : Space d → ℝ} (hw : IsAveragingDensity D w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
      ∫ z : Space d, omegaShift D w φ z ^ 2 ≤ K := by
  classical
  obtain ⟨hwt, hwnn, hw1⟩ := hw
  obtain ⟨hwsm, hwcs, hwsupp⟩ := hwt
  have hwc2 : Continuous (fun z : Space d => w z ^ 2) := hwsm.continuous.pow 2
  have hwk2 : HasCompactSupport (fun z : Space d => w z ^ 2) :=
    hwcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hwint2 : Integrable (fun z : Space d => w z ^ 2) :=
    hwc2.integrable_of_hasCompactSupport hwk2
  set VD : ℝ := (volume D).toReal with hVD
  refine ⟨2 + 2 * VD * ∫ z : Space d, w z ^ 2, by positivity, ?_⟩
  intro φ hφ hnorm
  obtain ⟨hφsm, hφcs, hφsupp⟩ := hφ
  have hφc2 : Continuous (fun z : Space d => φ z ^ 2) := hφsm.continuous.pow 2
  have hφk2 : HasCompactSupport (fun z : Space d => φ z ^ 2) :=
    hφcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hφint2 : Integrable (fun z : Space d => φ z ^ 2) :=
    hφc2.integrable_of_hasCompactSupport hφk2
  have hφ2 : ∫ z : Space d, φ z ^ 2 ≤ 1 :=
    integral_sq_le_one_of_sobolevNormSq_le d s hs φ hφsm hφcs hnorm
  have hDne : volume D ≠ ⊤ := (hD.2.1.measure_lt_top).ne
  have hc2 : (∫ z in D, φ z) ^ 2 ≤ VD := by
    have hφint : Integrable φ := hφsm.continuous.integrable_of_hasCompactSupport hφcs
    have h := sq_setIntegral_le D φ hφint.integrableOn hφint2.integrableOn hDne
    have h2 : ∫ z in D, φ z ^ 2 ≤ ∫ z, φ z ^ 2 :=
      setIntegral_le_integral hφint2 (Filter.Eventually.of_forall fun z => sq_nonneg _)
    have hVDnn : (0:ℝ) ≤ VD := by rw [hVD]; exact ENNReal.toReal_nonneg
    calc (∫ z in D, φ z) ^ 2 ≤ VD * ∫ z in D, φ z ^ 2 := h
      _ ≤ VD * 1 := mul_le_mul_of_nonneg_left (le_trans h2 hφ2) hVDnn
      _ = VD := mul_one _
  have hptw : ∀ z : Space d,
      omegaShift D w φ z ^ 2 ≤ 2 * φ z ^ 2 + 2 * (∫ y in D, φ y) ^ 2 * w z ^ 2 := by
    intro z
    have : omegaShift D w φ z = φ z - w z * ∫ y in D, φ y := rfl
    rw [this]
    nlinarith [sq_nonneg (φ z + w z * ∫ y in D, φ y)]
  have hmaj : Integrable (fun z : Space d =>
      2 * φ z ^ 2 + 2 * (∫ y in D, φ y) ^ 2 * w z ^ 2) :=
    (hφint2.const_mul 2).add (hwint2.const_mul _)
  have hshift2 : Integrable (fun z : Space d => omegaShift D w φ z ^ 2) := by
    have hsm : Continuous (omegaShift D w φ) :=
      hφsm.continuous.sub (hwsm.continuous.mul continuous_const)
    have hcs : HasCompactSupport (omegaShift D w φ) := hφcs.sub (hwcs.mul_right)
    have hsq : Continuous (fun z : Space d => omegaShift D w φ z ^ 2) := hsm.pow 2
    have hksq : HasCompactSupport (fun z : Space d => omegaShift D w φ z ^ 2) :=
      hcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact hsq.integrable_of_hasCompactSupport hksq
  have hmono := integral_mono hshift2 hmaj hptw
  rw [integral_add (hφint2.const_mul 2) (hwint2.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  have hwnn2 : (0:ℝ) ≤ ∫ z : Space d, w z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hVDnn : (0:ℝ) ≤ VD := by rw [hVD]; exact ENNReal.toReal_nonneg
  have hstep : 2 * (∫ y in D, φ y) ^ 2 * ∫ z : Space d, w z ^ 2 ≤
      2 * VD * ∫ z : Space d, w z ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hwnn2
  linarith


/-- **The `H^{-s}(D)` norm of an `ω`-representative.**  For every rescaled
lattice field `f`, the norm of `[f^{(R)}]^ω` is at most a constant of `D`, `ω`
and `s` times `(R^{-d}∑_x f(x)^2)^{1/2}`, the sum running over the cells of the
mesh that `D` meets.  The right side is a finite sum of the field's values, so
its expectation is controlled by the uniform second moment of the field; this is
how Steps 2 and 3 of `prop:d4-superdiffusive-limit` pass from a pointwise second
moment to an `H^{-s}(D)` bound (`sandpile.tex:3368-3404`). -/
theorem exists_negSobolevNorm_omegaRep_le {s : ℝ} (hs : 0 ≤ s)
    {D : Set (Space d)} (hD : IsDomain D) {w : Space d → ℝ} (hw : IsAveragingDensity D w) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ R : ℝ, 0 < R → ∀ g : Sandpile.Site d → ℝ,
      negSobolevNorm d s D (omegaRep D w (latticePairing R g)) ≤
        ENNReal.ofReal (K * Real.sqrt (R⁻¹ ^ d *
          ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * L⌉₊ + 1), g x ^ 2)) := by
  classical
  obtain ⟨K0, hK0, hK0b⟩ := exists_integral_sq_omegaShift_le hs hD hw
  obtain ⟨r, hr⟩ := hD.2.1.subset_closedBall (0 : Space d)
  refine ⟨Real.sqrt K0, max r 0, Real.sqrt_nonneg _, le_max_right _ _, ?_⟩
  intro R hR g
  have hLb : ∀ z ∈ D, ‖z‖ ≤ max r 0 := by
    intro z hz
    have := hr hz
    rw [mem_closedBall_zero_iff] at this
    exact le_trans this (le_max_left _ _)
  refine sSup_le ?_
  rintro v ⟨φ, hφ, hn, rfl⟩
  obtain ⟨hwt, hwnn, hw1⟩ := hw
  have hshift : IsTestFn (Set.univ : Set (Space d)) (omegaShift D w φ) :=
    isTestFn_univ_omegaShift hwt hφ
  have hsm : Continuous (omegaShift D w φ) := hshift.1.continuous
  have hcs : HasCompactSupport (omegaShift D w φ) := hshift.2.1
  have hint : Integrable (omegaShift D w φ) := hsm.integrable_of_hasCompactSupport hcs
  have hsq : Continuous (fun z : Space d => omegaShift D w φ z ^ 2) := hsm.pow 2
  have hksq : HasCompactSupport (fun z : Space d => omegaShift D w φ z ^ 2) :=
    hcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hint2 : Integrable (fun z : Space d => omegaShift D w φ z ^ 2) :=
    hsq.integrable_of_hasCompactSupport hksq
  have hsupp : ∀ z : Space d, omegaShift D w φ z ≠ 0 → ‖z‖ ≤ max r 0 := by
    intro z hz
    by_cases hφz : φ z = 0
    · have hwz : w z ≠ 0 := by
        intro hwz
        exact hz (by show φ z - w z * _ = 0; rw [hφz, hwz]; ring)
      exact hLb z (hwt.2.2 (subset_tsupport _ hwz))
    · exact hLb z (hφ.2.2 (subset_tsupport _ hφz))
  have hmem : ∀ z : Space d, omegaShift D w φ z ≠ 0 →
      (fun i => ⌊R * z i⌋) ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1) :=
    fun z hz => floor_mem_boxFinset R z (hsupp z hz)
  have hpair := abs_latticePairing_le hR g (omegaShift D w φ) hint hint2 _ hmem
  have hrep : omegaRep D w (latticePairing R g) φ = latticePairing R g (omegaShift D w φ) := rfl
  rw [hrep]
  refine ENNReal.ofReal_le_ofReal (le_trans hpair ?_)
  have hA : (0:ℝ) ≤
      ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1), g x ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hB : (0:ℝ) ≤ R⁻¹ ^ d := by positivity
  have hC : (0:ℝ) ≤ ∫ z : Space d, omegaShift D w φ z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hCK : ∫ z : Space d, omegaShift D w φ z ^ 2 ≤ K0 := hK0b φ hφ hn
  calc Real.sqrt (∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1), g x ^ 2) *
        Real.sqrt (R⁻¹ ^ d * ∫ z : Space d, omegaShift D w φ z ^ 2)
      = Real.sqrt
          ((∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1), g x ^ 2) *
            (R⁻¹ ^ d * ∫ z : Space d, omegaShift D w φ z ^ 2)) := (Real.sqrt_mul hA _).symm
    _ ≤ Real.sqrt (K0 * (R⁻¹ ^ d *
          ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1), g x ^ 2)) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [mul_nonneg hA hB]
    _ = Real.sqrt K0 * Real.sqrt (R⁻¹ ^ d *
          ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * max r 0⌉₊ + 1), g x ^ 2) :=
        Real.sqrt_mul hK0 _

end Sandpile.Support
