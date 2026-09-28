import Sandpile.Support.D4SStep2Second

/-!
# The pairing form of Step 2 at a fixed test function

The pairing form of the two displays of Step 2, at a FIXED test function
(`sandpile.tex:3368-3382`).

The frozen statement of `prop:d4-superdiffusive-limit` has two clauses: a convergence in
distribution of the pairing with each test function, and tightness of the `H^{-s}(D)` norms.
The norm is a supremum over the `H^s` unit ball, so a bound uniform on that ball serves the
second clause but says nothing about a test function of large `H^s` norm. For the first
clause the bounds are therefore repeated at one fixed test function, where they are in fact
easier: a fixed test function is Lipschitz, so its modulus of continuity at scale `1/R` is
`R^{-1}` with no Fourier weight, and the rate of the second display improves from
`R^{-\min\{s,1\}}` to `R^{-1}`. The two main results are `exists_abs_pairing_omegaRep_le`
and `exists_abs_pairing_parityConst_le`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support
open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The support radius of a bounded domain. -/
theorem exists_radius_of_isDomain {D : Set (Space d)} (hD : IsDomain D) :
    ∃ Lw : ℝ, 0 ≤ Lw ∧ ∀ z ∈ D, ‖z‖ ≤ Lw := by
  obtain ⟨r, hr⟩ := hD.2.1.subset_closedBall (0 : Space d)
  refine ⟨max r 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hr hz
  rw [mem_closedBall_zero_iff] at h
  exact le_trans h (le_max_left _ _)

/-- The `ω`-shift of a test function vanishes outside the radius of the domain. -/
theorem omegaShift_support {D : Set (Space d)} {w φ : Space d → ℝ}
    (hw : IsTestFn D w) (hφ : IsTestFn D φ) {Lw : ℝ} (hLw : ∀ z ∈ D, ‖z‖ ≤ Lw)
    (z : Space d) (hz : omegaShift D w φ z ≠ 0) : ‖z‖ ≤ Lw := by
  by_cases hφz : φ z = 0
  · have hwz : w z ≠ 0 := by
      intro hc
      exact hz (by show φ z - w z * _ = 0; rw [hφz, hc]; ring)
    exact hLw z (hw.2.2 (subset_tsupport _ hwz))
  · exact hLw z (hφ.2.2 (subset_tsupport _ hφz))

/-- **The first display, in pairing form at one test function.** -/
theorem exists_abs_pairing_omegaRep_le {D : Set (Space d)} (hD : IsDomain D)
    {w : Space d → ℝ} (hw : IsAveragingDensity D w) {φ : Space d → ℝ} (hφ : IsTestFn D φ) :
    ∃ K L : ℝ, 0 ≤ K ∧ 0 ≤ L ∧ ∀ R : ℝ, 0 < R → ∀ g : Sandpile.Site d → ℝ,
      |omegaRep D w (latticePairing R g) φ| ≤
        K * Real.sqrt (R⁻¹ ^ d *
          ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * L⌉₊ + 1), g x ^ 2) := by
  classical
  obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
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
  refine ⟨Real.sqrt (∫ z : Space d, omegaShift D w φ z ^ 2), Lw, Real.sqrt_nonneg _, hLw0, ?_⟩
  intro R hR g
  have hmem : ∀ z : Space d, omegaShift D w φ z ≠ 0 →
      (fun i => ⌊R * z i⌋) ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * Lw⌉₊ + 1) :=
    fun z hz => floor_mem_boxFinset R z (omegaShift_support hwt hφ hLw z hz)
  have hpair := abs_latticePairing_le hR g (omegaShift D w φ) hint hint2 _ hmem
  have hrep : omegaRep D w (latticePairing R g) φ = latticePairing R g (omegaShift D w φ) := rfl
  rw [hrep]
  refine le_trans hpair (le_of_eq ?_)
  have hA : (0:ℝ) ≤ ∑ x ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * Lw⌉₊ + 1), g x ^ 2 :=
    Finset.sum_nonneg fun x _ => sq_nonneg _
  have hB : (0:ℝ) ≤ R⁻¹ ^ d := by positivity
  have hC : (0:ℝ) ≤ ∫ z : Space d, omegaShift D w φ z ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  rw [← Real.sqrt_mul hA, ← Real.sqrt_mul hC]
  congr 1
  ring

/-- **The second display, in pairing form at one test function.**  The shifted
test function is Lipschitz, so its modulus of continuity at the scale of one
mesh step is `R^{-1}`. -/
theorem exists_abs_pairing_parityConst_le {D : Set (Space d)} (hD : IsDomain D)
    {w : Space d → ℝ} (hw : IsAveragingDensity D w) (i₀ : Fin d)
    {φ : Space d → ℝ} (hφ : IsTestFn D φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ (C : Sandpile.Site d → ℝ) (c₀ c₁ : ℝ),
      (∀ x : Sandpile.Site d, Sandpile.External.SameParity x 0 → C x = c₀) →
      (∀ x : Sandpile.Site d, ¬ Sandpile.External.SameParity x 0 → C x = c₁) →
      |omegaRep D w (latticePairing R C) φ| ≤ K * |c₀ - c₁| * R⁻¹ := by
  classical
  obtain ⟨Lw, hLw0, hLw⟩ := exists_radius_of_isDomain hD
  obtain ⟨hwt, hwnn, hw1⟩ := hw
  have hshift : IsTestFn (Set.univ : Set (Space d)) (omegaShift D w φ) :=
    isTestFn_univ_omegaShift hwt hφ
  obtain ⟨Cw, hCw0, hCw⟩ := exists_integral_sq_sub_translate_testFn hshift
  set A : Set (Space d) := Metric.closedBall (0 : Space d) (Lw + 1) with hA
  have hAvol : volume A ≠ ⊤ := (isCompact_closedBall (0 : Space d) (Lw + 1)).measure_lt_top.ne
  refine ⟨(1/2) * Real.sqrt ((volume A).toReal) * Real.sqrt Cw, by positivity, ?_⟩
  intro R hR C c₀ c₁ hC₀ hC₁
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set h : Space d := meshStep d R i₀ with hh
  have hnh : ‖h‖ = R⁻¹ := by rw [hh, norm_meshStep, abs_of_pos (by positivity)]
  set ψ : Space d → ℝ := omegaShift D w φ with hψ
  have hψsm : Continuous ψ := hshift.1.continuous
  have hψcs : HasCompactSupport ψ := hshift.2.1
  have hψint : Integrable ψ := hψsm.integrable_of_hasCompactSupport hψcs
  have hψmean : ∫ z : Space d, ψ z = 0 :=
    integral_omegaShift_eq_zero ⟨hwt, hwnn, hw1⟩ hφ
  have hψsupp : ∀ z : Space d, ψ z ≠ 0 → ‖z‖ ≤ Lw := omegaShift_support hwt hφ hLw
  set S : Finset (Sandpile.Site d) :=
    Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * Lw⌉₊ + 1) with hS
  have hmem : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ S :=
    fun z hz => floor_mem_boxFinset R z (hψsupp z hz)
  have hpairsum := latticePairing_eq_sum R C ψ hψint S hmem
  have hmass : ∑ x ∈ S, cellMass R ψ x = 0 := by
    rw [sum_cellMass_eq R ψ hψint S hmem, hψmean]
  have hparity := sum_parity_const_mul S C (cellMass R ψ) c₀ c₁ hC₀ hC₁ hmass
  have hfilter := sum_filter_cellMass_eq R ψ hψint S hmem
  have hrep : omegaRep D w (latticePairing R C) φ = latticePairing R C ψ := rfl
  have himb := abs_integral_mul_parityChar_le (d := d) hR0 i₀ ψ hψint hψmean
  have hdsm : Continuous (fun z : Space d => ψ z - ψ (z + h)) :=
    hψsm.sub (hψsm.comp (continuous_id.add continuous_const))
  have hdcs : HasCompactSupport (fun z : Space d => ψ z - ψ (z + h)) :=
    hψcs.sub (hψcs.comp_homeomorph (Homeomorph.addRight h))
  have hdint : Integrable (fun z : Space d => ψ z - ψ (z + h)) :=
    hdsm.integrable_of_hasCompactSupport hdcs
  have hdsq : Continuous (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) := hdsm.pow 2
  have hdksq : HasCompactSupport (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) :=
    hdcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hdint2 : Integrable (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) :=
    hdsq.integrable_of_hasCompactSupport hdksq
  have hnh1 : ‖h‖ ≤ 1 := by rw [hnh]; exact inv_le_one_of_one_le₀ hR
  have hdsuppA : ∀ z : Space d, ψ z - ψ (z + h) ≠ 0 → z ∈ A := by
    intro z hz
    rw [hA, mem_closedBall_zero_iff]
    by_cases h1 : ψ z = 0
    · have h2 : ψ (z + h) ≠ 0 := by intro hc; exact hz (by rw [h1, hc]; ring)
      have h3 : ‖z + h‖ ≤ Lw := hψsupp _ h2
      have h4 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by
        have := norm_sub_le (z + h) h
        simpa using this
      linarith [hnh1]
    · linarith [hψsupp z h1]
  have hL1 := integral_abs_le_sqrt_measure_mul A (fun z : Space d => ψ z - ψ (z + h))
    hdint hdint2 hAvol hdsuppA
  have hL2 : ∫ z : Space d, (ψ z - ψ (z + h)) ^ 2 ≤ Cw * ‖h‖ ^ 2 := hCw h
  have hsqrtle : Real.sqrt (∫ z : Space d, (ψ z - ψ (z + h)) ^ 2) ≤ Real.sqrt Cw * R⁻¹ := by
    refine le_trans (Real.sqrt_le_sqrt hL2) (le_of_eq ?_)
    rw [Real.sqrt_mul hCw0, hnh, Real.sqrt_sq (by positivity)]
  rw [hrep, hpairsum, hparity, hfilter, abs_mul]
  have hb : |∫ z : Space d, ψ z * parityChar R z| ≤
      (1/2) * (Real.sqrt ((volume A).toReal) * (Real.sqrt Cw * R⁻¹)) := by
    refine le_trans himb ?_
    have hstep : ∫ z : Space d, |ψ z - ψ (z + h)| ≤
        Real.sqrt ((volume A).toReal) * (Real.sqrt Cw * R⁻¹) :=
      le_trans hL1 (mul_le_mul_of_nonneg_left hsqrtle (Real.sqrt_nonneg _))
    linarith
  calc |c₀ - c₁| * |∫ z : Space d, ψ z * parityChar R z|
      ≤ |c₀ - c₁| * ((1/2) * (Real.sqrt ((volume A).toReal) * (Real.sqrt Cw * R⁻¹))) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = (1/2) * Real.sqrt ((volume A).toReal) * Real.sqrt Cw * |c₀ - c₁| * R⁻¹ := by ring

end Sandpile.Support
