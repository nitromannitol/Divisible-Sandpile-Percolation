import Sandpile.Support.ContCell

/-!
# The `L²` side of the cell-pairing bound

Steps 2 and 3 of `prop:d4-superdiffusive-limit` (`sandpile.tex:3368-3404`). Over the cells of the
mesh the pairing of a lattice field with a test function is the finite sum `∑_x f(x)m_R(x)` of
`Sandpile.Support.latticePairing_eq_sum`. Cauchy-Schwarz against the constant one on a set of
finite measure (`sq_setIntegral_le`) separates the random field from the test function in this
pairing (`abs_latticePairing_le`): the field contributes `∑_x f(x)²`, and the test function
contributes `∑_x m_R(x)² ≤ R^{-d}∫φ²` (`sum_sq_cellMass_le`), since each cell has volume `R^{-d}`
and the cells are disjoint. The same Cauchy-Schwarz estimate also bounds the `L¹` norm of a
function supported on a finite-measure set by its `L²` norm (`integral_abs_le_sqrt_measure_mul`),
which is how the modulus of continuity of Step 2's second display becomes a bound on the parity
imbalance (`sandpile.tex:3374-3382`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support
open Sandpile.Continuum

variable {d : ℕ}

/-- **Cauchy-Schwarz against the constant one** on a set of finite measure:
`(∫_A φ)² ≤ |A|∫_Aφ²`, by the discriminant of `λ ↦ ∫_A(φ-λ)²`. -/
theorem sq_setIntegral_le (A : Set (Space d)) (φ : Space d → ℝ)
    (h1 : IntegrableOn φ A) (h2 : IntegrableOn (fun z => φ z ^ 2) A)
    (hV : volume A ≠ ⊤) :
    (∫ z in A, φ z) ^ 2 ≤ (volume A).toReal * ∫ z in A, φ z ^ 2 := by
  set V : ℝ := (volume A).toReal with hVdef
  set I1 : ℝ := ∫ z in A, φ z with hI1
  set I2 : ℝ := ∫ z in A, φ z ^ 2 with hI2
  have hfin : IsFiniteMeasure (volume.restrict A) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hV
  have hVnn : (0:ℝ) ≤ V := by rw [hVdef]; exact ENNReal.toReal_nonneg
  have hkey : ∀ lam : ℝ, 0 ≤ I2 - 2 * lam * I1 + lam ^ 2 * V := by
    intro lam
    have hnn : (0:ℝ) ≤ ∫ z in A, (φ z - lam) ^ 2 :=
      integral_nonneg fun z => sq_nonneg _
    have e1 : ∫ z in A, ((φ z ^ 2 - 2 * lam * φ z) + lam ^ 2) =
        (∫ z in A, (φ z ^ 2 - 2 * lam * φ z)) + ∫ _z in A, lam ^ 2 :=
      integral_add (h2.sub (h1.const_mul _)) (integrable_const _)
    have e2 : ∫ z in A, (φ z ^ 2 - 2 * lam * φ z) =
        (∫ z in A, φ z ^ 2) - ∫ z in A, 2 * lam * φ z :=
      integral_sub h2 (h1.const_mul _)
    have e3 : ∫ z in A, 2 * lam * φ z = 2 * lam * ∫ z in A, φ z := integral_const_mul _ _
    have e4 : ∫ _z in A, lam ^ 2 = V * lam ^ 2 := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def, hVdef]
    have hpt : ∫ z in A, (φ z - lam) ^ 2 = ∫ z in A, ((φ z ^ 2 - 2 * lam * φ z) + lam ^ 2) :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [hpt, e1, e2, e3, e4] at hnn
    linarith
  rcases eq_or_lt_of_le hVnn with hV0 | hVpos
  · have hzero : volume A = 0 := by
      have h := (ENNReal.toReal_eq_zero_iff (volume A)).mp (by rw [← hVdef, ← hV0])
      tauto
    have hI10 : I1 = 0 := by
      rw [hI1, Measure.restrict_eq_zero.mpr hzero, integral_zero_measure]
    have hI2nn : 0 ≤ I2 := by rw [hI2]; exact integral_nonneg fun z => sq_nonneg _
    rw [hI10, ← hV0]
    simp
  · have h := hkey (I1 / V)
    have hexpand : I2 - 2 * (I1 / V) * I1 + (I1 / V) ^ 2 * V = I2 - I1 ^ 2 / V := by
      field_simp; ring
    rw [hexpand] at h
    have h2' := (div_le_iff₀ hVpos).mp (by linarith : I1 ^ 2 / V ≤ I2)
    linarith
/-- **The cell masses are square summable against the `L²` norm of the test
function**: `∑_x m_R(x)² ≤ R^{-d}∫φ²`, since each cell has volume `R^{-d}` and
the cells are disjoint. -/
theorem sum_sq_cellMass_le {R : ℝ} (hR : 0 < R) (φ : Space d → ℝ)
    (h1 : Integrable φ) (h2 : Integrable (fun z => φ z ^ 2)) (s : Finset (Sandpile.Site d)) :
    ∑ x ∈ s, cellMass R φ x ^ 2 ≤ R⁻¹ ^ d * ∫ z, φ z ^ 2 := by
  classical
  have hvol : ∀ x : Sandpile.Site d, (volume (cell d R x)).toReal = R⁻¹ ^ d := by
    intro x
    rw [volume_cell d hR x, ENNReal.toReal_pow, ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hR))]
  have hne : ∀ x : Sandpile.Site d, volume (cell d R x) ≠ ⊤ := by
    intro x
    rw [volume_cell d hR x]
    exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  have hterm : ∀ x ∈ s, cellMass R φ x ^ 2 ≤ R⁻¹ ^ d * ∫ z in cell d R x, φ z ^ 2 := by
    intro x _
    have h := sq_setIntegral_le (cell d R x) φ h1.integrableOn h2.integrableOn (hne x)
    rwa [hvol x] at h
  calc ∑ x ∈ s, cellMass R φ x ^ 2
      ≤ ∑ x ∈ s, R⁻¹ ^ d * ∫ z in cell d R x, φ z ^ 2 := Finset.sum_le_sum hterm
    _ = R⁻¹ ^ d * ∑ x ∈ s, ∫ z in cell d R x, φ z ^ 2 := by rw [Finset.mul_sum]
    _ = R⁻¹ ^ d * ∫ z in ⋃ x ∈ s, cell d R x, φ z ^ 2 := by
        rw [integral_biUnion_finset s (fun x _ => measurableSet_cell d R x)
          (fun x _ y _ hxy => cell_disjoint hxy) (fun x _ => h2.integrableOn)]
    _ ≤ R⁻¹ ^ d * ∫ z, φ z ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_integral h2 (Filter.Eventually.of_forall fun z => sq_nonneg _)

/-- **The pairing bound.**  Cauchy-Schwarz in the cell index separates the
lattice field from the test function:
`|f^{(R)}(φ)| ≤ (∑_{x∈s}f(x)²)^{1/2}(R^{-d}∫φ²)^{1/2}`, where `s` is any finite
set of cells covering the support of `φ`. -/
theorem abs_latticePairing_le {R : ℝ} (hR : 0 < R) (g : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (h1 : Integrable φ) (h2 : Integrable (fun z => φ z ^ 2)) (s : Finset (Sandpile.Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    |Sandpile.Continuum.latticePairing R g φ| ≤
      Real.sqrt (∑ x ∈ s, g x ^ 2) * Real.sqrt (R⁻¹ ^ d * ∫ z, φ z ^ 2) := by
  classical
  rw [latticePairing_eq_sum R g φ h1 s hs]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s g (cellMass R φ)
  have hmass := sum_sq_cellMass_le hR φ h1 h2 s
  have hg0 : (0:ℝ) ≤ ∑ x ∈ s, g x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hstep : (∑ x ∈ s, g x * cellMass R φ x) ^ 2 ≤
      (∑ x ∈ s, g x ^ 2) * (R⁻¹ ^ d * ∫ z, φ z ^ 2) :=
    le_trans hcs (mul_le_mul_of_nonneg_left hmass hg0)
  have habs : |∑ x ∈ s, g x * cellMass R φ x| =
      Real.sqrt ((∑ x ∈ s, g x * cellMass R φ x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
  rw [habs, ← Real.sqrt_mul hg0]
  exact Real.sqrt_le_sqrt hstep

/-- **The `L¹` norm against the `L²` norm on a set of finite measure.**  A
function supported in `A` has `∫|ψ| ≤ |A|^{1/2}(∫ψ²)^{1/2}`.  This is how the
modulus of continuity of Step 2's second display becomes a bound on the parity
imbalance (`sandpile.tex:3374-3382`). -/
theorem integral_abs_le_sqrt_measure_mul (A : Set (Space d)) (ψ : Space d → ℝ)
    (h1 : Integrable ψ) (h2 : Integrable (fun z => ψ z ^ 2))
    (hV : volume A ≠ ⊤) (hsupp : ∀ z : Space d, ψ z ≠ 0 → z ∈ A) :
    ∫ z : Space d, |ψ z| ≤
      Real.sqrt ((volume A).toReal) * Real.sqrt (∫ z : Space d, ψ z ^ 2) := by
  classical
  have hoff : ∀ z : Space d, z ∉ A → |ψ z| = 0 := by
    intro z hz
    by_cases hψ : ψ z = 0
    · rw [hψ, abs_zero]
    · exact absurd (hsupp z hψ) hz
  have hrestrict : ∫ z in A, |ψ z| = ∫ z : Space d, |ψ z| :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hoff
  have habs2 : ∀ z : Space d, |ψ z| ^ 2 = ψ z ^ 2 := fun z => sq_abs _
  have hcs := sq_setIntegral_le A (fun z => |ψ z|) h1.abs.integrableOn
    (by simpa only [habs2] using h2.integrableOn) hV
  have hsq : ∫ z in A, |ψ z| ^ 2 = ∫ z in A, ψ z ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => habs2 z)
  have hle : ∫ z in A, ψ z ^ 2 ≤ ∫ z : Space d, ψ z ^ 2 :=
    setIntegral_le_integral h2 (Filter.Eventually.of_forall fun z => sq_nonneg _)
  have hVnn : (0:ℝ) ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have hstep : (∫ z : Space d, |ψ z|) ^ 2 ≤ (volume A).toReal * ∫ z : Space d, ψ z ^ 2 := by
    rw [← hrestrict]
    refine le_trans hcs ?_
    rw [hsq]
    exact mul_le_mul_of_nonneg_left hle hVnn
  have hnn : (0:ℝ) ≤ ∫ z : Space d, |ψ z| := integral_nonneg fun z => abs_nonneg _
  calc ∫ z : Space d, |ψ z| = Real.sqrt ((∫ z : Space d, |ψ z|) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((volume A).toReal * ∫ z : Space d, ψ z ^ 2) := Real.sqrt_le_sqrt hstep
    _ = Real.sqrt ((volume A).toReal) * Real.sqrt (∫ z : Space d, ψ z ^ 2) :=
        Real.sqrt_mul hVnn _

end Sandpile.Support
