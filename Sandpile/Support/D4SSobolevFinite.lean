import Sandpile.Support.D4SPlancherel
import LatticeProb.Analysis.Sobolev.Scaling

/-!
# The `H^s` norm of a test function is finite

This file proves that the `H^s` norm of a test function is finite (`sandpile.tex:3324-3327`).
`sobolevNormSq d s φ` is a lower integral in `ℝ≥0∞`, so it is defined for every `φ` and is `⊤`
exactly when the weighted Fourier integral diverges. The tightness clause of
`prop:d4-superdiffusive-limit` is a supremum over the functions with `sobolevNormSq d s φ ≤ 1`,
so that clause says nothing unless that set is nonempty. It is nonempty: a test function is
smooth with compact support, hence a Schwartz function; its Fourier transform is Schwartz, and
a Schwartz function is dominated by any inverse power of `‖ξ‖`, so the weight
`(1+(2π‖ξ‖)^2)^s` is integrated against a rapidly decaying square. Scaling such a `φ` down
then puts it on the unit ball.
-/

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace Sandpile.Support

open Sandpile.Continuum

/-- **The Sobolev weight is dominated by a polynomial.**  The weight
`(1+(2\pi a)^2)^s` is at most a constant times `1+a^{2\lceil s\rceil}`. -/
theorem exists_rpow_weight_le (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      (1 + (2 * Real.pi * a) ^ 2) ^ s ≤ C * (1 + a ^ (2 * ⌈s⌉₊)) := by
  refine ⟨(2 * (1 + 4 * Real.pi ^ 2)) ^ (⌈s⌉₊ : ℕ), by positivity, ?_⟩
  intro a ha
  have hbase : (1:ℝ) ≤ 1 + (2 * Real.pi * a) ^ 2 := by nlinarith [sq_nonneg (2 * Real.pi * a)]
  have hsm : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have h1 : (1 + (2 * Real.pi * a) ^ 2) ^ s ≤ (1 + (2 * Real.pi * a) ^ 2) ^ ((⌈s⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hsm
  have h2 : (1 + (2 * Real.pi * a) ^ 2) ^ (((⌈s⌉₊ : ℕ)) : ℝ)
      = (1 + (2 * Real.pi * a) ^ 2) ^ (⌈s⌉₊ : ℕ) := Real.rpow_natCast _ _
  have hstep : 1 + (2 * Real.pi * a) ^ 2 ≤ (1 + 4 * Real.pi ^ 2) * (1 + a ^ 2) := by
    nlinarith [sq_nonneg a, sq_nonneg Real.pi, sq_nonneg (Real.pi * a)]
  have h3 : (1 + (2 * Real.pi * a) ^ 2) ^ (⌈s⌉₊ : ℕ)
      ≤ ((1 + 4 * Real.pi ^ 2) * (1 + a ^ 2)) ^ (⌈s⌉₊ : ℕ) :=
    pow_le_pow_left₀ (by positivity) hstep _
  have h4 : (1 + a ^ 2) ^ (⌈s⌉₊ : ℕ) ≤ 2 ^ (⌈s⌉₊ : ℕ) * (1 + a ^ (2 * ⌈s⌉₊)) := by
    have hpow : a ^ (2 * ⌈s⌉₊) = (a ^ 2) ^ (⌈s⌉₊ : ℕ) := by rw [pow_mul]
    have hA : (0:ℝ) ≤ (a ^ 2) ^ (⌈s⌉₊ : ℕ) := by positivity
    have h2p : (0:ℝ) < 2 ^ (⌈s⌉₊ : ℕ) := by positivity
    rcases le_total a 1 with hle | hge
    · have hb : (1 + a ^ 2) ≤ 2 := by nlinarith
      have hc : (1 + a ^ 2) ^ (⌈s⌉₊ : ℕ) ≤ 2 ^ (⌈s⌉₊ : ℕ) :=
        pow_le_pow_left₀ (by positivity) hb _
      rw [hpow]
      nlinarith
    · have hb : (1 + a ^ 2) ≤ 2 * a ^ 2 := by nlinarith
      have h5 : (1 + a ^ 2) ^ (⌈s⌉₊ : ℕ) ≤ (2 * a ^ 2) ^ (⌈s⌉₊ : ℕ) :=
        pow_le_pow_left₀ (by positivity) hb _
      rw [mul_pow] at h5
      rw [hpow]
      nlinarith
  have h6 : ((1 + 4 * Real.pi ^ 2) * (1 + a ^ 2)) ^ (⌈s⌉₊ : ℕ)
      ≤ (2 * (1 + 4 * Real.pi ^ 2)) ^ (⌈s⌉₊ : ℕ) * (1 + a ^ (2 * ⌈s⌉₊)) := by
    rw [mul_pow, mul_pow]
    have hc : (0:ℝ) ≤ (1 + 4 * Real.pi ^ 2) ^ (⌈s⌉₊ : ℕ) := by positivity
    nlinarith [h4]
  rw [h2] at h1
  linarith [h1, h3, h6]

/-- **The `H^s` norm of a test function is finite.** -/
theorem sobolevNormSq_lt_top (d : ℕ) (s : ℝ) (φ : Space d → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    sobolevNormSq d s φ < ⊤ := by
  classical
  have hcs2 : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  have hcoe : ⇑(hcs2.toSchwartzMap hsm2) = fun x : Space d => (φ x : ℂ) := rfl
  set g : SchwartzMap (Space d) ℂ := 𝓕 (hcs2.toSchwartzMap hsm2) with hgdef
  have hgc : ∀ ξ : Space d, g ξ = 𝓕 (fun x : Space d => (φ x : ℂ)) ξ := by
    intro ξ
    rw [hgdef]
    rw [SchwartzMap.fourier_coe, hcoe]
  obtain ⟨C, hC0, hCb⟩ := exists_rpow_weight_le s
  obtain ⟨C0, hC0pos, hC0b⟩ := g.decay 0 0
  have hgb : ∀ ξ : Space d, ‖g ξ‖ ≤ C0 := by
    intro ξ
    have h := hC0b ξ
    simpa using h
  have hI0 : Integrable (fun ξ : Space d => ‖g ξ‖) := by
    have h := g.integrable_pow_mul (volume : Measure (Space d)) 0
    simpa using h
  have hIk : Integrable (fun ξ : Space d => ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖) :=
    g.integrable_pow_mul (volume : Measure (Space d)) (2 * ⌈s⌉₊)
  set h : Space d → ℝ := fun ξ => C * C0 * (‖g ξ‖ + ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖) with hhdef
  have hIh : Integrable h (volume : Measure (Space d)) := (hI0.add hIk).const_mul _
  have hhnn : 0 ≤ᵐ[(volume : Measure (Space d))] h := by
    refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : (0:ℝ) ≤ ‖g ξ‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖ := by positivity
    have : (0:ℝ) ≤ C * C0 := mul_nonneg hC0 hC0pos.le
    show (0:ℝ) ≤ C * C0 * (‖g ξ‖ + ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖)
    positivity
  have hdom : ∀ ξ : Space d,
      ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        ‖𝓕 (fun x : Space d => (φ x : ℂ)) ξ‖ ^ 2)
        ≤ ENNReal.ofReal (h ξ) := by
    intro ξ
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hgc ξ]
    have hw := hCb ‖ξ‖ (norm_nonneg ξ)
    have hwnn : (0:ℝ) ≤ (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s :=
      Real.rpow_nonneg (by positivity) s
    have hq : ‖g ξ‖ ^ 2 ≤ C0 * ‖g ξ‖ := by
      have := hgb ξ
      nlinarith [norm_nonneg (g ξ)]
    have hrhs : (0:ℝ) ≤ C * (1 + ‖ξ‖ ^ (2 * ⌈s⌉₊)) := by positivity
    have hmul : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖g ξ‖ ^ 2
        ≤ (C * (1 + ‖ξ‖ ^ (2 * ⌈s⌉₊))) * (C0 * ‖g ξ‖) :=
      mul_le_mul hw hq (sq_nonneg _) hrhs
    show (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖g ξ‖ ^ 2
      ≤ C * C0 * (‖g ξ‖ + ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖)
    have hring : (C * (1 + ‖ξ‖ ^ (2 * ⌈s⌉₊))) * (C0 * ‖g ξ‖)
        = C * C0 * (‖g ξ‖ + ‖ξ‖ ^ (2 * ⌈s⌉₊) * ‖g ξ‖) := by ring
    linarith [hmul, hring.le, hring.ge]
  rw [sobolevNormSq]
  calc ∫⁻ ξ : Space d, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s *
        ‖𝓕 (fun x : Space d => (φ x : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ : Space d, ENNReal.ofReal (h ξ) := lintegral_mono hdom
    _ = ENNReal.ofReal (∫ ξ : Space d, h ξ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIh hhnn).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The Fourier transform of a real multiple. -/
theorem fourier_const_mul (d : ℕ) (c : ℝ) (φ : Space d → ℝ) (ξ : Space d) :
    𝓕 (fun x : Space d => ((c * φ x : ℝ) : ℂ)) ξ
      = (c : ℂ) * 𝓕 (fun x : Space d => (φ x : ℂ)) ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Complex.ofReal_mul]
  ring

/-- A real multiple of a test function is a test function. -/
theorem isTestFn_const_mul {d : ℕ} {D : Set (Space d)} (c : ℝ) {φ : Space d → ℝ}
    (hφ : IsTestFn D φ) : IsTestFn D (fun x => c * φ x) := by
  have hg : (fun y : ℝ => c * y) 0 = 0 := by simp
  refine ⟨contDiff_const.mul hφ.1, ?_, ?_⟩
  · exact hφ.2.1.comp_left (g := fun y : ℝ => c * y) hg
  · exact le_trans (tsupport_comp_subset (g := fun y : ℝ => c * y) hg φ) hφ.2.2

/-- **Every test function can be scaled into the `H^s` unit ball.**  So the
supremum defining `negSobolevNorm` runs over a set that contains a positive
multiple of every test function, and the tightness clause of
`prop:d4-superdiffusive-limit` is not a statement about an empty index set. -/
theorem exists_const_mul_sobolevNormSq_le_one (d : ℕ) (s : ℝ) {D : Set (Space d)}
    (φ : Space d → ℝ) (hφ : IsTestFn D φ) :
    ∃ c : ℝ, 0 < c ∧ IsTestFn D (fun x => c * φ x)
      ∧ sobolevNormSq d s (fun x => c * φ x) ≤ 1 := by
  have hfin : sobolevNormSq d s φ < ⊤ := sobolevNormSq_lt_top d s φ hφ.1 hφ.2.1
  set r : ℝ := (sobolevNormSq d s φ).toReal with hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hNr : sobolevNormSq d s φ = ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_toReal hfin.ne]
  set c : ℝ := 1 / Real.sqrt (r + 1) with hc
  have hpos : 0 < Real.sqrt (r + 1) := Real.sqrt_pos.mpr (by linarith)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcsq : c ^ 2 = 1 / (r + 1) := by
    rw [hc, div_pow, one_pow, Real.sq_sqrt (by linarith)]
  refine ⟨c, hc0, isTestFn_const_mul c hφ, ?_⟩
  rw [LatticeProb.Sobolev.sobolevNormSq_const_mul, hNr, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_one.mpr ?_
  rw [hcsq, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
  linarith

end Sandpile.Support
