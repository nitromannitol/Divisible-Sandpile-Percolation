import Sandpile.Support.D4SobolevEmbed

/-!
# Plancherel and the Sobolev-to-`L²` Embedding

Plancherel's theorem for the test functions of `ssec:notation`, and the
embedding of the `H^s` unit ball in the `L²` unit ball that Steps 2 and 3 of
`prop:d4-superdiffusive-limit` use (`sandpile.tex:3368-3404`).

`sobolevNormSq d s φ` is written through the Fourier transform, so the passage
from a bound on `‖φ‖_{H^s}` to a bound on `‖φ‖_{L²}` is Plancherel's identity
`∫|φ̂|² = ∫|φ|²`. A test function is smooth with compact support, hence a
Schwartz function, and Plancherel for Schwartz functions is available.
-/

open MeasureTheory Filter Topology
open scoped ENNReal FourierTransform

namespace Sandpile.Support

open Sandpile.Continuum

/-- **Plancherel for a test function**: `∫|φ̂(ξ)|²dξ = ∫|φ(x)|²dx`. -/
theorem integral_fourier_sq_eq (d : ℕ) (φ : Space d → ℝ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    ∫ ξ : Space d, ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2 = ∫ x : Space d, φ x ^ 2 := by
  classical
  have hcs2 : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  have hplan := SchwartzMap.integral_norm_sq_fourier (hcs2.toSchwartzMap hsm2)
  have hcoe : ⇑(hcs2.toSchwartzMap hsm2) = fun x : Space d => (φ x : ℂ) := rfl
  rw [SchwartzMap.fourier_coe, hcoe] at hplan
  simpa using hplan

/-- **The `H^s` unit ball sits in the `L²` unit ball.**  For `s ≥ 0`, a test
function with `‖φ‖_{H^s} ≤ 1` has `∫φ² ≤ 1`.  This is the embedding
`L²(D) ↪ H^{-s}(D)` of Step 3 (`sandpile.tex:3403`) in the form the dual norm
uses. -/
theorem integral_sq_le_one_of_sobolevNormSq_le (d : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (φ : Space d → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (h : sobolevNormSq d s φ ≤ 1) :
    ∫ x : Space d, φ x ^ 2 ≤ 1 := by
  classical
  have hcs2 : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hcs.comp_left (g := Complex.ofRealCLM) rfl
  have hsm2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => (φ x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hsm
  have hcoe : ⇑(hcs2.toSchwartzMap hsm2) = fun x : Space d => (φ x : ℂ) := rfl
  have hcont : Continuous (fun ξ : Space d => 𝓕 (fun x : Space d => (φ x : ℂ)) ξ) := by
    have h := (𝓕 (hcs2.toSchwartzMap hsm2)).continuous
    rwa [SchwartzMap.fourier_coe, hcoe] at h
  have hmeas : AEStronglyMeasurable
      (fun ξ : Space d => ‖𝓕 (fun x : Space d => (φ x : ℂ)) ξ‖ ^ 2) volume :=
    (hcont.norm.pow 2).aestronglyMeasurable
  have heq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall
      (fun ξ : Space d => sq_nonneg ‖𝓕 (fun x : Space d => (φ x : ℂ)) ξ‖))
    hmeas
  have hle := lintegral_fourier_sq_le_of_sobolevNormSq_le d s hs φ h
  rw [← integral_fourier_sq_eq d φ hsm hcs, heq]
  have h2 := ENNReal.toReal_mono (by simp) hle
  simpa using h2

end Sandpile.Support
