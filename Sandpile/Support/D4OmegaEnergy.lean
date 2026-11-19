import Sandpile.Support.D4DefectOmega
import Sandpile.Support.ContDominated
import LatticeProb.Analysis.Sobolev.NegEnergy

/-!
# Fourier energy control of an `ω`-paired lattice field

The `ω`-representative of a lattice pairing is integration against the
piecewise-constant embedding with its `ω`-average subtracted. On a bounded
domain, a smooth cutoff equal to one on the domain bounds the negative Sobolev
dual norm by the square root of the cutoff field's Fourier energy.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The piecewise-constant lattice field with its `ω`-average subtracted. -/
noncomputable def omegaEmbed {d : ℕ} (R : ℝ) (w : Space d → ℝ)
    (f : Site d → ℝ) (z : Space d) : ℝ :=
  embed R f z - ∫ u : Space d, embed R f u * w u

/-- A lattice embedding paired with a compactly supported smooth function is
integrable. -/
theorem integrable_embed_mul_isTestFn {d : ℕ} (R : ℝ) (f : Site d → ℝ)
    (φ : Space d → ℝ) (hφ : IsTestFn Set.univ φ) :
    Integrable (fun z => embed R f z * φ z) := by
  obtain ⟨C, L, hC, hL, hCbound, hsupp, hint⟩ := exists_bound_of_isTestFn hφ
  exact integrable_embed_mul R f φ hint (supportBox d R L)
    (fun z hz => floor_mem_boxFinset R z (hsupp z hz))

/-- The `ω`-centered embedding is integrable against every compactly supported
smooth function. -/
theorem integrable_omegaEmbed_mul {d : ℕ} (R : ℝ) (w : Space d → ℝ)
    (f : Site d → ℝ) (φ : Space d → ℝ) (hφ : IsTestFn Set.univ φ) :
    Integrable (fun z => omegaEmbed R w f z * φ z) := by
  have hφint : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have h := (integrable_embed_mul_isTestFn R f φ hφ).sub
    (hφint.const_mul (∫ u : Space d, embed R f u * w u))
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  change embed R f z * φ z - (∫ u : Space d, embed R f u * w u) * φ z = _
  unfold omegaEmbed
  ring

/-- Pairing a lattice field in its `ω`-representative is integration against
its `ω`-centered embedding, for tests supported in the domain. -/
theorem omegaRep_latticePairing_eq_omegaEmbed {d : ℕ} {D : Set (Space d)}
    {w φ : Space d → ℝ} (hw : IsTestFn D w) (hφ : IsTestFn D φ)
    (R : ℝ) (f : Site d → ℝ) :
    omegaRep D w (latticePairing R f) φ = ∫ z, omegaEmbed R w f z * φ z := by
  have hw' : IsTestFn Set.univ w := ⟨hw.1, hw.2.1, Set.subset_univ _⟩
  have hφ' : IsTestFn Set.univ φ := ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  have hwint := integrable_embed_mul_isTestFn R f w hw'
  have hφint := integrable_embed_mul_isTestFn R f φ hφ'
  have hφint' : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have htotal := setIntegral_eq_integral_of_isTestFn hφ
  change (∫ z : Space d, embed R f z * (φ z - w z * ∫ y in D, φ y)) = _
  calc
    _ = ∫ z : Space d, (embed R f z * φ z -
        (embed R f z * w z) * (∫ y in D, φ y)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    _ = (∫ z : Space d, embed R f z * φ z) -
        (∫ z : Space d, (embed R f z * w z) * (∫ y in D, φ y)) :=
      integral_sub hφint (hwint.mul_const _)
    _ = (∫ z : Space d, embed R f z * φ z) -
        (∫ z : Space d, embed R f z * w z) * (∫ z : Space d, φ z) := by
      rw [integral_mul_const, htotal]
    _ = ∫ z : Space d, (embed R f z * φ z -
        (∫ u : Space d, embed R f u * w u) * φ z) := by
      have hc : Integrable (fun z : Space d =>
          (∫ u : Space d, embed R f u * w u) * φ z) := hφint'.const_mul _
      have hh := integral_sub hφint hc
      rw [integral_const_mul] at hh
      exact hh.symm
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      unfold omegaEmbed
      ring

/-- A cutoff Fourier energy controls the negative Sobolev norm of an
`ω`-paired lattice field. -/
theorem negSobolevNorm_omegaRep_le_fourierNegEnergy {d : ℕ}
    (s : ℝ) (D : Set (Space d)) (w χ : Space d → ℝ) (R : ℝ) (f : Site d → ℝ)
    (hw : IsTestFn D w) (hχ : IsTestFn Set.univ χ) (hχD : ∀ x ∈ D, χ x = 1) :
    negSobolevNorm d s D (omegaRep D w (latticePairing R f)) ≤
      LatticeProb.Sobolev.fourierNegEnergy d s (fun z => χ z * omegaEmbed R w f z) ^
        (1 / 2 : ℝ) := by
  have hnorm := LatticeProb.Sobolev.negSobolevNorm_le_fourierNegEnergy d s D χ
    (omegaEmbed R w f) hχ hχD (fun φ hφ => integrable_omegaEmbed_mul R w f φ hφ)
  refine le_trans ?_ hnorm
  unfold LatticeProb.Sobolev.negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hφn, rfl⟩
  rw [omegaRep_latticePairing_eq_omegaEmbed hw hφ]
  exact le_sSup ⟨φ, hφ, hφn, rfl⟩

end Sandpile.Support
