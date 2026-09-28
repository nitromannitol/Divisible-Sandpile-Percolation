import Sandpile.Frozen.DGT4DiffusiveMembrane

/-!
# High-Sobolev Limit From the Diffusive Membrane Theorem

Theorem 1.3(iii)(c) of `sandpile.tex` (`sandpile.tex:275-289`) assembled from
`thm:dgt4-diffusive-membrane` (`sandpile.tex:4616-4639`), which the proof of
`thm:main-explosion` names at `sandpile.tex:307-308`: "part (iii)(c) is
Theorem~\ref{thm:dgt4-diffusive-membrane}".

Theorem 1.3(iii)(c) is the first conclusion of that theorem, read in its two
cases: the Gaussian scenery is the left branch of `hcase` at `κ = 1`, and the
atomless scenery bounded above with a regularly varying lower tail of index
`α > 2` is the right branch at `κ = 1 - 1/α`.  The second conclusion of the
theorem, the contact asymptotics, is not part of Theorem 1.3.

Two points of the transcription need work rather than a rewrite.

The Gaussian branch has to supply the hypothesis that `ν` is atomless, which
`thm:dgt4-diffusive-membrane` asks for and Theorem 1.3(iii)(c) does not:
`ν = gaussianReal 0 v` with a positive variance forces `v ≠ 0`, since
`gaussianReal 0 0` is the Dirac mass at the origin, whose `evariance` is zero;
and a real Gaussian with nonzero variance has a density, hence no atoms.

The time index differs by the order of a product: Theorem 1.3(iii)(c) writes
`⌊T R²⌋` and `thm:dgt4-diffusive-membrane` writes `⌊R² T⌋`.  They are the same
natural number.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

variable {d : ℕ}

/-- A real Gaussian law with positive `evariance` has nonzero variance parameter:
`gaussianReal 0 0` is the Dirac mass at the origin. -/
theorem gaussian_var_ne_zero {v : ℝ≥0} (hvar : 0 < evariance (id : ℝ → ℝ) (gaussianReal 0 v)) :
    v ≠ 0 := by
  intro hv
  subst hv
  rw [gaussianReal_zero_var] at hvar
  simp [evariance] at hvar

/-- A real Gaussian law with positive `evariance` has no atoms. -/
theorem gaussian_measure_singleton {v : ℝ≥0}
    (hvar : 0 < evariance (id : ℝ → ℝ) (gaussianReal 0 v)) (z : ℝ) :
    gaussianReal 0 v {z} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (gaussian_var_ne_zero hvar)
  exact measure_singleton z

/-- **Theorem 1.3(iii)(c) from `thm:dgt4-diffusive-membrane`.**  `hMembrane` is
the exact conclusion of that theorem, quantified over the scenery law, the
exponent `κ` and the case hypothesis; the two branches of Theorem 1.3(iii)(c)
are its two cases. -/
theorem high_sobolev_limit_of_membrane
    (_hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance (id : ℝ → ℝ) ν)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (hMembrane : ∀ κ : ℝ,
      (∀ z : ℝ, ν {z} = 0) →
      (((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
        (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
          (∀ lam : ℝ, 0 < lam →
            Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
              atTop (𝓝 (lam ^ (-α)))) ∧
          κ = 1 - 1 / α)) →
      ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
            R ^ (((d : ℝ) - 4) / 2) *
              Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
          (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) :
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Sandpile.Continuum.latticePairing R
                    (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν)
                (1 - 1 / α) T)) := by
  have hcomm : ∀ T R : ℝ, T * R ^ 2 = R ^ 2 * T := fun T R => mul_comm _ _
  constructor
  · intro v hv T hT s hs
    have hatom : ∀ z : ℝ, ν {z} = 0 := by
      subst hv
      exact gaussian_measure_singleton hvar
    have := hMembrane 1 hatom (Or.inl ⟨⟨v, hv⟩, rfl⟩) T hT s hs
    simpa only [hcomm] using this
  · intro hatom hbdd α hα hreg T hT s hs
    obtain ⟨b, hb⟩ := hbdd
    have := hMembrane (1 - 1 / α) hatom (Or.inr ⟨α, hα, ⟨b, hb⟩, hreg, rfl⟩) T hT s hs
    simpa only [hcomm] using this

end Sandpile.Support
