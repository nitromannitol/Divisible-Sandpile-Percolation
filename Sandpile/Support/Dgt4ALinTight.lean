/-
Tightness of the time-weighted membrane field for a fully general deterministic
array `q : ℝ → ℕ → ℝ`, transposed from `Sandpile.Support.weighted_membrane_tight`
(`Sandpile/Support/TightWeightedMembrane.lean`), which only allows a weight of
the special form `q(j/R²)`.  `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5615-5660`) needs the general array `q_{R,j} ∈ [0,1]`, so this
repeats that proof with the weight sequence `fun j => q R j` in place of
`fun j => q (j/R²)`; every step of the covariance bound only uses a uniform
bound on the weights on the summed range, which `q_{R,j} ∈ [0,1]` supplies
directly.
-/
import Sandpile.Support.TightWeightedMembrane

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

variable {d : ℕ}

/-- **Tightness of the time-weighted membrane field for a general array.**  For
`q : ℝ → ℕ → ℝ` bounded by `Q` on the summed range `j < ⌊R²T⌋`, the field
`R ↦ R^{(d-4)/2} · (Σ_{j<⌊R²T⌋} q(R,j) P^jζ)^{(R)}` is tight in `H^{-s}_loc(ℝ^d)`
for every `s > (d-4)/2`. -/
theorem weighted_membrane_tight_general (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0) (T : ℝ) (_hT : 0 < T) (q : ℝ → ℕ → ℝ) (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ → |q R j| ≤ Q) (s : ℝ)
    (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd4 : (0 : ℝ) < (d : ℝ) - 4 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hdecay⟩ := exists_weighted_membrane_covariance_decay hGH hd ν hsq Q hQ0
  refine Sandpile.Frozen.sobolev_tightness d ((d : ℝ) - 4) K hd4 (by linarith) hBesov
    (Sandpile.centeredMassLaw d ν)
    (fun R σ x => weightedField (fun j => q R j) ⌊R ^ 2 * T⌋₊ (Sandpile.scenery d σ) x) ?_ ?_ ?_
    s (by linarith)
  · intro R hR x
    exact memLp_two_weightedField_mass ν hsq hd1 _ _ x
  · intro R hR x
    exact integral_weightedField_mass ν hsq hmean hd1 _ _ x
  · intro R hR x y
    have hqb : ∀ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, |q R j| ≤ Q := by
      intro j hj
      exact hQ R j (Finset.mem_range.mp hj)
    rw [covariance_weightedField_mass ν hd1 _ _ x y]
    exact hdecay _ _ hqb x y

end Sandpile.Support
