import Sandpile.Support.CrossBallMemLp

/-!
# Finite-scale maximum field

The finite-scale maximum field of `lem:finite-scale-extraction`
(`sandpile.tex:2415-2425`):

  "For every `ε>0`, there are `c>0` and rational scales `s_1,…,s_k∈(0,1)` such
   that `P(⋂_{j=1}^N H_{𝓡_j}(4c; max_{1≤i≤k} 𝒳_{s_i}))≥1-ε`."

The maximum is over a finite nonempty family, so it is a genuine maximum and
inherits the measurability and the continuity of the `𝒳_{s_i}` it is taken over.
Both are needed by the chain bracket of `Sandpile/Support/CrossUnion.lean`, which
is what carries a crossing statement from one space carrying white noise to
another.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A finite nonempty supremum of continuous real functions is continuous. -/
theorem continuous_ciSup_fin {X : Type*} [TopologicalSpace X] {k : ℕ} (hk : 0 < k)
    (F : Fin k → X → ℝ) (hF : ∀ i, Continuous (F i)) :
    Continuous fun u => ⨆ i : Fin k, F i u := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := Continuous.finset_sup'_apply (s := (Finset.univ : Finset (Fin k)))
    (f := F) Finset.univ_nonempty (fun i _ => hF i)
  simpa only [Finset.sup'_univ_eq_ciSup] using h

/-- `max_{1≤i≤k} 𝒳_{s_i}`, the field the finite-scale extraction crosses. -/
noncomputable def maxBallField {Ω : Type*} (d k : ℕ)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) (s : Fin k → ℚ)
    (u : Sandpile.Continuum.Space 2) (ω : Ω) : ℝ :=
  ⨆ i : Fin k, ballField d W (s i : ℝ) u ω

/-- Each ball field at a positive scale is measurable. -/
theorem measurable_ballField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {t : ℝ} (ht : 0 < t)
    (u : Sandpile.Continuum.Space 2) :
    Measurable (ballField d W t u) :=
  hW.meas _ (memLp_ballKernel hd ht u)

/-- So is their maximum. -/
theorem measurable_maxBallField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d k : ℕ}
    (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : Fin k → ℚ}
    (hs : ∀ i, 0 < (s i : ℝ)) (u : Sandpile.Continuum.Space 2) :
    Measurable (maxBallField d k W s u) :=
  Measurable.iSup fun i => measurable_ballField hd hW (hs i) u

/-- And the maximum is almost surely continuous once each field is. -/
theorem ae_continuous_maxBallField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d k : ℕ}
    (hk : 0 < k) (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) {s : Fin k → ℚ}
    (hs : ∀ i, 0 < (s i : ℝ) ∧ (s i : ℝ) ≤ 1)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω) :
    ∀ᵐ ω ∂P, Continuous fun u => maxBallField d k W s u ω := by
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin k, Continuous fun u => ballField d W (s i : ℝ) u ω :=
    (ae_all_iff.mpr fun i => hcont (s i : ℝ) (hs i).1 (hs i).2)
  filter_upwards [hall] with ω hω
  exact continuous_ciSup_fin hk (fun i u => ballField d W (s i : ℝ) u ω) hω

end Sandpile.Support
