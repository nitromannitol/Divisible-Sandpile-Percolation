import Sandpile.Support.Dgt4AStep2Output

/-!
# The Step-2 output of `thm:dgt4-many-limits`, named

Step 2 of the proof of `thm:dgt4-many-limits` (`sandpile.tex:6051-6275`), named. The paper's Step 2
proves the two band limits `eq:dgt4-band-contact-rate` and `eq:dgt4-band-contact-comparison`
uniformly over `δ R_k^2 ≤ n ≤ T R_k^2`, at the exponent `κ_k = 1 + 1/ϑ_k` of the constructed
scenery. Those exponents move with the scale, so Step 3 (`sandpile.tex:6275-6305`) fixes
`κ ∈ [3/2,2]`, extracts `k_ℓ ↑ ∞` with `κ_{k_ℓ} → κ`, and reads the two limits along `R_{k_ℓ}`; the
uniform contact-threshold estimate `eq:dgt4-uniform-contact-thresholds` is what
`lem:dgt4-path-survival` assumes.

`Dgt4AStep2Input d ν` is that output in the form the frozen Step-3 chain consumes: one sequence of
scales `R_k ↑ ∞` together with, for every `κ ∈ [3/2,2]` and every horizon `T > 0`, the uniform
contact-threshold estimate along those scales. The extraction of `k_ℓ` is what supplies, for each
`κ`, an exponent sequence converging to it.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile

/-- The Step-2 output of `thm:dgt4-many-limits` (`sandpile.tex:6046-6270`): one
sequence of scales `R_k ↑ ∞` such that, for every `κ ∈ [3/2,2]` and every
`T > 0`, the uniform contact-threshold estimate
`eq:dgt4-uniform-contact-thresholds` holds along those scales. -/
def Dgt4AStep2Input (d : ℕ) (ν : Measure ℝ) : Prop :=
  ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
    ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 → ∀ T : ℝ, 0 < T →
      UniformContactThresholdsAlong d ν κ T Rseq

/-- The two band limits of Step 2, at an exponent sequence converging to each
`κ ∈ [3/2,2]`, give the Step-2 output. -/
theorem dgt4AStep2Input_of_output (d : ℕ) (ν : Measure ℝ)
    (Rseq : ℕ → ℝ) (hmono : StrictMono Rseq) (htop : Tendsto Rseq atTop atTop)
    (h : ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
      ∃ kseq : ℕ → ℝ, Tendsto kseq atTop (𝓝 κ) ∧ Dgt4AStep2Output d ν kseq Rseq) :
    Dgt4AStep2Input d ν := by
  refine ⟨Rseq, hmono, htop, fun κ hκ T hT => ?_⟩
  obtain ⟨kseq, hkseq, hout⟩ := h κ hκ
  have hκ0 : 0 < κ := lt_of_lt_of_le (by norm_num) hκ.1
  exact uniformContactThresholdsAlong_of_step2 d ν kseq Rseq htop κ T hκ0 hT hkseq hout

/-- The uniform contact-threshold estimate at the exponent `κ` and horizon `T`,
from the Step-2 output. -/
theorem uniformContactThresholdsAlong_of_step2Input (d : ℕ) (ν : Measure ℝ)
    (h : Dgt4AStep2Input d ν) (κ : ℝ) (hκ : κ ∈ Set.Icc ((3 : ℝ) / 2) 2)
    (T : ℝ) (hT : 0 < T) :
    ∃ Rseq : ℕ → ℝ, StrictMono Rseq ∧ Tendsto Rseq atTop atTop ∧
      UniformContactThresholdsAlong d ν κ T Rseq := by
  obtain ⟨Rseq, hmono, htop, hmain⟩ := h
  exact ⟨Rseq, hmono, htop, hmain κ hκ T hT⟩

end Sandpile.Support
