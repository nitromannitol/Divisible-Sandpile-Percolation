import Sandpile.Law
import Sandpile.Walk
import Sandpile.Frozen.DGT4PathSurvival

/-! # Uniform and Pointwise Contact Thresholds

The uniform contact-threshold estimate `eq:dgt4-uniform-contact-thresholds`
(`sandpile.tex:5473-5480`), which is the hypothesis of `lem:dgt4-path-survival`
and is what the two proofs of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:4969` and `sandpile.tex:5306`) establish:

  "for every $\varepsilon\in(0,1)$, as $R\to\infty$,
   $\max_{\lceil\varepsilon n_R\rceil\leq m\leq n_R}
    \{|m\P(J(0)>\E u_{m-1}(0))/(G(0,0)\kappa)-1|
     +m\P(\{u_m(0)=0\}\triangle\{J(0)>\E u_{m-1}(0)\})\}\to0$."

Naming it isolates the single analytic input that both `prop:dgt4-linearization`
and `prop:dgt4-contact-asymptotics` still need: the first is
`lem:dgt4-linearization-from-survival` applied to the time weights, whose two
hypotheses are supplied by `lem:dgt4-path-survival` from this estimate, and the
second is this estimate read at `m = n` together with the symmetric-difference
bound, which is `dgt4_contact_of_thresholds` below.

The transcription is character for character the `hthresholds` argument of
`Sandpile.Frozen.dgt4_path_survival`, so that the sealed lemma applies to it
directly.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `eq:dgt4-uniform-contact-thresholds` of `sandpile.tex:5468-5475`, the
hypothesis of `lem:dgt4-path-survival`: uniformly over
`⌈ε n_R⌉ ≤ m ≤ n_R`, the threshold probability `P(J(0) > E u_{m-1}(0))` is
`G(0,0)κ/m` to leading order and the contact event `{u_m(0)=0}` agrees with the
threshold event up to `o(1/m)`. -/
def UniformContactThresholds (d : ℕ) (ν : Measure ℝ)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ) (κ T : ℝ) : Prop :=
  ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
    ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
      |(m : ℝ) * ((Sandpile.centeredMassLaw d ν)
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
          (Sandpile.green d 0 0 * κ) - 1| +
        (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
          (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
            {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
              J σ 0})).toReal ≤ η

/-- The two limits that the two case-specific proofs of
`prop:dgt4-contact-asymptotics` establish (`sandpile.tex:4964` ff. and
`sandpile.tex:5301` ff.): the threshold probability at the level `E u_{m-1}(0)`
is `G(0,0)κ/m` to leading order, and the contact event agrees with the threshold
event up to `o(1/m)`.  These are limits in the single index `m`; they imply the
uniform form `UniformContactThresholds` because `⌈ε n_R⌉ → ∞`. -/
def PointwiseContactThresholds (d : ℕ) (ν : Measure ℝ)
    (J : (Sandpile.Site d → ℝ) → Sandpile.Site d → ℝ) (κ : ℝ) : Prop :=
  Tendsto (fun m : ℕ => (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
      (Sandpile.green d 0 0 * κ)) atTop (𝓝 1) ∧
  Tendsto (fun m : ℕ => (m : ℝ) * ((Sandpile.centeredMassLaw d ν)
      (symmDiff {σ | Sandpile.odometer σ m 0 = 0}
        {σ | Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (m - 1) <
          J σ 0})).toReal) atTop (𝓝 0)

end Sandpile
