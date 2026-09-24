/-
The final assembly of `prop:fixed-scale-crossings` (`sandpile.tex:2121-2128`)
out of the two estimates its proof produces:

  `sandpile.tex:2235-2240`, the crossing at level zero,
    `P(H_{[-θR,θR]×[0,2R]}(0)) ≥ c₀`  uniformly in `R ≥ 1`,

  `sandpile.tex:2302-2309`, the level loss,
    `0 ≤ P(H(0)) - P(H(L/R)) ≤ C L R^{-α₁/2}`  for every `R ≥ 1`.

  "Together with [the zero-level crossing], this gives the proposition."

The `liminf` is taken in `ℝ≥0∞`, so the loss term is compared there; the point
of the argument is that the loss vanishes as `R → ∞` for each fixed `L`, which
is why one `p` serves every `L`.
-/
import Sandpile.Support.CrossBasic

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Frozen.FixedScaleCrossings

/-- A negative power of `R` beats any positive constant for large `R`. -/
theorem eventually_mul_rpow_neg_le {C a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∀ᶠ R : ℝ in atTop, C * R ^ (-a) ≤ e := by
  have h0 : Filter.Tendsto (fun R : ℝ => C * R ^ (-a)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop ha).const_mul C
  exact h0.eventually_le_const he

/-- The proposition of `sandpile.tex:2121-2128` from its two estimates: a
uniform positive lower bound at level zero and a level loss that vanishes as
`R → ∞`.  The constant `c / 2` is a lower bound for the `liminf` at every level
`L / R`, uniformly in `L ≥ 0`. -/
theorem liminf_crossing_of_level_and_loss
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (θ : ℝ)
    (lev : ℝ) (c C a R₀ : ℝ) (hc : 0 < c) (ha : 0 < a)
    (h0 : ∀ R : ℝ, R₀ ≤ R →
      ENNReal.ofReal c ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | lev ≤ X u ω}})
    (L : ℝ)
    (hloss : ∀ R : ℝ, R₀ ≤ R →
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | lev ≤ X u ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}} +
          ENNReal.ofReal (C * L * R ^ (-a))) :
    ENNReal.ofReal (c / 2) ≤ Filter.liminf (fun R : ℝ =>
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ X u ω}}) atTop := by
  refine le_liminf_ennreal ?_
  have hev : ∀ᶠ R : ℝ in atTop, C * L * R ^ (-a) ≤ c / 2 :=
    eventually_mul_rpow_neg_le ha (by linarith)
  filter_upwards [hev, eventually_ge_atTop R₀] with R hRe hR1
  refine ofReal_half_le_of_add hc.le (le_trans (le_trans (h0 R hR1) (hloss R hR1)) ?_)
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal hRe)

end Sandpile.Support
