import Mathlib

/-! # Derivative Variance Limit

The passage from the two displays of Step 1 of
`lem:dgt4-linearization-from-survival` to `eq:dgt4-derivative-variance-limit`
(`sandpile.tex:5769-5783`).

The paper combines the early display `eq:dgt4-early-derivative-variance` and the
late display `eq:dgt4-late-derivative-variance` by

  "`Var(D^{≤}_{R,z}+D^{>}_{R,z}) ≤ 2 Var(D^{≤}_{R,z}) + 2 E[(D^{>}_{R,z})²]`",

obtaining `limsup_R ∑_z Var(∂_{ζ(z)}F_R) ≤ C(φ)δ² + o(1)` for every `δ > 0`, and
lets `δ → 0`.  The two lemmas below are that passage: the limsup bound from the
two displays, and the elementary fact that a nonnegative quantity whose limsup is
at most `2Cδ²` for every `δ > 0` tends to zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- The limsup bound obtained by combining the early and late displays. -/
theorem limsup_le_of_early_late (V eps o : ℝ → ℝ) (C δ : ℝ) (hδ : 0 < δ)
    (heps : Tendsto eps atTop (𝓝 0)) (ho : Tendsto o atTop (𝓝 0))
    (hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ V R)
    (h : ∀ᶠ R : ℝ in atTop,
      V R ≤ 2 * (C * eps R + C / (δ * R ^ 2)) + 2 * (C * δ ^ 2 + o R)) :
    limsup V atTop ≤ 2 * C * δ ^ 2 := by
  have hb : Tendsto (fun R : ℝ => 2 * (C * eps R + C / (δ * R ^ 2)) + 2 * (C * δ ^ 2 + o R))
      atTop (𝓝 (2 * C * δ ^ 2)) := by
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hsq : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := by
      simpa only [Real.rpow_two] using tendsto_rpow_atTop h2pos
    have h1 : Tendsto (fun R : ℝ => C / (δ * R ^ 2)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := C)).div_atTop (Filter.Tendsto.const_mul_atTop hδ hsq)
    have h2 : Tendsto (fun R : ℝ => C * eps R + C / (δ * R ^ 2)) atTop (𝓝 0) := by
      simpa using (heps.const_mul C).add h1
    have h3 : Tendsto (fun R : ℝ => C * δ ^ 2 + o R) atTop (𝓝 (C * δ ^ 2)) := by
      simpa using ho.const_add (C * δ ^ 2)
    have h4 := (h2.const_mul 2).add (h3.const_mul 2)
    convert h4 using 2
    ring
  have hbdd : ∀ᶠ R : ℝ in atTop, V R ≤ 2 * C * δ ^ 2 + 1 := by
    filter_upwards [h, hb.eventually (eventually_lt_nhds (lt_add_one (2 * C * δ ^ 2)))]
      with R hR hR'
    linarith
  refine (Filter.limsup_le_iff (Filter.isCoboundedUnder_le_of_eventually_le atTop hnonneg)
    (Filter.isBoundedUnder_of_eventually_le hbdd)).mpr ?_
  intro y hy
  filter_upwards [h, hb.eventually (eventually_lt_nhds hy)] with R hR hR'
  exact lt_of_le_of_lt hR hR'

/-- A nonnegative quantity whose limsup is at most `2Cδ²` for every `δ > 0`, and
which is eventually bounded above, tends to zero. -/
theorem tendsto_zero_of_limsup_le (V : ℝ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ V R)
    (hbdd : ∀ᶠ R : ℝ in atTop, V R ≤ B)
    (h : ∀ δ : ℝ, 0 < δ → limsup V atTop ≤ 2 * C * δ ^ 2) :
    Tendsto V atTop (𝓝 0) := by
  have h0 : limsup V atTop ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hpos : 0 < ε / (2 * C + 2) := div_pos hε (by linarith)
    have hδ : 0 < Real.sqrt (ε / (2 * C + 2)) := Real.sqrt_pos.mpr hpos
    have h1 := h _ hδ
    have h2 : 2 * C * (Real.sqrt (ε / (2 * C + 2))) ^ 2 ≤ ε := by
      rw [Real.sq_sqrt hpos.le, mul_div_assoc']
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * C + 2)]
      nlinarith
    linarith
  have hliminf : 0 ≤ liminf V atTop :=
    Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_eventually_le atTop hbdd) hnonneg
  have hls : liminf V atTop ≤ limsup V atTop :=
    Filter.liminf_le_limsup (Filter.isBoundedUnder_of_eventually_le hbdd)
      (Filter.isBoundedUnder_of_eventually_ge hnonneg)
  have hlimsup0 : limsup V atTop = 0 := le_antisymm h0 (le_trans hliminf hls)
  have hliminf0 : liminf V atTop = 0 := le_antisymm (le_trans hls h0) hliminf
  exact tendsto_of_liminf_eq_limsup (u := V) (f := atTop) (a := 0) hliminf0 hlimsup0
    (Filter.isBoundedUnder_of_eventually_le hbdd) (Filter.isBoundedUnder_of_eventually_ge hnonneg)

/-- The combination of the early and late displays: from `V ≤ 2 early + 2 late`,
`early ≤ C ε + C/(δR²)` and `late ≤ C δ² + o`, the hypothesis of
`limsup_le_of_early_late`. -/
theorem eventually_le_of_early_late (V early late eps o : ℝ → ℝ) (C δ : ℝ)
    (hsplit : ∀ᶠ R : ℝ in atTop, V R ≤ 2 * early R + 2 * late R)
    (hearly : ∀ᶠ R : ℝ in atTop, early R ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ᶠ R : ℝ in atTop, late R ≤ C * δ ^ 2 + o R) :
    ∀ᶠ R : ℝ in atTop,
      V R ≤ 2 * (C * eps R + C / (δ * R ^ 2)) + 2 * (C * δ ^ 2 + o R) := by
  filter_upwards [hsplit, hearly, hlate] with R h1 h2 h3
  linarith

/-- The limsup bound of `eq:dgt4-derivative-variance-limit` from the two
displays: `V ≤ 2 early + 2 late`, `early ≤ C ε_R(δ) + C/(δR²)` and
`late ≤ C δ² + o(1)` give `limsup V ≤ 2Cδ²`. -/
theorem limsup_derivVar_le (V early late eps o : ℝ → ℝ) (C δ : ℝ) (hδ : 0 < δ)
    (heps : Tendsto eps atTop (𝓝 0)) (ho : Tendsto o atTop (𝓝 0))
    (hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ V R)
    (hsplit : ∀ᶠ R : ℝ in atTop, V R ≤ 2 * early R + 2 * late R)
    (hearly : ∀ᶠ R : ℝ in atTop, early R ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ᶠ R : ℝ in atTop, late R ≤ C * δ ^ 2 + o R) :
    limsup V atTop ≤ 2 * C * δ ^ 2 :=
  limsup_le_of_early_late V eps o C δ hδ heps ho hnonneg
    (eventually_le_of_early_late V early late eps o C δ hsplit hearly hlate)

/-- The conclusion of Step 1 of `lem:dgt4-linearization-from-survival`: if
`V ≤ 2 early + 2 late` eventually, `early ≤ C ε_R(δ) + C/(δR²)` for every
`δ > 0`, `late ≤ C δ² + o(1)`, and `V` is eventually nonnegative and bounded,
then `V → 0`. -/
theorem tendsto_zero_derivVar (V early late eps o : ℝ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (heps : ∀ δ : ℝ, 0 < δ → Tendsto eps atTop (𝓝 0))
    (ho : ∀ δ : ℝ, 0 < δ → Tendsto o atTop (𝓝 0))
    (hnonneg : ∀ᶠ R : ℝ in atTop, 0 ≤ V R)
    (hbdd : ∀ᶠ R : ℝ in atTop, V R ≤ B)
    (hsplit : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, V R ≤ 2 * early R + 2 * late R)
    (hearly : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, early R ≤ C * eps R + C / (δ * R ^ 2))
    (hlate : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, late R ≤ C * δ ^ 2 + o R) :
    Tendsto V atTop (𝓝 0) :=
  tendsto_zero_of_limsup_le V C B hC hnonneg hbdd fun δ hδ =>
    limsup_le_of_early_late V eps o C δ hδ (heps δ hδ) (ho δ hδ) hnonneg
      (eventually_le_of_early_late V early late eps o C δ (hsplit δ hδ) (hearly δ hδ)
        (hlate δ hδ))

end Sandpile
