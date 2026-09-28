import Sandpile.Support.CrossRescale

/-!
# The rescaled crossing estimate

`eq:rescaled-crossing-estimate` (`sandpile.tex:2404-2413`) for the crossing
events, from the chain identity of `Sandpile/Support/CrossRescale.lean` and the
bracket of `Sandpile/Support/CrossUnion.lean`.

  "Observe that Proposition~\ref{prop:fixed-scale-crossings} and
   `eq:cont-field-scaling` imply that, for all `a>0` and `h>0`, there is `p>0`
   such that for every `L≥1` there is `s_0` such that
   `P(H_{[-a,a]×[0,2h]}(L b(s); 𝒳_s)) ≥ p` for every `0<s<s_0`."

With `R = h/s`, the rectangle `[-a,a]×[0,2h]` dilated by `1/s` is
`[-(a/h)R,(a/h)R]×[0,2R]`, which is the rectangle of
`prop:fixed-scale-crossings` with `θ = a/h`; the level `L b(s)` at scale `s`
becomes the level `L b(s)/b` at scale one, where `b` is the field scale `s` or
`√s`.  This module carries out that comparison.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- `eq:rescaled-crossing-estimate` (`sandpile.tex:2404-2413`) for the crossing
events themselves: a crossing of the dilated rectangle by `{𝒳_1 ≥ λ}` forces, no
less often, a crossing of the rectangle by `{𝒳_s ≥ b(λ-ε)}`, for every `ε > 0`
and every RATIONAL scale `s`.

The `ε` is the price of passing through the chain events, which is the only way
to compare the two probabilities: the scaling of the field is an equality in
LAW, a crossing event is not known to be measurable, and equality in law says
nothing about the outer measure of a set that is not measurable.  The paper
absorbs this loss in the slack of `L ≥ 1` in its statement. -/
theorem measure_crossing_ballField_scale
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℚ} (hs : 0 < (s : ℝ))
    (hcont1 : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω)
    (hconts : ∀ᵐ ω ∂P, Continuous fun u => ballField d W (s : ℝ) u ω)
    (p q : Fin 2 → ℝ) (h0 : p 0 < q 0) (h1 : p 1 < q 1) (i : Fin 2)
    (lam ε : ℝ) (hε : 0 < ε) :
    P {ω | Crosses (fun k => (s : ℝ)⁻¹ * p k) (fun k => (s : ℝ)⁻¹ * q k) i
        {u | lam ≤ ballField d W 1 u ω}}
      ≤ P {ω | Crosses p q i
        {u | (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε)
            ≤ ballField d W (s : ℝ) u ω}} := by
  have hσ : (0 : ℝ) < (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) := by
    by_cases h : d = 2
    · rw [if_pos h]; exact hs
    · rw [if_neg h]; exact Real.sqrt_pos.mpr hs
  have hinv : (0 : ℝ) < (s : ℝ)⁻¹ := inv_pos.mpr hs
  have hd0 : (s : ℝ)⁻¹ * p 0 < (s : ℝ)⁻¹ * q 0 := mul_lt_mul_of_pos_left h0 hinv
  have hd1 : (s : ℝ)⁻¹ * p 1 < (s : ℝ)⁻¹ * q 1 := mul_lt_mul_of_pos_left h1 hinv
  have hlev : (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε) /
      (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) = lam - ε :=
    mul_div_cancel_left₀ _ (ne_of_gt hσ)
  have hstep := measure_crossApprox_ballField_scale hGauss hd hW hs p q i
    ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε))
  rw [hlev] at hstep
  calc P {ω | Crosses (fun k => (s : ℝ)⁻¹ * p k) (fun k => (s : ℝ)⁻¹ * q k) i
        {u | lam ≤ ballField d W 1 u ω}}
      ≤ P (crossApprox (ballField d W 1) (fun k => (s : ℝ)⁻¹ * p k)
          (fun k => (s : ℝ)⁻¹ * q k) i (lam - ε)) :=
        measure_crossing_le_crossApprox P hd0 hd1 hε hcont1
    _ = P (crossApprox (ballField d W (s : ℝ)) p q i
          ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε))) := hstep.symm
    _ ≤ P {ω | Crosses p q i
          {u | (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε)
              ≤ ballField d W (s : ℝ) u ω}} :=
        measure_crossApprox_le_crossing P hconts

/-- `eq:rescaled-crossing-estimate` (`sandpile.tex:2404-2413`) itself:

  "Proposition~\ref{prop:fixed-scale-crossings} and `eq:cont-field-scaling`
   imply that, for all `a>0` and `h>0`, there is `p>0` such that for every
   `L≥1` there is `s_0=s_0(a,h,L)∈(0,1]` such that
   `P(H_{[-a,a]×[0,2h]}(L b(s); 𝒳_s)) ≥ p` for every `0<s<s_0`."

The hypothesis is the conclusion of `prop:fixed-scale-crossings` for the unit
field with `θ = a/h`, and the conclusion is the paper's, at the rational scales
`Sandpile/Support/CrossRescale.lean` needs.  With `R = h/s` the paper's three
identities are `(a/h)R = a/s`, `2R = 2h/s` and `h(L+1)/R = (L+1)s`; the crossing
scale `b(s)` appears as `(if d = 2 then s else √s) · s`, which is `s²` in
dimension two and `s^{3/2}` in dimension three, exactly
`eq:continuum-crossing-scale`.

The `L+1` in place of `L`, and the `p/2` in place of `p`, are the two slacks the
passage through the chain events costs: the liminf gives every value below `p`
eventually, and the bracket costs an `ε` in the level, taken here to be `s`. -/
theorem rescaled_crossing_estimate
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω)
    (al h : ℝ) (hal : 0 < al) (hh : 0 < h) (pr : ℝ) (hpr : 0 < pr)
    (hprop : ∀ L : ℝ, 0 ≤ L → ENNReal.ofReal pr ≤ liminf (fun R : ℝ =>
      P {ω | Crosses ![-((al / h) * R), 0] ![(al / h) * R, 2 * R] 0
        {u | L / R ≤ ballField d W 1 u ω}}) atTop)
    (L : ℝ) (hL : 1 ≤ L) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℚ, 0 < (s : ℝ) → (s : ℝ) < s₀ →
      ENNReal.ofReal (pr / 2) ≤ P {ω | Crosses ![-al, 0] ![al, 2 * h] 0
        {u | L * ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (s : ℝ))
          ≤ ballField d W (s : ℝ) u ω}} := by
  have hL0 : (0 : ℝ) ≤ h * (L + 1) := by nlinarith
  have hlt : ENNReal.ofReal (pr / 2) < ENNReal.ofReal pr :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mpr (by linarith)
  have hev := eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt (hprop _ hL0))
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp hev
  have hmax : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨min (h / max R₀ 1) 1, lt_min (div_pos hh hmax) one_pos, ?_⟩
  intro s hs hss
  have hss' : (s : ℝ) < h / max R₀ 1 := lt_of_lt_of_le hss (min_le_left _ _)
  have hs1 : (s : ℝ) ≤ 1 := (lt_of_lt_of_le hss (min_le_right _ _)).le
  have hne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hhne : h ≠ 0 := ne_of_gt hh
  have h2 : (s : ℝ) * max R₀ 1 < h := (lt_div_iff₀ hmax).mp hss'
  have hstep : max R₀ 1 ≤ h / (s : ℝ) := by
    rw [le_div_iff₀ hs]
    calc max R₀ 1 * (s : ℝ) = (s : ℝ) * max R₀ 1 := mul_comm _ _
      _ ≤ h := le_of_lt h2
  have hRle : R₀ ≤ h / (s : ℝ) := le_trans (le_max_left R₀ 1) hstep
  have hmain := hR₀ (h / (s : ℝ)) hRle
  have hid1 : (al / h) * (h / (s : ℝ)) = (s : ℝ)⁻¹ * al := by
    rw [div_mul_div_comm, mul_comm al h, mul_div_mul_left _ _ hhne, inv_mul_eq_div]
  have hid2 : 2 * (h / (s : ℝ)) = (s : ℝ)⁻¹ * (2 * h) := by
    rw [inv_mul_eq_div, mul_div_assoc]
  have hid3 : h * (L + 1) / (h / (s : ℝ)) = (L + 1) * (s : ℝ) := by
    rw [div_div_eq_mul_div, mul_assoc, mul_div_cancel_left₀ _ hhne]
  have hcp : (fun k => (s : ℝ)⁻¹ * (![-al, 0] : Fin 2 → ℝ) k)
      = ![-((al / h) * (h / (s : ℝ))), 0] := by
    funext k
    fin_cases k
    · show (s : ℝ)⁻¹ * (-al) = -((al / h) * (h / (s : ℝ)))
      rw [hid1]
      ring
    · show (s : ℝ)⁻¹ * (0 : ℝ) = 0
      ring
  have hcq : (fun k => (s : ℝ)⁻¹ * (![al, 2 * h] : Fin 2 → ℝ) k)
      = ![(al / h) * (h / (s : ℝ)), 2 * (h / (s : ℝ))] := by
    funext k
    fin_cases k
    · show (s : ℝ)⁻¹ * al = (al / h) * (h / (s : ℝ))
      rw [hid1]
    · show (s : ℝ)⁻¹ * (2 * h) = 2 * (h / (s : ℝ))
      rw [hid2]
  have hscale := measure_crossing_ballField_scale hGauss hd hW hs
    (hcont 1 one_pos le_rfl) (hcont (s : ℝ) hs hs1) ![-al, 0] ![al, 2 * h]
    (by simp; linarith) (by simp; linarith) 0 ((L + 1) * (s : ℝ)) (s : ℝ) hs
  rw [hcp, hcq] at hscale
  have hlev : (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * ((L + 1) * (s : ℝ) - (s : ℝ))
      = L * ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (s : ℝ)) := by ring
  rw [hlev] at hscale
  rw [hid3] at hmain
  exact le_trans (le_of_lt hmain) hscale


end Sandpile.Support
