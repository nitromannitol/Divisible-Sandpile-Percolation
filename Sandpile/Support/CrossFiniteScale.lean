/-
Step 1 of `lem:finite-scale-extraction` (`sandpile.tex:2431-2484`), as far as the
rescaled crossing estimate carries it.

  "We first use `eq:rescaled-crossing-estimate` and a 0-1 argument to get
   almost-sure crossings at arbitrarily small scales for a fixed rectangle."

The first half of that sentence is here: the union over the rational scales
below any prescribed bound has probability at least a constant that does not
depend on the bound or on the level parameter `L`.  The 0-1 argument that raises
that constant to one is the tail-field argument of `sandpile.tex:2455-2482`,
which is not carried out here.
-/
import Sandpile.Support.CrossRescaleCrossing

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The first display of Step 1 of `lem:finite-scale-extraction`
(`sandpile.tex:2437-2447`):

  "For every `j,L≥1`, `eq:rescaled-crossing-estimate` gives
   `P(⋃_{s∈(0,1/j)∩ℚ} H_𝓡(L b(s); 𝒳_s)) ≥ p`, with `p>0` independent of `j`
   and `L`: choose a rational `s < min{1/j, s_0}`."

The choice of the rational scale is `exists_rat_btwn` applied to the smaller of
the two bounds, and the union is over the same rational scales the chain
vocabulary of `Sandpile/Support/CrossRescale.lean` is covariant under.  The
bound `p/2` does not depend on the prescribed `η`, which is the point of the
display. -/
theorem union_rational_scales_ge
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω)
    (al h : ℝ) (hal : 0 < al) (hh : 0 < h) (pr : ℝ) (hpr : 0 < pr)
    (hprop : ∀ L : ℝ, 0 ≤ L → ENNReal.ofReal pr ≤ liminf (fun R : ℝ =>
      P {ω | Crosses ![-((al / h) * R), 0] ![(al / h) * R, 2 * R] 0
        {u | L / R ≤ ballField d W 1 u ω}}) atTop)
    (L : ℝ) (hL : 1 ≤ L) (η : ℝ) (hη : 0 < η) :
    ENNReal.ofReal (pr / 2) ≤ P (⋃ s : ℚ, ⋃ _ : 0 < (s : ℝ) ∧ (s : ℝ) < η,
      {ω | Crosses ![-al, 0] ![al, 2 * h] 0
        {u | L * ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (s : ℝ))
          ≤ ballField d W (s : ℝ) u ω}}) := by
  obtain ⟨s₀, hs₀, hmain⟩ :=
    rescaled_crossing_estimate hGauss hd hW hcont al h hal hh pr hpr hprop L hL
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show (0 : ℝ) < min η s₀ from lt_min hη hs₀)
  have hspos : 0 < (s : ℝ) := hs1
  have hsη : (s : ℝ) < η := lt_of_lt_of_le hs2 (min_le_left _ _)
  have hss₀ : (s : ℝ) < s₀ := lt_of_lt_of_le hs2 (min_le_right _ _)
  refine le_trans (hmain s hspos hss₀) (measure_mono ?_)
  exact Set.subset_iUnion₂ (s := fun (t : ℚ) (_ : 0 < (t : ℝ) ∧ (t : ℝ) < η) =>
    {ω | Crosses ![-al, 0] ![al, 2 * h] 0
      {u | L * ((if d = 2 then (t : ℝ) else Real.sqrt (t : ℝ)) * (t : ℝ))
        ≤ ballField d W (t : ℝ) u ω}}) s ⟨hspos, hsη⟩

/-- The continuity from below of Step 2 of `lem:finite-scale-extraction`
(`sandpile.tex:2497-2502`):

  "By continuity from below, there are finitely many pairs `(n_1,S_1),…,(n_m,S_m)`
   such that `P(⋃_{i=1}^m ⋂_j H_{𝓡_j}(4/n_i; max_{s∈S_i} 𝒳_s)) ≥ 1-ε`."

An increasing sequence of events whose union has probability one has a stage of
probability at least `1-ε`.  The sets need not be measurable: Mathlib's
continuity from below is stated for the outer measure of an increasing sequence
of arbitrary sets, which is the generality the crossing events need. -/
theorem exists_finite_stage {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : ℕ → Set Ω) (hmono : Monotone A)
    (hfull : P (⋃ i, A i) = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ENNReal.ofReal (1 - ε) ≤ P (A m) := by
  have hlt : ENNReal.ofReal (1 - ε) < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr (by linarith)
  have htend := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hfull] at htend
  have hev := htend.eventually (eventually_gt_nhds hlt)
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨m, le_of_lt hm⟩


/-- The chain form of the transport, which is the one Step 1's zero-one argument
needs: the lower bound it produces is a bound on a MEASURABLE event.  It is the
first two steps of `measure_crossing_ballField_scale`, stopped before the last
bracket.

The crossing events of the paper's Step 1 are not known to be measurable, so
neither the intersection over `L` and `j` nor the tail-field argument can be run
on them directly.  The chain events are measurable, a countable union of them is
measurable, and the bracket returns to the crossing events at the end. -/
theorem measure_chain_ballField_scale_ge
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℚ} (hs : 0 < (s : ℝ))
    (hcont1 : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω)
    (p q : Fin 2 → ℝ) (h0 : p 0 < q 0) (h1 : p 1 < q 1) (i : Fin 2)
    (lam ε : ℝ) (hε : 0 < ε) :
    P {ω | Crosses (fun k => (s : ℝ)⁻¹ * p k) (fun k => (s : ℝ)⁻¹ * q k) i
        {u | lam ≤ ballField d W 1 u ω}}
      ≤ P (crossApprox (ballField d W (s : ℝ)) p q i
          ((if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * (lam - ε))) := by
  have hσ : (0 : ℝ) < (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) := by
    by_cases hdd : d = 2
    · rw [if_pos hdd]; exact hs
    · rw [if_neg hdd]; exact Real.sqrt_pos.mpr hs
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

/-- The union over the rational scales of the chain events is measurable, being
a countable union of measurable sets.  This is what makes the zero-one argument
of `sandpile.tex:2455-2482` available in this vocabulary. -/
theorem measurableSet_union_rational_chain
    {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hmeas : ∀ (t : ℝ) (u : Sandpile.Continuum.Space 2), Measurable (ballField d W t u))
    (p q : Fin 2 → ℝ) (i : Fin 2) (lev : ℚ → ℝ) (η : ℝ) :
    MeasurableSet (⋃ s : ℚ, ⋃ _ : 0 < (s : ℝ) ∧ (s : ℝ) < η,
      crossApprox (ballField d W (s : ℝ)) p q i (lev s)) :=
  MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    measurableSet_crossApprox (hmeas (s : ℝ)) p q i (lev s)


end Sandpile.Support
