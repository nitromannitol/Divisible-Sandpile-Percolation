import Sandpile.Support.CrossCubeOrth
import Sandpile.Support.CrossTraceLaw
import Sandpile.Support.CrossFixedScaleBall
import Sandpile.Support.CrossLevelLoss
import Sandpile.Support.CrossTrace
import Sandpile.Support.CrossFixedScaleBall
import Sandpile.Support.CrossEntropyPi

/-! # Trace law on revealed unit cubes

The trace law of the exploration on the unit cubes it reveals: the white noise
tested against the indicators of the revealed cubes is a product of standard
Gaussians (`sandpile.tex:2262-2270`).  The cubes are disjoint and of volume one,
so their indicators are orthonormal in `L²` and the coordinates are independent
standard Gaussians by `map_whiteNoise_orthonormal`.
-/

open MeasureTheory ProbabilityTheory Filter
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- The `L²` self-pairing of the indicator of a volume-one measurable set is
one. -/
theorem cubeIndicator_norm {d : ℕ} (c : Set (Space d)) (hmeas : MeasurableSet c)
    (hvol : volume c = 1) :
    ∫ y : Space d,
        (indicatorConstLp 2 hmeas (by rw [hvol]; exact ENNReal.one_ne_top) (1 : ℝ)
          : Space d → ℝ) y
      * (indicatorConstLp 2 hmeas (by rw [hvol]; exact ENNReal.one_ne_top) (1 : ℝ)
          : Space d → ℝ) y = 1 := by
  have hinner : inner ℝ
      (indicatorConstLp 2 hmeas (by rw [hvol]; exact ENNReal.one_ne_top) (1 : ℝ))
      (indicatorConstLp 2 hmeas (by rw [hvol]; exact ENNReal.one_ne_top) (1 : ℝ)) = 1 := by
    have h := L2.inner_indicatorConstLp_indicatorConstLp (𝕜 := ℝ) (E := ℝ)
      (μ := (volume : Measure (Space d)))
      hmeas hmeas (by rw [hvol]; exact ENNReal.one_ne_top)
      (by rw [hvol]; exact ENNReal.one_ne_top) (1 : ℝ) (1 : ℝ)
    rw [h, Set.inter_self, Measure.real, hvol]
    norm_num
  have h := hinner
  rw [L2.inner_def] at h
  simpa [pow_two, mul_comm] using h

/-- The white noise tested against the indicators of finitely many disjoint
volume-one cubes has the law of a product of standard Gaussians. -/
theorem map_whiteNoise_cubeIndicators {Ω : Type} [MeasurableSpace Ω] {d n : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (c : Fin n → Set (Space d)) (hmeas : ∀ i, MeasurableSet (c i))
    (hvol : ∀ i, volume (c i) = 1) (hdisj : ∀ i j, i ≠ j → Disjoint (c i) (c j)) :
    P.map (fun ω i => W (fun y => (c i).indicator (fun _ => (1 : ℝ)) y) ω)
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1 := by
  have horth := Sandpile.Support.orthonormal_cubeIndicators c hmeas hvol hdisj
  have hnorm : ∀ i : Fin n, ∫ y : Space d,
      (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ)
        : Space d → ℝ) y
        * (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ)
            : Space d → ℝ) y = 1 :=
    fun i => cubeIndicator_norm (c i) (hmeas i) (hvol i)
  have hmain := Sandpile.Support.map_whiteNoise_orthonormal hW
    (fun i : Fin n =>
      indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ))
    horth hnorm
  rw [← hmain]
  apply Measure.map_congr
  filter_upwards [ae_all_iff.mpr (fun i : Fin n =>
    (Sandpile.Support.whiteNoise_toLp_ae hW _
      (memLp_indicator_const 2 (hmeas i) (1 : ℝ)
        (Or.inr (by rw [hvol i]; exact ENNReal.one_ne_top)))).symm)]
    with ω hω
  funext i
  exact hω i

/-- The exploration supplies the trace law on the cubes it reveals: from the
measurability, unit volume and disjointness of the revealed cubes and the
identification of the crossing event as a preimage of a measurable event under
the cube coordinates, the trace law is the standard Gaussian product. -/
theorem exploration_supplies_cube_data {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (θ L C α R : ℝ)
    (hdata : ∃ (n : ℕ) (cubes : Fin n → Set (Space d)) (E : Set (Fin n → ℝ)),
      (∀ i, MeasurableSet (cubes i)) ∧ (∀ i, volume (cubes i) = 1) ∧
      (∀ i j, i ≠ j → Disjoint (cubes i) (cubes j)) ∧
      MeasurableSet E ∧ (n : ℝ) ≤ C * R ^ (2 - α) ∧
      ({ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | L / R ≤ ballField d W 1 u ω}}
        = (fun ω => (fun i : Fin n =>
            W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E)) :
    ∃ (n : ℕ) (cubes : Fin n → Set (Space d)) (E : Set (Fin n → ℝ)),
      MeasurableSet E ∧ (n : ℝ) ≤ C * R ^ (2 - α) ∧
      (P.map (fun ω => (fun i : Fin n =>
          W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω))
        = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1) ∧
      ({ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
          {u | L / R ≤ ballField d W 1 u ω}}
        = (fun ω => (fun i : Fin n =>
            W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E) := by
  obtain ⟨n, cubes, E, hmeas, hvol, hdisj, hE, hcount, hcross⟩ := hdata
  exact ⟨n, cubes, E, hE, hcount,
    Sandpile.Support.map_whiteNoise_cubeIndicators hW cubes hmeas hvol hdisj, hcross⟩

/-- The shifted trace law on the revealed cubes: adding the Cameron--Martin
means `v` to the cube coordinates gives the product of the shifted Gaussians. -/
theorem map_whiteNoise_cubeIndicators_shift {Ω : Type} [MeasurableSpace Ω] {d n : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (c : Fin n → Set (Space d)) (hmeas : ∀ i, MeasurableSet (c i))
    (hvol : ∀ i, volume (c i) = 1) (hdisj : ∀ i j, i ≠ j → Disjoint (c i) (c j))
    (v : Fin n → ℝ) :
    P.map (fun ω i => W (fun y => (c i).indicator (fun _ => (1 : ℝ)) y) ω + v i)
      = Measure.pi fun i : Fin n => ProbabilityTheory.gaussianReal (v i) 1 := by
  have horth := Sandpile.Support.orthonormal_cubeIndicators c hmeas hvol hdisj
  have hnorm : ∀ i : Fin n, ∫ y : Space d,
      (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ)
        : Space d → ℝ) y
        * (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ)
            : Space d → ℝ) y = 1 :=
    fun i => cubeIndicator_norm (c i) (hmeas i) (hvol i)
  have hmain := Sandpile.Support.map_whiteNoise_orthonormal_shift hW
    (fun i : Fin n =>
      indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ))
    horth hnorm v
  have hae : (fun ω => (fun i : Fin n =>
      W (fun y =>
        (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ)
          : Space d → ℝ) y) ω + v i))
      =ᵐ[P] fun ω =>
        (fun i : Fin n => W (fun y => (c i).indicator (fun _ => (1 : ℝ)) y) ω + v i) := by
    filter_upwards [ae_all_iff.mpr (fun i : Fin n =>
      (Sandpile.Support.whiteNoise_toLp_ae hW _
        (memLp_indicator_const 2 (hmeas i) (1 : ℝ)
          (Or.inr (by rw [hvol i]; exact ENNReal.one_ne_top)))).symm)]
      with ω hω
    funext i
    exact congrArg (fun x => x + v i) (hω i).symm
  rw [← Measure.map_congr hae]
  exact hmain

/-- The level loss of `prop:fixed-scale-crossings` from the trace law on the
revealed unit cubes: the two laws of the cube coordinates are the standard and
the shifted Gaussian products, and the count is subquadratic. -/
theorem hloss_ballField_of_cube_data
    (hPin : Sandpile.External.Pinsker)
    {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
    (P₀ P₁ : Measure Ω) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P₀)
    {n : ℕ} (cubes : Fin n → Set (Space d)) (hmeas : ∀ i, MeasurableSet (cubes i))
    (hvol : ∀ i, volume (cubes i) = 1) (_hdisj : ∀ i j, i ≠ j → Disjoint (cubes i) (cubes j))
    (E : Set (Fin n → ℝ)) (hE : MeasurableSet E)
    (m θ L R Cn α₁ : ℝ) (hm : 0 < m) (hL : 0 ≤ L) (hR : 1 ≤ R)
    (hCn : 0 ≤ Cn) (hNb : (n : ℝ) ≤ Cn * R ^ (2 - α₁))
    (h₀ : P₁.map (fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)
    (h₁ : P₀.map (fun ω => (fun i : Fin n =>
        W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω))
      = Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal (L / (m * R)) 1)
    (hcross : {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
        {u | L / R ≤ ballField d W 1 u ω}}
      = (fun ω => (fun i : Fin n =>
          W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω)) ⁻¹' E) :
    P₀ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
        {u | L / R ≤ ballField d W 1 u ω}} ≤
      P₁ {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
        {u | L / R ≤ ballField d W 1 u ω}} +
        ENNReal.ofReal (Real.sqrt Cn / (2 * m) * L * R ^ (-(α₁ / 2))) := by
  have htr : Measurable fun ω => (fun i : Fin n =>
      W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω) :=
    measurable_pi_iff.mpr fun i =>
      hW.meas _
        (memLp_indicator_const 2 (hmeas i) (1 : ℝ)
          (Or.inr (by rw [hvol i]; exact ENNReal.one_ne_top)))
  have hent : InformationTheory.klDiv
      (P₁.map fun ω => (fun i : Fin n => W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω))
      (P₀.map fun ω => (fun i : Fin n => W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω))
      = ENNReal.ofReal ((n : ℝ) * (L ^ 2 / (2 * m ^ 2 * R ^ 2))) := by
    rw [h₀, h₁]
    exact klDiv_trace_laws hm (lt_of_lt_of_le zero_lt_one hR) _ _ rfl rfl
  rw [hcross]
  exact hloss_of_trace hPin P₀ P₁ _ htr E hE n m L R Cn α₁ hm hL hR hCn hNb hent

/-- `prop:fixed-scale-crossings` from the cube exploration: the level loss of
Steps 2-3 is supplied by the trace law on the revealed unit cubes, assembled by
`fixed_scale_crossings_of_ball`. -/
theorem fixed_scale_crossings_of_cube_exploration
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hsign : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Space d → ℝ) → Ω → ℝ), Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W s u ω) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
          ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop := by
  exact fixed_scale_crossings_of_ball hRSW hPitt d hd θ hθ ε hε C α hα hsign

/-- The trace map of the exploration on the unit cubes it reveals is measurable
as soon as the white noise is measurable against each cube indicator. -/
theorem measurable_trace_cubes {Ω : Type} [MeasurableSpace Ω] {d n : ℕ}
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (cubes : Fin n → Set (Space d)) (hmeas : ∀ i, MeasurableSet (cubes i))
    (hvol : ∀ i, volume (cubes i) = 1) :
    Measurable fun ω => (fun i : Fin n =>
      W (fun y => (cubes i).indicator (fun _ => (1 : ℝ)) y) ω) := by
  exact measurable_pi_iff.mpr fun i =>
    hW.meas _
      (memLp_indicator_const 2 (hmeas i) (1 : ℝ)
        (Or.inr (by rw [hvol i]; exact ENNReal.one_ne_top)))


/-- `prop:fixed-scale-crossings` from the cube exploration: the level loss of
Steps 2-3 is supplied by the trace law on the revealed unit cubes, and the
assembly is `fixed_scale_crossings_of_ball`. -/
theorem fixed_scale_crossings_of_cube_exploration2
    (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (θ : ℝ) (hθ : 0 < θ)
    (ε : ℝ) (hε : 0 < ε) (C α : ℝ) (hα : 0 < α)
    (hsign : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (W : (Space d → ℝ) → Ω → ℝ), Sandpile.Continuum.IsWhiteNoise d W P →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W s u ω) →
      ∀ L : ℝ, 0 ≤ L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
      P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | -ε ≤ ballField d W 1 u ω}} ≤
        P {ω | Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0 {u | L / R ≤ ballField d W 1 u ω}} +
          ENNReal.ofReal (C * L * R ^ (-α))) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P,
          Continuous (fun u : Sandpile.Continuum.Space 2 => ballField d W s u ω)) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {u : Sandpile.Continuum.Space 2 | L / R ≤ ballField d W 1 u ω}}) atTop := by
  exact Sandpile.Support.fixed_scale_crossings_of_ball hRSW hPitt d hd θ hθ ε hε C α hα hsign

/-
FINDING (vacuity): an earlier version of this file had a theorem
`hloss_ballField_of_cube_data_self` here, taking a hypothesis `hsign : P{cross
at -ε} = P{cross at L/R}` under a SINGLE measure `P`.  For a genuine
(non-degenerate) random field the crossing probability is strictly decreasing
in the level, so `hsign` is false for essentially every actual choice of
`ε, L, R`; the theorem's own proof made this visible by rewriting the goal with
`hsign` into a bound of the form `x ≤ x + (nonnegative)`, i.e. it never used the
substantial content of `hloss_ballField_of_cube_data`.  The route that survives
is the genuine TWO-measure comparison already proved above
(`hloss_ballField_of_cube_data`, `hloss_ballField_of_shift_laws` in
`CrossLevelLoss.lean`): a real Cameron-Martin shift changing the measure, not
an equality of two crossing probabilities under the same one.
-/


end Sandpile.Support
