/-
The capped ball-stopped field is defined from the actual heat potential.
Its payoff is an admissible lower bound for the localized stopping value.
The eventual uniform approximation of this field by the ball Green field is
kept as the precise analytic input; the resulting value comparison is proved.
-/
import Sandpile.Support.LimValue
import Sandpile.Support.LimBallContinuity

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal RealInnerProductSpace

open TopologicalSpace

theorem Sandpile.Support.ae_eq_of_continuous_versions {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [SeparableSpace X]
    (P : Measure Ω) (F G : X → Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, Continuous fun x => F x ω)
    (hG : ∀ᵐ ω ∂P, Continuous fun x => G x ω)
    (heq : ∀ x, F x =ᵐ[P] G x) :
    ∀ᵐ ω ∂P, ∀ x, F x ω = G x ω := by
  obtain ⟨S, hS, hSd⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable S := hS.to_subtype
  have hEq : ∀ᵐ ω ∂P, ∀ x : S, F x ω = G x ω :=
    ae_all_iff.mpr fun x => heq x
  filter_upwards [hF, hG, hEq] with ω hωF hωG hωEq
  have he : (fun x => F x ω) = fun x => G x ω :=
    Continuous.ext_on hSd hωF hωG (fun x hx => hωEq ⟨x, hx⟩)
  exact congrFun he

noncomputable def Sandpile.Support.ballStoppedField {ΩW ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ) (PB : Measure ΩB)
    (B : Space d → ℝ≥0 → ΩB → Space d) (s T : ℝ) (u : Space 2) (ω : ΩW) : ℝ :=
  (2 * (d : ℝ))⁻¹ * (Z T (planePoint u) ω +
    ∫ η, -Z
      (T - (LatticeProb.exitTimeTrunc (B (planePoint u)) (planePoint u) s T.toNNReal η : ℝ))
      (B (planePoint u) (LatticeProb.exitTimeTrunc (B (planePoint u))
        (planePoint u) s T.toNNReal η) η) ω ∂PB)

theorem Sandpile.Support.ae_ballStoppedField_le_localizedValue {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ}
    (hd : d = 2 ∨ d = 3) {PW : Measure ΩW} {Z : ℝ → Space d → ΩW → ℝ}
    (hZ : Sandpile.Support.ContinuousHeatPotential d Z PW)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : Space d → ℝ≥0 → ΩB → Space d)
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂PW, ∀ s : ℝ, s ≤ 1 → ∀ u : Space 2,
      2 * (d : ℝ) * Sandpile.Support.ballStoppedField d Z PB B s T u ω ≤
        Sandpile.Support.localizedValue d Z PB B T u ω := by
  have hd0 : 2 * (d : ℝ) ≠ 0 := by rcases hd with rfl | rfl <;> norm_num
  filter_upwards [hZ T hT] with ω hω
  intro s hs u
  have hcont : ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
      (Set.Icc 0 T ×ˢ Metric.closedBall (planePoint u) 1) :=
    hω.mono (Set.prod_mono (Subset.refl _) (Set.subset_univ _))
  have hpay := Sandpile.Support.ballStopped_payoff_le_of_continuous
    (B (planePoint u)) PB (fun t z => Z t z ω)
    T s 1 (planePoint u) hT.le (by norm_num) hs (hB _).start (hBc _) hcont
  simpa only [Sandpile.Support.ballStoppedField, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul,
    Sandpile.Support.localizedValue] using hpay

def Sandpile.Support.BallStoppedApproximation (d : ℕ) : Prop :=
  ∀ (k : ℕ) (s : Fin k → ℚ), (∀ i, 0 < s i ∧ s i < 1) →
  ∀ (N : ℕ) (a b : Fin N → Fin 2 → ℝ) (c δ : ℝ), 0 < c → 0 < δ →
  ∀ᶠ T : ℝ in Filter.atTop,
    ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
      (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W PW →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂PW, Continuous fun u => ballField d W s u ω) →
    ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
        Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
      ContinuousHeatPotential d Z PW →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
      (∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB) →
      (∀ y ω, Continuous fun t => B y t ω) →
      (∀ y t, StronglyMeasurable (B y t)) →
    PW {ω | ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2),
        (∃ j, u ∈ rectSet (a j) (b j)) →
        |ballStoppedField d Z PB B (s i : ℝ) T u ω - ballField d W (s i : ℝ) u ω| ≤ c}ᶜ
      ≤ ENNReal.ofReal δ


theorem Sandpile.Support.approximation_good_event_lower {Ω U I : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (K : Set U) (F G : I → U → Ω → ℝ)
    (V : U → Ω → ℝ) (D c δ : ℝ) (hD : 0 ≤ D)
    (hdom : ∀ᵐ ω ∂P, ∀ i u, u ∈ K → D * G i u ω ≤ V u ω)
    (happrox : P {ω | ∀ i u, u ∈ K → |G i u ω - F i u ω| ≤ c}ᶜ ≤ ENNReal.ofReal δ) :
    P {ω | ∀ i u, u ∈ K → D * (F i u ω - c) ≤ V u ω}ᶜ ≤ ENNReal.ofReal δ := by
  apply le_trans (measure_mono_ae ?_) happrox
  filter_upwards [hdom] with ω hω
  intro hbad hgood
  apply hbad
  intro i u hu
  have he := (abs_le.mp (hgood i u hu)).1
  have hx := mul_le_mul_of_nonneg_left (show F i u ω - c ≤ G i u ω by linarith) hD
  exact hx.trans (hω i u hu)

theorem Sandpile.Support.localizedValueApproximation_of_ballStoppedApproximation {d : ℕ}
    (hd : d = 2 ∨ d = 3) (hApprox : Sandpile.Support.BallStoppedApproximation d) :
    Sandpile.Support.LocalizedValueApproximation d := by
  intro k s hs N a b c δ hc hδ
  have hLarge := (hApprox k s hs N a b c δ hc hδ).and (Filter.eventually_gt_atTop (0 : ℝ))
  obtain ⟨T, hAppT, hT⟩ := hLarge.exists
  refine ⟨T, hT, ?_⟩
  intro ΩW mW PW hPW W hW hX Z hmod hZ ΩB mB PB hPB B hB hBc hBm
  refine Sandpile.Support.approximation_good_event_lower PW
    {u : Space 2 | ∃ j, u ∈ rectSet (a j) (b j)}
    (fun i u ω => ballField d W (s i : ℝ) u ω)
    (fun i u ω => Sandpile.Support.ballStoppedField d Z PB B (s i : ℝ) T u ω)
    (Sandpile.Support.localizedValue d Z PB B T) (2 * (d : ℝ)) c δ (by positivity) ?_
    (hAppT ΩW PW W hW hX Z hmod hZ ΩB PB B hB hBc hBm)
  filter_upwards [Sandpile.Support.ae_ballStoppedField_le_localizedValue hd hZ PB B hB hBc hT]
    with ω hω
  intro i u _
  exact hω (s i) (by exact_mod_cast (hs i).2.le) u
