/-
Couplings of the rescaled heat potential and its continuous Gaussian limit.
The finite-dimensional convergence and equicontinuity clauses give probability
measures with the original scenery and white-noise marginals and uniform control
on each compact subset of the time strip.
-/
import Sandpile.Support.StopFieldCoupling
import Sandpile.Support.HeatPotentialDefs
import Sandpile.Continuum.WhiteNoise
import Sandpile.Law

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.Continuum.heat_field_coupling :
∀ (d : ℕ), 1 ≤ d →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
    ∀ (ΩW : Type*) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
      (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W PW →
    ∀ T : ℝ, 0 < T →
    (∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1 q.2 ω) →
    (∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
        (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
            Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
              (Sandpile.scenery d σ) (r i) (w i))
          atTop
          (fun (ω : ΩW) (i : Fin m) =>
            Sandpile.Continuum.gaussianPotential d (variance id ν) W (r i) (w i) ω)
          (fun _ => Sandpile.centeredMassLaw d ν) PW) →
    (∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
        K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, M < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                (Sandpile.scenery d σ) p.1 p.2|} ≤ ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
                η < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) p.1 p.2 -
                  Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) q.1 q.2|} ≤ ENNReal.ofReal ε)) →
    ∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
      K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
          P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
          P.map Prod.snd = PW ∧
          P {p | ∃ q ∈ K,
              ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d p.1) q.1 q.2 -
                  Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1 q.2 p.2|}
            ≤ ENNReal.ofReal δ := by
  intro d _hd ν _ ΩW _ PW _ W _hW T _hT hcont hfdd htight K hK hKT ε δ hε hδ
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ℝ → (Sandpile.Site d → ℝ) → K → ℝ := fun R σ q =>
    Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1.1 q.1.2
  let g : ΩW → K → ℝ := fun ω q =>
    Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1.1 q.1.2 ω
  have hfd : ∀ (m : ℕ) (x : Fin m → K), TendstoInDistribution
      (fun R σ i => f R σ (x i)) atTop (fun ω i => g ω (x i))
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
    intro m x
    exact hfdd m (fun i => (x i).1.1) (fun i => (x i).1.2)
      (fun i => (hKT (x i).property).1)
  have hgm : ∀ q : K, AEMeasurable (fun ω => g ω q) PW := by
    intro q
    exact (measurable_pi_apply (0 : Fin 1)).comp_aemeasurable
      (hfd 1 (fun _ => q)).aemeasurable_limit
  have hgc : ∀ᵐ ω ∂PW, Continuous (g ω) := by
    filter_upwards [hcont] with ω hω
    exact hω.comp continuous_subtype_val
  have heq : ∀ a b : ℝ, 0 < a → 0 < b → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ R : ℝ in atTop,
      (Sandpile.centeredMassLaw d ν)
        {σ | ∃ x y : K, dist x y < ρ ∧ b < |f R σ x - f R σ y|} ≤ ENNReal.ofReal a := by
    intro a b ha hb
    obtain ⟨ρ, hρ, hr⟩ := (htight K hK hKT).2 a b ha hb
    refine ⟨ρ, hρ, (eventually_ge_atTop (1 : ℝ)).mono fun R hR => ?_⟩
    apply le_trans (measure_mono ?_) (hr R hR)
    rintro σ ⟨x, y, hxy, hv⟩
    exact ⟨x.1, x.property, y.1, y.property, hxy, hv⟩
  have h := Sandpile.Continuum.exists_field_coupling_on_compact
    (fun _ : ℝ => Sandpile.centeredMassLaw d ν) PW f g hgm hgc atTop hfd heq ε δ hε hδ
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 h
  refine ⟨max 1 R₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hR₀ R ((le_max_right _ _).trans hR)
  refine ⟨P, hP, hPf, hPs, ?_⟩
  have he : {p : (Sandpile.Site d → ℝ) × ΩW | ∃ q ∈ K,
      ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
        (Sandpile.scenery d p.1) q.1 q.2 -
        Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1 q.2 p.2|} =
      {p | ∃ q : K, ε < |f R p.1 q - g p.2 q|} := by
    ext p
    simp only [mem_setOf_eq, Subtype.exists, f, g]
    constructor <;> rintro ⟨q, hq, hv⟩ <;> exact ⟨q, hq, hv⟩
  rw [he]
  exact hbad
