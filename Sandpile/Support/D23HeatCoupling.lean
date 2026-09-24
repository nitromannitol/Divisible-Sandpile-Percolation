/-
Coupling the heat potentials along a sequence of scenery laws. Uniform
exponential moments supply compact equicontinuity; the remaining input is
finite-dimensional convergence for the same sequence (`sandpile.tex:1950-1955`).
-/
import Sandpile.Support.KillFieldCoupling
import Sandpile.Support.D23UniformTightness

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Continuum

/-- Sequence-indexed compact coupling, with the original varying scenery
law as the first marginal. -/
theorem heat_field_coupling_seq_of_fdd
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (ν n))
    (hK₀ : ∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(ν n) ≤ K₀)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (Z : ΩW → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d => Z ω q.1 q.2)
    (T : ℝ) (hT : 0 < T)
    (hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun n (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
          Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n)
            (Sandpile.scenery d σ) (r i) (w i)) atTop
        (fun ω i => Z ω (r i) (w i))
        (fun n => Sandpile.centeredMassLaw d (ν n)) PW)
    (K : Set (ℝ × Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (hKT : K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
      P.map Prod.fst = Sandpile.centeredMassLaw d (ν n) ∧ P.map Prod.snd = PW ∧
      P {p | ∃ q ∈ K, ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n)
          (Sandpile.scenery d p.1) q.1 q.2 - Z p.2 q.1 q.2|} ≤ ENNReal.ofReal δ := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : ℕ → (Sandpile.Site d → ℝ) → K → ℝ := fun n σ q =>
    Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n) (Sandpile.scenery d σ) q.1.1 q.1.2
  let g : ΩW → K → ℝ := fun ω q =>
    Z ω q.1.1 q.1.2
  have hfd : ∀ (m : ℕ) (x : Fin m → K), TendstoInDistribution
      (fun n σ i => f n σ (x i)) atTop (fun ω i => g ω (x i))
      (fun n => Sandpile.centeredMassLaw d (ν n)) PW := by
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
  have heq : ∀ a b : ℝ, 0 < a → 0 < b → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n : ℕ in atTop,
      (Sandpile.centeredMassLaw d (ν n))
        {σ | ∃ x y : K, dist x y < ρ ∧ b < |f n σ x - f n σ y|} ≤ ENNReal.ofReal a := by
    intro a b ha hb
    obtain ⟨ρ, hρ, hr⟩ := (Sandpile.Support.heat_potential_tightness_uniform_of_exp_bound
      hd hd3 θ₀ K₀ hθ₀ T hT K hK hKT).2 a b ha hb
    refine ⟨ρ, hρ, (hR.eventually (eventually_ge_atTop (1 : ℝ))).mono fun n hn => ?_⟩
    apply le_trans (measure_mono ?_) (hr (ν n) inferInstance (hmean n) (hexp n) (hK₀ n) (R n) hn)
    rintro σ ⟨x, y, hxy, hv⟩
    exact ⟨x.1, x.property, y.1, y.property, hxy, hv⟩
  have h := Sandpile.Continuum.exists_field_coupling_on_compact
    (fun n : ℕ => Sandpile.centeredMassLaw d (ν n)) PW f g hgm hgc atTop hfd heq ε δ hε hδ
  filter_upwards [h] with n hn
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hn
  refine ⟨P, hP, hPf, hPs, ?_⟩
  have he : {p : (Sandpile.Site d → ℝ) × ΩW | ∃ q ∈ K,
      ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n)
        (Sandpile.scenery d p.1) q.1 q.2 -
        Z p.2 q.1 q.2|} =
      {p | ∃ q : K, ε < |f n p.1 q - g p.2 q|} := by
    ext p
    simp only [mem_setOf_eq, Subtype.exists, f, g]
    constructor <;> rintro ⟨q, hq, hv⟩ <;> exact ⟨q, hq, hv⟩
  rw [he]
  exact hbad

end Sandpile.Continuum
