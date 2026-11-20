import Sandpile.Support.NearOptimalPathStopping
import Sandpile.Support.StoppedRewardSpatialContinuity
import Sandpile.Support.BrownianValueContinuity

/-!
# Finite near-optimal families

A compact set of starting points admits finitely many bounded path rules such
that one of the rules is near-optimal at every point of the set.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Finitely many bounded raw path rules suffice to approximate the stopping
value uniformly on a compact set of starting points. -/
theorem Sandpile.Support.exists_finite_near_optimal_path_rules
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d 0 B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset (Sandpile.Continuum.Space d))
      (θ : Sandpile.Continuum.Space d → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0),
      (∀ z, IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable))
        (fun p => (θ z p : ℝ≥0∞))) ∧
      (∀ z p, θ z p ≤ T) ∧
      ∀ y ∈ K, ∃ z ∈ S,
        Sandpile.External.Snell.snellValue (fun t ω => y + B t ω) P G T - ε <
          ∫ ω, G ((T : ℝ) - θ z (fun t => z + B t ω))
            (y + B (θ z (fun t => z + B t ω)) ω) ∂P := by
  classical
  let C : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d :=
    fun y t ω => y + B t ω
  have hC : ∀ y, Sandpile.Continuum.IsBrownian d y (C y) P := fun y =>
    Sandpile.Support.isBrownian_add_const d P B hB y
  have hCm : ∀ y t, StronglyMeasurable (C y t) := fun y t =>
    (measurable_const.add (hBm t).measurable).stronglyMeasurable
  have hCc : ∀ y ω, Continuous fun t => C y t ω := fun y ω => continuous_const.add (hBc ω)
  let V : Sandpile.Continuum.Space d → ℝ := fun y =>
    Sandpile.External.Snell.snellValue (C y) P G T
  have hVc : Continuous V := by
    have h := Sandpile.Support.continuousOn_brownian_snellValue P C hC hCm hCc T G hG hgrow
    have h' := h.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y : Sandpile.Continuum.Space d =>
        (show ((0 : ℝ≥0), y) ∈ Set.Icc (0 : ℝ≥0) T ×ˢ Set.univ from
          ⟨⟨le_rfl, zero_le⟩, Set.mem_univ y⟩))
    simpa only [Function.comp_def, Prod.fst, Prod.snd, id_eq, NNReal.coe_zero, sub_zero, V] using h'
  have hex : ∀ z : Sandpile.Continuum.Space d,
      ∃ θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0,
        IsStoppingTime (LatticeProb.natFiltration
          (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
          (fun t => (measurable_pi_apply t).stronglyMeasurable))
          (fun p => (θ p : ℝ≥0∞)) ∧ (∀ p, θ p ≤ T) ∧
        V z - ε / 2 < ∫ ω, G ((T : ℝ) - θ (fun t => C z t ω))
          (C z (θ (fun t => C z t ω)) ω) ∂P := fun z =>
    Sandpile.Support.exists_near_optimal_raw_path_stoppingTime z P (C z) (hC z)
      (hCm z) (hCc z) T G hG hgrow (ε / 2) (half_pos hε)
  choose θ hθ hθT hθnear using hex
  let ρ : Sandpile.Continuum.Space d → Ω → ℝ≥0 := fun z ω => θ z (fun t => z + B t ω)
  have hρ : ∀ z, Sandpile.Continuum.IsBrownianStopping B (ρ z) := by
    intro z
    apply (Sandpile.Support.isBrownianStopping_add_const z B (ρ z)).mp
    exact Sandpile.Support.isBrownianStopping_path_comp (C z) (θ z) (hθ z)
  have hρT : ∀ z ω, ρ z ω ≤ T := fun z ω => hθT z _
  let F : Sandpile.Continuum.Space d → Sandpile.Continuum.Space d → ℝ := fun z y =>
    ∫ ω, G ((T : ℝ) - ρ z ω) (y + B (ρ z ω) ω) ∂P
  have hFc : ∀ z, Continuous (F z) := fun z =>
    Sandpile.Support.continuous_integral_translated_stopping_payoff 0 P B hB hBm hBc
      T G hG hgrow (ρ z) (hρ z) (hρT z)
  let U : Sandpile.Continuum.Space d → Set (Sandpile.Continuum.Space d) :=
    fun z => {y | V y - ε < F z y}
  have hUopen : ∀ z, IsOpen (U z) := fun z =>
    isOpen_lt (hVc.sub continuous_const) (hFc z)
  have hself : ∀ z, z ∈ U z := by
    intro z
    have hnear := hθnear z
    change V z - ε / 2 < F z z at hnear
    change V z - ε < F z z
    linarith
  have hcover : K ⊆ ⋃ z, U z := fun y hy => Set.mem_iUnion.2 ⟨y, hself y⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hUopen hcover
  refine ⟨S, θ, hθ, hθT, ?_⟩
  intro y hy
  obtain ⟨z, hz⟩ := Set.mem_iUnion.1 (hS hy)
  obtain ⟨hzS, hzy⟩ := Set.mem_iUnion.1 hz
  exact ⟨z, hzS, hzy⟩
