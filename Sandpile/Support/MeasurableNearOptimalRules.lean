import Sandpile.Support.FiniteNearOptimalRules
import Sandpile.Support.FiniteMeasurableSelection

/-!
# Measurable selection of near-optimal rules

On a compact set, one can choose among finitely many near-optimal raw path
rules by a bounded measurable label.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A finite family of near-optimal path rules on a compact set admits a
measurable finite-valued selector. -/
theorem Sandpile.Support.exists_measurable_near_optimal_path_rules
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
    ∃ (N : ℕ) (c : ℕ → Sandpile.Continuum.Space d)
      (k : Sandpile.Continuum.Space d → ℕ)
      (θ : ℕ → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0),
      Measurable k ∧ (∀ y, k y ≤ N) ∧
      (∀ n, IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable))
        (fun p => (θ n p : ℝ≥0∞))) ∧
      (∀ n p, θ n p ≤ T) ∧
      ∀ y ∈ K,
        Sandpile.External.Snell.snellValue (fun t ω => y + B t ω) P G T - ε <
          ∫ ω, G ((T : ℝ) - θ (k y) (fun t => c (k y) + B t ω))
            (y + B (θ (k y) (fun t => c (k y) + B t ω)) ω) ∂P := by
  classical
  obtain ⟨S, θ, hθ, hθT, hnear⟩ :=
    Sandpile.Support.exists_finite_near_optimal_path_rules P B hB hBm hBc T G hG hgrow K hK ε hε
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
  have hUm : ∀ z, MeasurableSet (U z) := fun z =>
    (isOpen_lt (hVc.sub continuous_const) (hFc z)).measurableSet
  have hcover : ∀ y ∈ K, ∃ z ∈ S, y ∈ U z := hnear
  obtain ⟨N, c, k, hkm, hkN, hk⟩ :=
    Sandpile.Support.exists_measurable_finite_cover_selector K S 0 U hUm hcover
  refine ⟨N, c, k, (fun n => θ (c n)), hkm, hkN, (fun n => hθ (c n)),
    (fun n => hθT (c n)), ?_⟩
  intro y hy
  exact (hk y hy).2.2
