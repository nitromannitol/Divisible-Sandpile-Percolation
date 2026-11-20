import Sandpile.Support.BrownianStoppingConcatenation
import Sandpile.Support.PathStoppingApproximation
import Sandpile.Support.StoppingTimeSelection
import Sandpile.Support.D23CubeValueRegularity

/-!
# Selecting Brownian continuation rules

A countable selection of bounded path rules based on the information at a
deterministic time gives a bounded stopping time after that time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- Selecting a continuation rule using the past at a deterministic time gives
an admissible stopping time of the original process. -/
theorem Sandpile.Support.isBrownianStopping_select_continuation
    {Ω ι : Type*} {d : ℕ} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (s H : ℝ≥0)
    (k : Ω → ι) (hk : Measurable[Sandpile.Continuum.brownianFiltration B s] k)
    (y : ι → Sandpile.Continuum.Space d)
    (θ : ι → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : ∀ i, IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ i p : ℝ≥0∞)))
    (hθH : ∀ i p, θ i p ≤ H) :
    let σ : Ω → ℝ≥0 := fun ω => s + θ (k ω) (fun t => y (k ω) + (B (s + t) ω - B s ω))
    Sandpile.Continuum.IsBrownianStopping B σ ∧ ∀ ω, s ≤ σ ω ∧ σ ω ≤ s + H := by
  let W : ℝ≥0 → Ω → Sandpile.Continuum.Space d := fun t ω => B (s + t) ω - B s ω
  let η : ι → Ω → ℝ≥0 := fun i ω => θ i (fun t => y i + W t ω)
  let ρ : ι → Ω → ℝ≥0 := fun i ω => s + η i ω
  have hη : ∀ i, Sandpile.Continuum.IsBrownianStopping W (η i) := by
    intro i
    apply (Sandpile.Support.isBrownianStopping_add_const (y i) W (η i)).mp
    exact Sandpile.Support.isBrownianStopping_path_comp (fun t ω => y i + W t ω) (θ i) (hθ i)
  have hρ : ∀ i, Sandpile.Continuum.IsBrownianStopping B (ρ i) := fun i =>
    Sandpile.Continuum.isBrownianStopping_add_shift B s (η i) (hη i)
  have hρlo : ∀ i ω, s ≤ ρ i ω := fun i ω => le_add_right (le_refl s)
  have hρhi : ∀ i ω, ρ i ω ≤ s + H := fun i ω => add_le_add_right (hθH i _) s
  have hsel := Sandpile.Support.isStoppingTime_countable_selection
    (Sandpile.Continuum.brownianFiltration B) s k hk ρ hρ hρlo
  exact ⟨hsel, fun ω => ⟨hρlo (k ω) ω, hρhi (k ω) ω⟩⟩

/-- A countable selection of bounded continuation rules at different restart
times is a Brownian stopping time if each selection event is known at its
restart time. -/
theorem Sandpile.Support.isBrownianStopping_select_continuation_of_times
    {Ω ι : Type*} {d : ℕ} [Countable ι]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (s H : ι → ℝ≥0)
    (k : Ω → ι)
    (hk : ∀ i, MeasurableSet[Sandpile.Continuum.brownianFiltration B (s i)] {ω | k ω = i})
    (y : ι → Sandpile.Continuum.Space d)
    (θ : ι → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : ∀ i, IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable))
      (fun p => (θ i p : ℝ≥0∞)))
    (hθH : ∀ i p, θ i p ≤ H i) (T : ℝ≥0) (hT : ∀ i, s i + H i ≤ T) :
    let σ : Ω → ℝ≥0 := fun ω => s (k ω) + θ (k ω)
      (fun t => y (k ω) + (B (s (k ω) + t) ω - B (s (k ω)) ω))
    Sandpile.Continuum.IsBrownianStopping B σ ∧ ∀ ω, s (k ω) ≤ σ ω ∧ σ ω ≤ T := by
  let W : ι → ℝ≥0 → Ω → Sandpile.Continuum.Space d :=
    fun i t ω => B (s i + t) ω - B (s i) ω
  let η : ι → Ω → ℝ≥0 := fun i ω => θ i (fun t => y i + W i t ω)
  let ρ : ι → Ω → ℝ≥0 := fun i ω => s i + η i ω
  have hη : ∀ i, Sandpile.Continuum.IsBrownianStopping (W i) (η i) := by
    intro i
    apply (Sandpile.Support.isBrownianStopping_add_const (y i) (W i) (η i)).mp
    exact Sandpile.Support.isBrownianStopping_path_comp
      (fun t ω => y i + W i t ω) (θ i) (hθ i)
  have hρ : ∀ i, Sandpile.Continuum.IsBrownianStopping B (ρ i) := fun i =>
    Sandpile.Continuum.isBrownianStopping_add_shift B (s i) (η i) (hη i)
  have hρlo : ∀ i ω, s i ≤ ρ i ω := fun i ω => le_add_right (le_refl (s i))
  have hρhi : ∀ i ω, ρ i ω ≤ T := fun i ω =>
    (add_le_add_right (hθH i _) (s i)).trans (hT i)
  have hsel := Sandpile.Support.isStoppingTime_countable_selection_of_lower_bounds
    (Sandpile.Continuum.brownianFiltration B) s k hk ρ hρ hρlo
  exact ⟨hsel, fun ω => ⟨hρlo (k ω) ω, hρhi (k ω) ω⟩⟩
