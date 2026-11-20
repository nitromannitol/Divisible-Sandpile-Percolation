import LatticeProb.Prob.StoppingDyadic

/-!
# Bounded dyadic approximations of stopping times

A stopping time bounded by a finite horizon is the pointwise limit of finitely
valued stopping times obtained by rounding upwards and clipping at the horizon.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Rounding a bounded stopping time upwards and clipping at its horizon gives
finitely valued stopping times that converge pointwise from above. -/
theorem Sandpile.Support.exists_finite_stoppingTime_approximation
    {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕 fun ω => (τ ω : ℝ≥0∞))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ σ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : ℝ≥0∞)) ∧
      (∀ n, (Set.range (σ n)).Finite) ∧
      (∀ n ω, τ ω ≤ σ n ω ∧ σ n ω ≤ T) ∧
      ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (LatticeProb.dyUp n (τ ω)) T
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · intro n
    have h : IsStoppingTime 𝓕 fun ω =>
        min ((LatticeProb.dyUp n (τ ω) : ℝ≥0) : WithTop ℝ≥0) (T : WithTop ℝ≥0) :=
      (LatticeProb.isStoppingTime_dyUp hτ n).min_const T
    rw [show (fun ω => min ((LatticeProb.dyUp n (τ ω) : ℝ≥0) : WithTop ℝ≥0)
      (T : WithTop ℝ≥0)) = (fun ω => ((σ n ω : ℝ≥0) : WithTop ℝ≥0)) from
      funext fun ω => (WithTop.coe_min _ _).symm] at h
    exact h
  · intro n
    refine ((Set.finite_Iic ⌈(2 ^ n : ℝ≥0) * T⌉₊).image fun j : ℕ =>
      min ((j : ℝ≥0) / 2 ^ n) T).subset ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨⌈(2 ^ n : ℝ≥0) * τ ω⌉₊,
      Nat.ceil_mono (mul_le_mul_of_nonneg_left (hτT ω) (by positivity)), rfl⟩
  · intro n ω
    exact ⟨le_min (LatticeProb.le_dyUp n _) (hτT ω), min_le_right _ _⟩
  · intro ω
    have h := (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
    rw [min_eq_left (hτT ω)] at h
    exact h
