import Sandpile.Support.D4OmegaEmbedCovariance
import LatticeProb.Prob.CountableMeasurable

/-!
# Measurability and moments of centered membrane embeddings

The random embedded membrane is jointly measurable, square-integrable at each
spatial point, and centered. These facts support its Fourier energy estimates.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- Joint measurability of a centered embedding follows from measurability of
all lattice values. -/
theorem measurable_omegaEmbed_field {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (R L : ℝ) (w : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (X : Site d → Ω → ℝ)
    (hX : ∀ x, Measurable (X x)) :
    Measurable (fun p : Ω × Space d => omegaEmbed R w (fun x => X x p.1) p.2) := by
  simp_rw [omegaEmbed_eq_sub_cellMass R L w hw hL]
  have hcoord : Measurable (fun p : Ω × Space d => (fun i => ⌊R * p.2 i⌋ : Site d)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_coord R i).comp measurable_snd
  have hfield : Measurable (fun p : Ω × Space d => X (fun i => ⌊R * p.2 i⌋) p.1) :=
    LatticeProb.measurable_eval_var _ hcoord (fun p x => X x p.1)
      (fun x => (hX x).comp measurable_fst)
  exact hfield.sub (Finset.measurable_sum _ fun a _ =>
    ((hX a).comp measurable_fst).const_mul (cellMass R w a))

/-- Every spatial section of a centered embedding is square-integrable. -/
theorem memLp_two_omegaEmbed_field {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (R L : ℝ) (w : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (X : Site d → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P) (z : Space d) :
    MemLp (fun ω => omegaEmbed R w (fun x => X x ω) z) 2 P := by
  simp_rw [omegaEmbed_eq_sub_cellMass R L w hw hL]
  exact (hX _).sub (memLp_finsetSum _ fun a _ => (hX a).const_mul _)

/-- Centering in space preserves the zero mean of each lattice value. -/
theorem integral_omegaEmbed_field {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (R L : ℝ) (w : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (X : Site d → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P) (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (z : Space d) : ∫ ω, omegaEmbed R w (fun x => X x ω) z ∂P = 0 := by
  simp_rw [omegaEmbed_eq_sub_cellMass R L w hw hL]
  have hi : Integrable (fun ω => ∑ a ∈ supportBox d R L, cellMass R w a * X a ω) P :=
    (memLp_finsetSum _ fun a _ => (hX a).const_mul _).integrable (by norm_num)
  rw [integral_sub ((hX _).integrable (by norm_num)) hi, hmean]
  simp_rw [integral_finsetSum _ (fun a _ => ((hX a).const_mul _).integrable (by norm_num)),
    integral_const_mul, hmean, mul_zero, Finset.sum_const_zero, sub_zero]

/-- On a bounded support, the second moments of a centered embedding admit a
finite bound for each fixed mesh and random field. -/
theorem exists_second_moment_bound_omegaEmbed {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (R L H : ℝ) (w φ : Space d → ℝ) (hw : Integrable w)
    (hL : ∀ z, w z ≠ 0 → ‖z‖ ≤ L) (hH : ∀ z, φ z ≠ 0 → ‖z‖ ≤ H)
    (X : Site d → Ω → ℝ) :
    ∃ B : ℝ, ∀ z, φ z ≠ 0 →
      ∫ ω, (omegaEmbed R w (fun x => X x ω) z) ^ 2 ∂P ≤ B := by
  let Y : Site d → Ω → ℝ := fun x ω =>
    X x ω - ∑ a ∈ supportBox d R L, cellMass R w a * X a ω
  refine ⟨∑ x ∈ supportBox d R H, |∫ ω, Y x ω ^ 2 ∂P|, ?_⟩
  intro z hz
  have hin : (fun i => ⌊R * z i⌋ : Site d) ∈ supportBox d R H :=
    floor_mem_boxFinset R z (hH z hz)
  have heq (ω : Ω) : omegaEmbed R w (fun x => X x ω) z =
      Y (fun i => ⌊R * z i⌋) ω := omegaEmbed_eq_sub_cellMass R L w hw hL _ z
  simp_rw [heq]
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x : Site d => |∫ ω, Y x ω ^ 2 ∂P|)
    (fun x _ => abs_nonneg _) hin)

end Sandpile.Support
