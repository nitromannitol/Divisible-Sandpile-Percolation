import Sandpile.Support.MeanAValue
import Sandpile.Support.ExplBallLocal

/-! # Vanishing of the field at time zero

The field vanishes at time zero, and the value dominates the field.

`eq:dlt4-linear-gaussian-potential` (`sandpile.tex:1014-1021`) reads
`Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))`, and the finite-time Green kernel
`g_0^{BM}(x,·)` is the integral of the heat kernel over an empty time interval,
hence the zero function; white noise is linear, so `Z(0,x) = 0` almost surely at
each `x`.  A modification that is almost surely continuous on `[0,T] × ℝ^d`
therefore vanishes at time zero at EVERY point simultaneously, almost surely:
the exceptional set is the union of the countably many exceptional sets of a
dense sequence of points.

That is what makes the stopping rule `τ ≡ T` of
`eq:continuum-membrane-stopping-value` pay exactly `Z(T,x)`, so that

  `𝒰_Z(T,x) = Z(T,x) + sup_{τ≤T} E_x[-Z(T-τ,B_τ)] ≥ Z(T,x)`,

which is the first of the two inequalities of `sandpile.tex:2024-2026`
("`𝒰(1,0) ≥ max{Z(1,0),0}`") and the one that carries the nondegeneracy of the
limiting variance.  No bound on the attainable payoffs is needed for it: a
supremum of a set containing `0` is nonnegative whether or not the set is
bounded above, since an unbounded set of reals has supremum `0` in this
convention as well.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The finite-time Green kernel at time zero is the zero function. -/
theorem greenTimeBM_zero_time (d : ℕ) (x : Space d) :
    (fun y => greenTimeBM d 0 x y) = (fun _ => (0 : ℝ)) := by
  funext y
  unfold greenTimeBM
  exact intervalIntegral.integral_same

/-- White noise vanishes at the zero test function. -/
theorem whiteNoise_zero {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    W (fun _ => (0 : ℝ)) =ᵐ[PW] fun _ => (0 : ℝ) := by
  have hmem : MemLp (fun _ : Space d => (0 : ℝ)) 2 (volume : Measure (Space d)) :=
    MemLp.zero
  have h := hW.smul (0 : ℝ) (fun _ : Space d => (0 : ℝ)) hmem
  have hfun : ((0 : ℝ) • fun _ : Space d => (0 : ℝ)) = fun _ : Space d => (0 : ℝ) := by
    funext y; simp
  rw [hfun] at h
  filter_upwards [h] with ω hω
  rw [hω]
  ring

/-- The Gaussian heat potential vanishes at time zero, almost surely at each point. -/
theorem gaussianPotential_zero_time {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (x : Space d) :
    (fun ω => gaussianPotential d ν2 W 0 x ω) =ᵐ[PW] fun _ => (0 : ℝ) := by
  filter_upwards [whiteNoise_zero PW W hW] with ω hω
  unfold gaussianPotential
  rw [greenTimeBM_zero_time d x, hω]
  ring

/-- **The continuous modification vanishes at time zero at every point, almost
surely.**  The exceptional set is the union of those of a dense sequence. -/
theorem ae_forall_field_zero_time {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) (ν2 : ℝ)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) :
    ∀ᵐ ω ∂PW, ∀ y : Space d, Z 0 y ω = 0 := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Space d)
  have hpt : ∀ n : ℕ, ∀ᵐ ω ∂PW, Z 0 (u n) ω = 0 := by
    intro n
    filter_upwards [hZmod 0 (u n), gaussianPotential_zero_time PW W hW ν2 (u n)] with ω h1 h2
    rw [h1, h2]
  have hall : ∀ᵐ ω ∂PW, ∀ n : ℕ, Z 0 (u n) ω = 0 := ae_all_iff.2 hpt
  filter_upwards [hall, hZcont 1 one_pos] with ω hzero hcont
  have hc : Continuous fun y : Space d => Z 0 y ω := by
    have hmaps : ∀ y : Space d, ((0 : ℝ), y) ∈
        Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Space d)) := by
      intro y
      exact ⟨Set.mem_Icc.2 ⟨le_rfl, zero_le_one⟩, Set.mem_univ y⟩
    exact hcont.comp_continuous (by fun_prop) hmaps
  have heq : (fun y : Space d => Z 0 y ω) = fun _ => (0 : ℝ) := by
    refine hc.ext_on hu continuous_const ?_
    rintro y ⟨n, rfl⟩
    exact hzero n
  intro y
  exact congrFun heq y

/-- A supremum of a set of reals containing `0` is nonnegative, bounded or not. -/
theorem zero_le_sSup_of_mem (S : Set ℝ) (h : (0 : ℝ) ∈ S) : 0 ≤ sSup S := by
  by_cases hb : BddAbove S
  · exact le_csSup hb h
  · rw [Real.sSup_of_not_bddAbove hb]

/-- **The stopping rule `τ ≡ T` pays nothing** when the field vanishes at time
zero, so the discount is nonnegative. -/
theorem zero_le_brownianDiscount_of_zero_time {ΩB : Type*} [MeasurableSpace ΩB]
    (PB : Measure ΩB) (B : ℝ≥0 → ΩB → Space d) (h : ℝ → Space d → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (hzero : ∀ y : Space d, h 0 y = 0) :
    0 ≤ brownianDiscount B PB h T := by
  refine zero_le_sSup_of_mem _ ?_
  refine ⟨fun _ => T.toNNReal, isBrownianStopping_const B _, ?_, ?_⟩
  · intro ω
    rw [Real.coe_toNNReal T hT]
  · have hrw : ∀ ω : ΩB, -h (T - ((T.toNNReal : ℝ≥0) : ℝ)) (B T.toNNReal ω) = 0 := by
      intro ω
      rw [Real.coe_toNNReal T hT, sub_self, hzero]
      ring
    simp only [hrw]
    rw [integral_zero]

/-- **The value dominates the field**: `𝒰_Z(T,x) ≥ Z(T,x)`, almost surely. -/
theorem ae_field_le_continuumValue {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (PW : Measure ΩW) (PB : Measure ΩB)
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) (ν2 : ℝ)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d) (T : ℝ) (hT : 0 ≤ T) (x : Space d) :
    ∀ᵐ ω ∂PW, Z T x ω ≤ continuumValue d Z B PB T x ω := by
  filter_upwards [ae_forall_field_zero_time PW W hW ν2 Z hZmod hZcont] with ω hω
  have hd0 := zero_le_brownianDiscount_of_zero_time PB (B x) (fun t z => Z t z ω) T hT hω
  unfold continuumValue brownianValue
  linarith

end Sandpile.Support
