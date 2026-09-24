/-
The rank-one reduction is a contraction for the `\ell^2` distance.

`sandpile.tex:5270-5271` says that conditioning the Gaussian scenery on `-V_\infty(0)`
"replaces its covariance by a rank-one reduction, so the same bound holds
conditionally".  The reduction is `\delta\mapsto\delta-\langle e,\delta\rangle e` for the
unit vector `e=G(0,\cdot)/\|G(0,\cdot)\|`, and what makes the concentration bound survive
it is Pythagoras: the reduction decreases the squared `\ell^2` norm by exactly
`\langle e,\delta\rangle^2`.  The three lemmas here are that identity in the form the
conditioning uses it, where a square-summable family is given by a `HasSum` and not by a
membership in `lp`.
-/
import Sandpile.Support.Dgt4ACondTail

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

/-- A family with a summable square lies in `lp 2`. -/
theorem memLp_two_of_hasSum_sq {ι : Type*} (δ : ι → ℝ) (M : ℝ)
    (h : HasSum (fun i => δ i ^ 2) M) : Memℓp δ 2 := by
  refine (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).2 ?_
  refine h.summable.congr fun i => ?_
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs, sq_abs]

/-- The squares of the coordinates of an `lp 2` family sum to the squared norm. -/
theorem hasSum_sq_coeFn_lp {ι : Type*} (f : lp (fun _ : ι => ℝ) 2) :
    HasSum (fun i => ((f : ι → ℝ) i) ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) f
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at h
  simp only [Real.rpow_natCast] at h
  have heq : ∀ i : ι, ‖(f : ι → ℝ) i‖ ^ (2 : ℕ) = ((f : ι → ℝ) i) ^ 2 := fun i => by
    rw [Real.norm_eq_abs, sq_abs]
  simpa only [heq] using h

/-- **The rank-one reduction is a contraction** (`sandpile.tex:5265-5266`): removing the
component along a unit vector decreases the squared `\ell^2` norm by the square of the
coefficient. -/
theorem hasSum_sq_sub_smul {ι : Type*} (e : lp (fun _ : ι => ℝ) 2) (he : ‖e‖ = 1)
    (δ : ι → ℝ) (M : ℝ) (h : HasSum (fun i => δ i ^ 2) M) :
    ∃ c : ℝ, HasSum (fun i => (e : ι → ℝ) i * δ i) c ∧
      HasSum (fun i => (δ i - c * (e : ι → ℝ) i) ^ 2) (M - c ^ 2) := by
  have hδ : Memℓp δ 2 := memLp_two_of_hasSum_sq δ M h
  set g : lp (fun _ : ι => ℝ) 2 := ⟨δ, hδ⟩ with hgdef
  have hgc : ((g : lp (fun _ : ι => ℝ) 2) : ι → ℝ) = δ := rfl
  have hM : ‖g‖ ^ 2 = M := by
    refine HasSum.unique ?_ h
    have hsq := hasSum_sq_coeFn_lp g
    rwa [hgc] at hsq
  refine ⟨(inner ℝ e g : ℝ), ?_, ?_⟩
  · have hi := lp.hasSum_inner (𝕜 := ℝ) e g
    simpa [RCLike.inner_apply, conj_trivial, hgc, mul_comm] using hi
  · have hnorm : ‖g - (inner ℝ e g : ℝ) • e‖ ^ 2 = M - (inner ℝ e g : ℝ) ^ 2 := by
      have hexp : ‖g - (inner ℝ e g : ℝ) • e‖ ^ 2
          = ‖g‖ ^ 2 - 2 * (inner ℝ g ((inner ℝ e g : ℝ) • e) : ℝ)
            + ‖(inner ℝ e g : ℝ) • e‖ ^ 2 :=
        norm_sub_sq_real g ((inner ℝ e g : ℝ) • e)
      have h1 : (inner ℝ g ((inner ℝ e g : ℝ) • e) : ℝ) = (inner ℝ e g : ℝ) ^ 2 := by
        rw [real_inner_smul_right, real_inner_comm]
        ring
      have h2 : ‖(inner ℝ e g : ℝ) • e‖ ^ 2 = (inner ℝ e g : ℝ) ^ 2 := by
        rw [norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]
      rw [hexp, h1, h2, hM]
      ring
    have hs := hasSum_sq_coeFn_lp (g - (inner ℝ e g : ℝ) • e)
    rw [hnorm] at hs
    refine hs.congr_fun ?_
    intro i
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hgc]

end Sandpile
