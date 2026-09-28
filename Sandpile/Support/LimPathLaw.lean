import Sandpile.Continuum.Stopping
import Sandpile.Support.ExplBallExit
import LatticeProb.Prob.BrownianPathLaw

/-!
# The law of a centred Brownian path is base-point- and space-independent

The law of the centred path of a Brownian motion does not depend on the starting
point, nor on the space the motion is built on.

The library proves this for the increments after a time `t₀` of ONE motion
(`LatticeProb.IsBrownianSpace.map_shift_eq`).  What the crossing argument needs is
the same statement for two motions, possibly on two different spaces and started at
two different points: the paths `t ↦ B_t − B_0` and `t ↦ B'_t − B'_0` have the same
law on `ℝ≥0 → ℝ^d`.  The proof is the library's: the coordinates of a motion are
independent, so the law of the vector of coordinate paths is the product of the
coordinate path laws, and each coordinate path is a pre-Brownian motion, whose law on
path space is determined by its finite dimensional distributions
(`LatticeProb.map_path_eq_of_isPreBrownianReal`).  The rescaling by `√d` that turns a
coordinate of the motion into a standard pre-Brownian motion is undone by a
measurable map on path space.

This module mentions nothing of this repository: it belongs in the shared library and
is recorded as generic, to migrate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- **The law of the centred path is the same for two Brownian motions**, whatever their
starting points and whatever the spaces they are built on. -/
theorem map_centredPath_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {x x' : Space d} {B : ℝ≥0 → Ω → Space d} {B' : ℝ≥0 → Ω' → Space d}
    (hB : IsBrownian d x B P) (hB' : IsBrownian d x' B' Q)
    (hm : ∀ t, Measurable (B t)) (hm' : ∀ t, Measurable (B' t)) :
    P.map (fun ω (t : ℝ≥0) => B t ω - B 0 ω)
      = Q.map (fun ω (t : ℝ≥0) => B' t ω - B' 0 ω) := by
  set c : ℝ := Real.sqrt d with hc
  have hsp : LatticeProb.IsBrownianSpace d x B P := isBrownianSpace_of_isBrownian hB
  have hsp' : LatticeProb.IsBrownianSpace d x' B' Q := isBrownianSpace_of_isBrownian hB'
  have hev : ∀ i : Fin d, Measurable fun v : Space d => v i := fun i => by fun_prop
  have hcoord : ∀ (t : ℝ≥0) (i : Fin d), Measurable fun ω => B t ω i :=
    fun t i => (hev i).comp (hm t)
  have hcoord' : ∀ (t : ℝ≥0) (i : Fin d), Measurable fun ω => B' t ω i :=
    fun t i => (hev i).comp (hm' t)
  have hmT : Measurable (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B t ω i - B 0 ω i))) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun t => ?_
    exact ((hcoord t i).sub (hcoord 0 i)).const_mul c
  have hmT' : Measurable (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B' t ω i - B' 0 ω i))) := by
    refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun t => ?_
    exact ((hcoord' t i).sub (hcoord' 0 i)).const_mul c
  -- independence of the coordinate paths
  have hindep : iIndepFun (fun (i : Fin d) ω => (fun t : ℝ≥0 => c * (B t ω i - B 0 ω i))) P := by
    have h := (hsp.shift 0).indep
    have h2 := h.comp (fun _ (g : ℝ≥0 → ℝ) => fun t : ℝ≥0 => c * g t)
      (fun _ => measurable_pi_lambda _ fun t =>
        ((measurable_pi_apply t : Measurable fun g : ℝ≥0 → ℝ => g t)).const_mul c)
    refine h2.congr ?_
    intro i
    filter_upwards with ω
    funext t
    simp only [Function.comp_apply, PiLp.sub_apply, zero_add]
  have hindep' : iIndepFun (fun (i : Fin d) ω => (fun t : ℝ≥0 => c * (B' t ω i - B' 0 ω i))) Q := by
    have h := (hsp'.shift 0).indep
    have h2 := h.comp (fun _ (g : ℝ≥0 → ℝ) => fun t : ℝ≥0 => c * g t)
      (fun _ => measurable_pi_lambda _ fun t =>
        ((measurable_pi_apply t : Measurable fun g : ℝ≥0 → ℝ => g t)).const_mul c)
    refine h2.congr ?_
    intro i
    filter_upwards with ω
    funext t
    simp only [Function.comp_apply, PiLp.sub_apply, zero_add]
  have hpi : P.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B t ω i - B 0 ω i)))
      = Measure.pi (fun i : Fin d => P.map (fun ω (t : ℝ≥0) => c * (B t ω i - B 0 ω i))) :=
    hindep.map_fun_eq_pi_map (fun i => (measurable_pi_lambda _ fun t =>
      ((hcoord t i).sub (hcoord 0 i)).const_mul c).aemeasurable)
  have hpi' : Q.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B' t ω i - B' 0 ω i)))
      = Measure.pi (fun i : Fin d => Q.map (fun ω (t : ℝ≥0) => c * (B' t ω i - B' 0 ω i))) :=
    hindep'.map_fun_eq_pi_map (fun i => (measurable_pi_lambda _ fun t =>
      ((hcoord' t i).sub (hcoord' 0 i)).const_mul c).aemeasurable)
  -- each coordinate path has the same law
  have hcoordlaw : ∀ i : Fin d, P.map (fun ω (t : ℝ≥0) => c * (B t ω i - B 0 ω i))
      = Q.map (fun ω (t : ℝ≥0) => c * (B' t ω i - B' 0 ω i)) := by
    intro i
    have h1 : IsPreBrownianReal (fun t ω => c * (B t ω i - B 0 ω i)) P := by
      have h := ((hsp.shift 0).coord i).toIsPreBrownianReal
      simpa only [PiLp.sub_apply, PiLp.zero_apply, sub_zero, zero_add] using h
    have h2 : IsPreBrownianReal (fun t ω => c * (B' t ω i - B' 0 ω i)) Q := by
      have h := ((hsp'.shift 0).coord i).toIsPreBrownianReal
      simpa only [PiLp.sub_apply, PiLp.zero_apply, sub_zero, zero_add] using h
    exact LatticeProb.map_path_eq_of_isPreBrownianReal h1 h2
      (fun t => ((hcoord t i).sub (hcoord 0 i)).const_mul c)
      (fun t => ((hcoord' t i).sub (hcoord' 0 i)).const_mul c)
  have hT : P.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B t ω i - B 0 ω i)))
      = Q.map (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B' t ω i - B' 0 ω i))) := by
    rw [hpi, hpi']
    exact congrArg Measure.pi (funext hcoordlaw)
  -- undo the rescaling
  by_cases hd : d = 0
  · subst hd
    have h1 : (fun ω (t : ℝ≥0) => B t ω - B 0 ω) = fun _ (_ : ℝ≥0) => (0 : Space 0) := by
      funext ω t
      ext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    have h2 : (fun ω (t : ℝ≥0) => B' t ω - B' 0 ω) = fun _ (_ : ℝ≥0) => (0 : Space 0) := by
      funext ω t
      ext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    rw [h1, h2, Measure.map_const, Measure.map_const]
    simp
  have hcne : c ≠ 0 := by
    have hdpos : (0 : ℝ) < d := by
      have : 0 < d := Nat.pos_of_ne_zero hd
      exact_mod_cast this
    rw [hc]
    exact (Real.sqrt_pos.2 hdpos).ne'
  have hφ : Measurable fun v : Fin d → (ℝ≥0 → ℝ) => (fun t : ℝ≥0 =>
      ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => c⁻¹ * v i t) : Space d)) := by
    refine measurable_pi_lambda _ fun t => ?_
    refine ((EuclideanSpace.equiv (Fin d) ℝ).symm.continuous).measurable.comp ?_
    refine measurable_pi_lambda _ fun i => ?_
    exact (((measurable_pi_apply t : Measurable fun g : ℝ≥0 → ℝ => g t)).comp
      ((measurable_pi_apply i : Measurable fun v : Fin d → (ℝ≥0 → ℝ) => v i))).const_mul c⁻¹
  have hsymm : ∀ (v : Fin d → ℝ) (i : Fin d),
      ((EuclideanSpace.equiv (Fin d) ℝ).symm v) i = v i := fun _ _ => rfl
  have hcompB : (fun v : Fin d → (ℝ≥0 → ℝ) => (fun t : ℝ≥0 =>
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => c⁻¹ * v i t) : Space d)))
        ∘ (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B t ω i - B 0 ω i)))
      = fun ω (t : ℝ≥0) => B t ω - B 0 ω := by
    funext ω t
    ext i
    simp only [Function.comp_apply, PiLp.sub_apply, hsymm]
    rw [inv_mul_cancel_left₀ hcne]
  have hcompB' : (fun v : Fin d → (ℝ≥0 → ℝ) => (fun t : ℝ≥0 =>
        ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => c⁻¹ * v i t) : Space d)))
        ∘ (fun ω (i : Fin d) => (fun t : ℝ≥0 => c * (B' t ω i - B' 0 ω i)))
      = fun ω (t : ℝ≥0) => B' t ω - B' 0 ω := by
    funext ω t
    ext i
    simp only [Function.comp_apply, PiLp.sub_apply, hsymm]
    rw [inv_mul_cancel_left₀ hcne]
  rw [← hcompB, ← hcompB', ← Measure.map_map hφ hmT, ← Measure.map_map hφ hmT', hT]

end Sandpile.Support
