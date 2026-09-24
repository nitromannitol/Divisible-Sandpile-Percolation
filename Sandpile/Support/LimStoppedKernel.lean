/-
The white-noise representation of the ball-stopped field of
`sandpile.tex:2499-2513`.

The field `𝒳_{s,T}` is defined at `Sandpile/Support/LimValueApproximation.lean`
as `(2d)⁻¹` times the increment `Z(T,u) - E_B[Z(T-τ, B_τ)]` of the heat potential
along the rule that stops the motion when it leaves the ball of radius `s` about
its starting point, or at the horizon `T`.  The paper describes the same field as
`(2d)⁻¹` times the white-noise average against the expected occupation density of
that stopped motion, and this module proves that the two descriptions agree: the
increment is almost surely `W` evaluated at the explicit spatial function

  `y ↦ g_T(u,y) - ∫ g_{T-τ(b)}(B_{τ(b)}(b), y) dP_B(b)`,

which is `ballStoppedKernel` below.  Both the stochastic Fubini
(`gaussianPotential_stopped_integral_comm_pointwise`) and the pointwise form of
the Bochner integral of the Green kernels are already available; what is added
here is the identification of the whole increment, in the exact shape
`ballStoppedField` is written in, together with the square integrability of the
kernel, which every clause of `IsWhiteNoise` asks for before it says anything.
-/
import Sandpile.Support.LimValueApproximation
import Sandpile.Support.ExplGreenFubini

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {ΩW ΩB : Type*}

/-- The exit time of the ball of radius `s` about `planePoint u`, truncated at the
horizon `T`: the stopping rule of `sandpile.tex:2501-2503`. -/
noncomputable def ballStopTime (d : ℕ) (B : Space d → ℝ≥0 → ΩB → Space d) (s T : ℝ)
    (u : Space 2) (b : ΩB) : ℝ≥0 :=
  LatticeProb.exitTimeTrunc (B (planePoint u)) (planePoint u) s T.toNNReal b

theorem ballStopTime_le {d : ℕ} (B : Space d → ℝ≥0 → ΩB → Space d) (s T : ℝ)
    (u : Space 2) (b : ΩB) : ballStopTime d B s T u b ≤ T.toNNReal := by
  have h : ((ballStopTime d B s T u b : ℝ≥0) : ℝ≥0∞) ≤ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ballStopTime, LatticeProb.coe_exitTimeTrunc]
    exact inf_le_right
  exact_mod_cast h

theorem ballStopTime_le_real {d : ℕ} (B : Space d → ℝ≥0 → ΩB → Space d) {s T : ℝ}
    (hT : 0 ≤ T) (u : Space 2) (b : ΩB) : (ballStopTime d B s T u b : ℝ) ≤ T := by
  have h := ballStopTime_le B s T u b
  have h' : (ballStopTime d B s T u b : ℝ) ≤ ((T.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast h
  rwa [Real.coe_toNNReal T hT] at h'

theorem measurable_ballStopTime [MeasurableSpace ΩB] {d : ℕ}
    {B : Space d → ℝ≥0 → ΩB → Space d} (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) (s T : ℝ) (u : Space 2) :
    Measurable (ballStopTime d B s T u) :=
  LatticeProb.measurable_exitTimeTrunc (hBm (planePoint u)) (hBc (planePoint u))
    (planePoint u) s T.toNNReal

/-- The expected Green kernel from the stopped position, the second half of the
occupation density of the stopped rule. -/
noncomputable def stoppedGreenKernel [MeasurableSpace ΩB] (d : ℕ) (PB : Measure ΩB)
    (B : Space d → ℝ≥0 → ΩB → Space d) (s T : ℝ) (u : Space 2) (y : Space d) : ℝ :=
  ∫ b, greenTimeBM d (T - (ballStopTime d B s T u b : ℝ))
    (B (planePoint u) (ballStopTime d B s T u b) b) y ∂PB

/-- **The occupation density of the ball-stopped rule.**  The expected occupation
density, at `y`, of the motion started at `planePoint u` and stopped when it leaves
the ball of radius `s` or at the horizon `T`, in the form the increment of the heat
potential produces it. -/
noncomputable def ballStoppedKernel [MeasurableSpace ΩB] (d : ℕ) (PB : Measure ΩB)
    (B : Space d → ℝ≥0 → ΩB → Space d) (s T : ℝ) (u : Space 2) (y : Space d) : ℝ :=
  greenTimeBM d T (planePoint u) y - stoppedGreenKernel d PB B s T u y

section

variable [MeasurableSpace ΩB] {d : ℕ}

/-- The stopped Green kernel is square integrable: it is the pointwise form of a
Bochner integral of square integrable Green kernels. -/
theorem memLp_stoppedGreenKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 ≤ T) (u : Space 2) :
    MemLp (stoppedGreenKernel d PB B s T u) 2 (volume : Measure (Space d)) := by
  set τ : ΩB → ℝ≥0 := ballStopTime d B s T u with hτdef
  have hτm : Measurable τ := measurable_ballStopTime hBc hBm s T u
  have hτT : ∀ b, τ b ≤ T.toNNReal := ballStopTime_le B s T u
  set q : ΩB → ℝ≥0 × Space d := fun b =>
    (⟨((T.toNNReal : ℝ≥0) : ℝ) - τ b, sub_nonneg.mpr (by exact_mod_cast hτT b)⟩,
      B (planePoint u) (τ b) b) with hqdef
  have hq : Measurable q :=
    measurable_stopped_spaceTime (B (planePoint u)) (hBc _) (hBm _) τ hτm T.toNNReal hτT
  have hqT : ∀ b, (q b).1 ≤ T.toNNReal := fun b =>
    show ((T.toNNReal : ℝ≥0) : ℝ) - τ b ≤ ((T.toNNReal : ℝ≥0) : ℝ) from
      sub_le_self _ (τ b).property
  set F : ΩB → Lp ℝ 2 (volume : Measure (Space d)) := fun b =>
    (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp
      (greenTimeBM d (q b).1 (q b).2) with hFdef
  set f : ΩB → Space d → ℝ := fun b y => greenTimeBM d (q b).1 (q b).2 y with hfdef
  have hF : Integrable F PB :=
    integrable_greenTimeBM_toLp_of_bounded_time PB hd hd3 q hq T.toNNReal hqT
  have hf : Integrable (Function.uncurry f) (PB.prod (volume : Measure (Space d))) :=
    integrable_greenTimeBM_product PB hd q hq T.toNNReal hqT
  have he (b : ΩB) : f b =ᵐ[volume] (fun y => F b y) :=
    (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).coeFn_toLp.symm
  have hrep := coe_integral_L2_eq_integral_of_integrable PB volume F hF f hf he
  have hmem : MemLp (fun y => ∫ b, f b y ∂PB) 2 (volume : Measure (Space d)) :=
    MemLp.ae_eq hrep (Lp.memLp (∫ b, F b ∂PB))
  have hco : stoppedGreenKernel d PB B s T u = fun y => ∫ b, f b y ∂PB := by
    funext y
    simp only [stoppedGreenKernel, hfdef, hqdef, Real.coe_toNNReal T hT]
    rfl
  rw [hco]
  exact hmem

theorem memLp_ballStoppedKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 ≤ T) (u : Space 2) :
    MemLp (ballStoppedKernel d PB B s T u) 2 (volume : Measure (Space d)) :=
  (memLp_greenTimeBM hd hd3 hT (planePoint u)).sub
    (memLp_stoppedGreenKernel hd hd3 PB hBc hBm hT u)

end

/-- **The ball-stopped field is the white-noise average against its occupation
density.**  This is the identification `sandpile.tex:2499-2503` makes when it calls
`𝒳_{s,T}(u)` "`(2d)⁻¹` times the white-noise average against the expected occupation
density of Brownian motion, started at `u`, stopped at time `T` or when it exits the
ball of radius `s` around `u`". -/
theorem ae_ballStoppedField_eq_whiteNoise [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) {Z : ℝ → Space d → ΩW → ℝ}
    (hmod : ∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d 1 W t x ω)
    (hZc : ContinuousHeatPotential d Z PW)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 < T) (u : Space 2) :
    (fun ω => 2 * (d : ℝ) * ballStoppedField d Z PB B s T u ω) =ᵐ[PW]
      W (ballStoppedKernel d PB B s T u) := by
  have hd0 : 2 * (d : ℝ) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  set τ : ΩB → ℝ≥0 := ballStopTime d B s T u with hτdef
  have hτm : Measurable τ := measurable_ballStopTime hBc hBm s T u
  have hτT : ∀ b, τ b ≤ T.toNNReal := ballStopTime_le B s T u
  have hTc : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
  -- the stochastic Fubini for the stopped term
  have hcomm := gaussianPotential_stopped_integral_comm_pointwise hd hd3 hW 1 Z
    (fun t _ x => hmod t x) hZc PB (B (planePoint u)) (hBc _) (hBm _) τ hτm T.toNNReal hτT
  have hstop : W (stoppedGreenKernel d PB B s T u) =ᵐ[PW]
      fun ω => ∫ b, Z (T - (τ b : ℝ)) (B (planePoint u) (τ b) b) ω ∂PB := by
    have hker : stoppedGreenKernel d PB B s T u
        = fun y => ∫ b, Real.sqrt 1 *
          greenTimeBM d (((T.toNNReal : ℝ≥0) : ℝ) - τ b)
            (B (planePoint u) (τ b) b) y ∂PB := by
      funext y
      rw [stoppedGreenKernel, hTc]
      simp only [Real.sqrt_one, one_mul]
      rfl
    rw [hker]
    refine hcomm.2.trans (Eventually.of_forall fun ω => ?_)
    simp only [hTc]
  -- the free term
  have hfree : Z T (planePoint u) =ᵐ[PW] W (greenTimeBM d T (planePoint u)) := by
    refine (hmod T (planePoint u)).trans (Eventually.of_forall fun ω => ?_)
    simp only [gaussianPotential, Real.sqrt_one, one_mul]
  -- additivity of the noise on the two square integrable kernels
  have hmemS : MemLp (stoppedGreenKernel d PB B s T u) 2 (volume : Measure (Space d)) :=
    memLp_stoppedGreenKernel hd hd3 PB hBc hBm hT.le u
  have hmemD : MemLp (ballStoppedKernel d PB B s T u) 2 (volume : Measure (Space d)) :=
    memLp_ballStoppedKernel hd hd3 PB hBc hBm hT.le u
  have hadd : W (fun y => ballStoppedKernel d PB B s T u y + stoppedGreenKernel d PB B s T u y)
      =ᵐ[PW] fun ω => W (ballStoppedKernel d PB B s T u) ω +
        W (stoppedGreenKernel d PB B s T u) ω := hW.add _ _ hmemD hmemS
  have hsum : (fun y => ballStoppedKernel d PB B s T u y + stoppedGreenKernel d PB B s T u y)
      = greenTimeBM d T (planePoint u) := by
    funext y
    rw [ballStoppedKernel]
    ring
  rw [hsum] at hadd
  filter_upwards [hfree, hstop, hadd, hcomm.1] with ω h1 h2 h3 _
  have hval : 2 * (d : ℝ) * ballStoppedField d Z PB B s T u ω
      = Z T (planePoint u) ω - ∫ b, Z (T - (τ b : ℝ)) (B (planePoint u) (τ b) b) ω ∂PB := by
    simp only [ballStoppedField, hτdef, ballStopTime]
    rw [integral_neg, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    ring
  rw [hval, h1, ← h2, h3]
  ring

end Sandpile.Support
