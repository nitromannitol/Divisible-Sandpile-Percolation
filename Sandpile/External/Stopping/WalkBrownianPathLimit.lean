import Sandpile.External.Stopping.WalkInterpolatedFiniteTimes
import Sandpile.External.Stopping.WalkPathConvergence

/-!
# Functional limit of interpolated walks

Tightness and finite-dimensional convergence identify the weak limit of the
interpolated walk laws with any measurable continuous version of Brownian motion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The interpolated walk laws converge to the law of a continuous version of
the Brownian motion, provided the rescaled starting sites remain bounded. -/
theorem tendsto_diffusiveWalkPathLaw_brownian
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (x : ℕ → Site d) (hR : Tendsto R atTop atTop)
    (y : Continuum.Space d)
    (hx : Tendsto (fun n => Lclt.scaledSite (R n) (x n)) atTop (𝓝 y))
    (M : ℝ) (hM : ∀ n, dist (Lclt.scaledSite (R n) (x n)) 0 ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P)
    (F : Ω → C(ℝ≥0, Continuum.Space d)) (hF : AEMeasurable F P)
    (hFB : ∀ᵐ ω ∂P, ∀ t, F ω t = y + B t ω) :
    Tendsto (fun n => diffusiveWalkPathLaw d (R n) (x n)) atTop
      (𝓝 (⟨P.map F, (Measure.isProbabilityMeasure_map_iff hF).2 inferInstance⟩ :
        ProbabilityMeasure C(ℝ≥0, Continuum.Space d))) := by
  let μ : ProbabilityMeasure C(ℝ≥0, Continuum.Space d) :=
    ⟨P.map F, (Measure.isProbabilityMeasure_map_iff hF).2 inferInstance⟩
  apply tendsto_diffusiveWalkPathLaw_of_finiteDimensional d R x hR M hM μ
  intro I
  let e : (I × Fin d → ℝ) → (I → Continuum.Space d) := fun z i =>
    WithLp.toLp 2 (fun j => z (i, j))
  have he : Continuous e := by
    apply continuous_pi
    intro i
    apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.continuous.comp
    exact continuous_pi fun j => continuous_apply (i, j)
  have h := (tendstoInDistribution_walk_interpolated_finite_times R hR
    (fun i : I => (i : ℝ≥0)) x y hx P B hB).continuous_comp he
  have hlim : TendstoInDistribution
      (fun n X (i : I) => diffusiveWalk (R n) i X) atTop
      (fun ω i => F ω i) (fun n => LatticeProb.siteWalkLaw d (x n)) P := by
    apply h.congr
    · intro n
      exact Filter.Eventually.of_forall (fun X => by ext i j; rfl)
    · filter_upwards [hFB] with ω hω
      ext i j
      simp only [Function.comp_apply, e, WithLp.ofLp_toLp]
      exact congrArg (fun z : Continuum.Space d => z j) (hω i).symm
  have heval : Measurable (fun f : C(ℝ≥0, Continuum.Space d) =>
      I.restrict (ReflectedGMS.MartingaleLimit.pathCoordinates f)) :=
    (ReflectedGMS.MartingaleLimit.continuous_finsetRestrict_pathCoordinates I).measurable
  have heq (n : ℕ) : (diffusiveWalkPathLaw d (R n) (x n)).map
      (fun f => I.restrict (ReflectedGMS.MartingaleLimit.pathCoordinates f)) =
      (⟨(LatticeProb.siteWalkLaw d (x n)).map
        (fun X (i : I) => diffusiveWalk (R n) i X), inferInstance⟩ :
        ProbabilityMeasure (I → Continuum.Space d)) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Measure.map _ (walkLaw d (x n))).map _ = _
    rw [Measure.map_map heval (measurable_diffusiveWalkPath (R n))]
    rfl
  have heq' : μ.map (fun f => I.restrict (ReflectedGMS.MartingaleLimit.pathCoordinates f)) =
      (⟨P.map (fun ω i => F ω i), inferInstance⟩ : ProbabilityMeasure (I → Continuum.Space d)) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (P.map F).map _ = _
    rw [AEMeasurable.map_map_of_aemeasurable heval.aemeasurable hF]
    rfl
  simp_rw [heq, heq']
  exact hlim.tendsto

end Sandpile.External.Stopping
