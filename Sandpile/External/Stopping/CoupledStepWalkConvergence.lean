import Sandpile.External.Stopping.CenteredWalkCoupling
import Sandpile.External.Stopping.StepWalkJointMeasurable

/-!
# Uniform convergence of coupled step walks

The Skorokhod coupling of interpolated paths also yields uniform convergence of
centered step walks, since the interpolation error is at most one mesh step.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Under the centered-walk coupling, the corresponding step paths converge
uniformly on every fixed finite time interval. -/
theorem ae_tendstoUniformlyOn_centered_diffusiveStepWalk
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} [NeZero d]
    (R : ℕ → ℝ) (q : ℕ → Site d) (hRpos : ∀ n, 0 < R n)
    (hR : Tendsto R atTop atTop)
    (X : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hXm : ∀ n, Measurable (X n)) (hXlaw : ∀ n, P.map (X n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (X n ω)) atTop (𝓝 (Y ω)))
    (H : ℝ≥0) :
    ∀ᵐ ω ∂P, TendstoUniformlyOn
      (fun n t => diffusiveStepWalk (R n) t (X n ω) - Lclt.scaledSite (R n) (q n))
      (fun t => Y ω t) atTop (Set.Icc 0 H) := by
  have herr : ∀ᵐ ω ∂P, ∀ n t,
      ‖diffusiveWalk (R n) t (X n ω) - diffusiveStepWalk (R n) t (X n ω)‖ ≤ 1 / R n := by
    apply ae_all_iff.2
    intro n
    have ht : ∀ᵐ X ∂P.map (X n), ∀ t,
        ‖diffusiveWalk (R n) t X - diffusiveStepWalk (R n) t X‖ ≤ 1 / R n := by
      rw [hXlaw n]
      exact ae_norm_diffusiveWalk_sub_stepWalk_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
        (q n) (R n) (hRpos n)
    exact ae_of_ae_map (hXm n).aemeasurable ht
  have hinv : Tendsto (fun n => 1 / R n) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  filter_upwards [hconv, herr] with ω hω he
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hω)
    (Set.Icc (0 : ℝ≥0) H) isCompact_Icc
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, 1 / R n < ε / 2 :=
    hinv.eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [hu (ε / 2) (half_pos hε), hsmall] with n hn hs t ht
  have hwalk := hn t ht
  have hstep : dist (centeredWalkPath (R n) (q n) (X n ω) t)
      (diffusiveStepWalk (R n) t (X n ω) - Lclt.scaledSite (R n) (q n)) ≤ 1 / R n := by
    rw [dist_eq_norm]
    change ‖(diffusiveWalk (R n) t (X n ω) - Lclt.scaledSite (R n) (q n)) -
      (diffusiveStepWalk (R n) t (X n ω) - Lclt.scaledSite (R n) (q n))‖ ≤ _
    simpa only [sub_sub_sub_cancel_right] using he n t
  exact lt_of_le_of_lt (dist_triangle _ _ _) (by linarith)

end Sandpile.External.Stopping
