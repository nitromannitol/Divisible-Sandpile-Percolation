import Sandpile.External.Stopping.CoupledBrownianCubeExit
import Sandpile.External.Stopping.LatticeCubeExitFinite
import Sandpile.External.Stopping.CenteredWalkCoupling

/-!
# Coupled invariance principle for cube-stopped walks

Centered simple random walks can be coupled with Brownian motion so that their
cube exit times and paths stopped at the exit and a finite horizon converge
almost surely. The walk and Brownian marginals retain their original laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The cube-stopped centered walk admits a Brownian coupling with almost sure
convergence of exit times and stopped paths, also for varying horizons. -/
theorem exists_cube_stopped_walk_brownian_coupling
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (H : ℕ → ℝ≥0) (h : ℝ≥0) (hH : Tendsto H atTop (𝓝 h))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : LatticeProb.IsBrownianSpace d 0 B PB) :
    ∃ (F : ΩB → C(ℝ≥0, Continuum.Space d)) (_hFm : Measurable F),
      (∀ᵐ ω ∂PB, ∀ t, F ω t = B t ω) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d)),
        (∀ n, Measurable (X n)) ∧ Measurable Y ∧
        (∀ n, P.map (X n) = walkLaw d (q n)) ∧ P.map Y = PB.map F ∧
        ∀ᵐ ω ∂P,
          let τ := LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω
          let N := fun n => (Sandpile.exitTime (supBox (q n) (R n)) (X n ω)).toNat
          let m := fun n => (⟨(R n) ^ 2, sq_nonneg (R n)⟩ : ℝ≥0)
          τ ≠ ⊤ ∧ (∀ n, Sandpile.exitTime (supBox (q n) (R n)) (X n ω) ≠ ⊤) ∧
          Tendsto (fun n => LatticeProb.ConstantStepInterpolation.knot (m n) (N n)) atTop
            (𝓝 τ.toNNReal) ∧
          Tendsto (fun n => LatticeProb.stoppedPath
              ((min (LatticeProb.ConstantStepInterpolation.knot (m n) (N n)) (H n) : ℝ≥0) : ℝ≥0∞)
              (centeredWalkPath (R n) (q n) (X n ω))) atTop
            (𝓝 (LatticeProb.stoppedPath ((min τ.toNNReal h : ℝ≥0) : ℝ≥0∞) (Y ω))) := by
  obtain ⟨F, hFm, hF, Ω, mΩ, P, hP, X, Y, hXm, hYm, hXmap, hYmap, hconv⟩ :=
    exists_centered_walk_brownian_coupling d R q hRpos hR PB B hB
  have hregular := ae_equalLaw_brownian_unitCube_exit_regular B hB F hFm hF Y hYm hYmap
  have hwalk : ∀ᵐ ω ∂P, ∀ n,
      X n ω 0 = q n ∧ (∀ j, (LatticeProb.lattice d).Adj (X n ω j) (X n ω (j + 1))) ∧
        Sandpile.exitTime (supBox (q n) (R n)) (X n ω) ≠ ⊤ := by
    apply ae_all_iff.2
    intro n
    have ha : ∀ᵐ Z ∂P.map (X n), Z 0 = q n ∧
        (∀ j, (LatticeProb.lattice d).Adj (Z j) (Z (j + 1))) ∧
        Sandpile.exitTime (supBox (q n) (R n)) Z ≠ ⊤ := by
      rw [hXmap n]
      filter_upwards [LatticeProb.ae_adj_siteWalkLaw (q n),
        ae_latticeCube_exitTime_ne_top (q n) (q n) (R n)] with Z hz he
      exact ⟨hz.1, hz.2, he⟩
    exact ae_of_ae_map (hXm n).aemeasurable ha
  refine ⟨F, hFm, hF, Ω, mΩ, P, hP, X, Y, hXm, hYm, hXmap, hYmap, ?_⟩
  filter_upwards [hconv, hregular, hwalk] with ω hconvω hregω hwalkω
  dsimp only
  let τ := LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω
  let m : ℕ → ℝ≥0 := fun n => ⟨(R n) ^ 2, sq_nonneg (R n)⟩
  let N : ℕ → ℕ := fun n => (Sandpile.exitTime (supBox (q n) (R n)) (X n ω)).toNat
  have hm (n : ℕ) : 0 < m n := by
    change (0 : ℝ) < (R n) ^ 2
    exact sq_pos_of_pos (hRpos n)
  have hexit (n : ℕ) : hitTime (supBox (q n) (R n))ᶜ (X n ω) = N n := by
    rw [← exitTime_eq_hitTime_compl]
    exact (ENat.natCast_toNat (hwalkω n).2.2).symm
  have hstart (n : ℕ) : X n ω 0 ∈ supBox (q n) (R n) := by
    rw [(hwalkω n).1]
    intro i
    simp only [sub_self, abs_zero]
    exact Int.floor_nonneg.2 (hRpos n).le
  have hstep (n j : ℕ) : X n ω (j + 1) = X n ω j ∨
      (LatticeProb.lattice d).Adj (X n ω j) (X n ω (j + 1)) := Or.inr ((hwalkω n).2.1 j)
  have hpath (n : ℕ) (t : ℝ≥0) : centeredWalkPath (R n) (q n) (X n ω) t =
      LatticeProb.ConstantStepInterpolation.path (m n)
        (centeredScaledSite (R n) (q n) ∘ X n ω) t := by
    change diffusiveWalk (R n) t (X n ω) - Lclt.scaledSite (R n) (q n) =
      LatticeProb.ConstantStepInterpolation.path ((R n) ^ 2)
        (centeredScaledSite (R n) (q n) ∘ X n ω) t
    exact (centered_constantStep_path_eq_diffusiveWalk (R n) (q n) (X n ω) t).symm
  have hclock := tendsto_latticeCube_clocks_and_stoppedPaths R q (fun n => X n ω) m N
    (fun n => centeredWalkPath (R n) (q n) (X n ω)) (Y ω) τ.toNNReal h H
    hRpos hR hm hexit hstart hstep hpath hconvω hH hregω.2.1 hregω.2.2
  exact ⟨hregω.1, fun n => (hwalkω n).2.2, hclock.2.1, hclock.2.2.2⟩

end Sandpile.External.Stopping
