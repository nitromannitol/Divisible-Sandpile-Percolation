import Sandpile.External.Stopping.LatticeCubeBoundary
import LatticeProb.Graph.ExitTime
import LatticeProb.Graph.WalkAverage

/-!
# Simple random walk exits finite sets

The site-walk law and the graph-walk law have equal finite-horizon survival
probabilities. A simple random walk on a positive-dimensional lattice therefore
leaves every finite set almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- The two constructions of lattice simple random walk give the same
probability of staying in a set through a finite horizon. -/
theorem siteWalkLaw_stayIn_eq_graphWalkLaw {d : ℕ} [NeZero d] (D : Set (Site d))
    (n : ℕ) (x : Site d) :
    LatticeProb.siteWalkLaw d x (LatticeProb.Graph.stayIn D n) =
      LatticeProb.Graph.walkLaw (LatticeProb.lattice d) x (LatticeProb.Graph.stayIn D n) := by
  classical
  let S := LatticeProb.Graph.stayIn D n
  let F : (ℕ → Site d) → ℝ := S.indicator 1
  have hSm : MeasurableSet S := LatticeProb.Graph.measurableSet_stayIn D n
  have hFm : Measurable F := measurable_const.indicator hSm
  have hFb (X : ℕ → Site d) : ‖F X‖ ≤ 1 := by
    by_cases hX : X ∈ S <;> simp [F, hX]
  have hdep : LatticeProb.Graph.DependsUpTo n F := by
    intro X Y hXY
    have heq : X ∈ S ↔ Y ∈ S := by
      change (∀ j ≤ n, X j ∈ D) ↔ (∀ j ≤ n, Y j ∈ D)
      constructor <;> intro h j hj
      · rw [← hXY j hj]; exact h j hj
      · rw [hXY j hj]; exact h j hj
    by_cases hX : X ∈ S
    · have hY : Y ∈ S := heq.1 hX
      simp [F, hX, hY]
    · have hY : Y ∉ S := fun hY => hX (heq.2 hY)
      simp [F, hX, hY]
  have hdeg (v : Site d) : 0 < (LatticeProb.lattice d).degree v := by
    rw [LatticeProb.Graph.Zd.degree_eq]
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    omega
  have h1 := LatticeProb.walkExp_eq_integral n x F hdep
  have h2 := LatticeProb.Graph.walkExp_eq_integral hdeg n x F hFm 1 hFb hdep
  have hr : (LatticeProb.siteWalkLaw d x).real S =
      (LatticeProb.Graph.walkLaw (LatticeProb.lattice d) x).real S := by
    rw [← integral_indicator_one hSm, ← integral_indicator_one hSm]
    exact h1.symm.trans h2
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hr

/-- A simple random walk on a positive-dimensional lattice almost surely
leaves every given finite set. -/
theorem ae_siteWalk_exits_finite {d : ℕ} [NeZero d] (A : Finset (Site d)) (x : Site d) :
    ∀ᵐ X ∂(LatticeProb.siteWalkLaw d x), ∃ n, X n ∉ A := by
  classical
  let D : Set (Site d) := A
  let G := LatticeProb.lattice d
  let μ := LatticeProb.siteWalkLaw d x
  let ν := LatticeProb.Graph.walkLaw G x
  let S : ℕ → Set (ℕ → Site d) := LatticeProb.Graph.stayIn D
  have hdeg (v : Site d) : 0 < G.degree v := by
    rw [LatticeProb.Graph.Zd.degree_eq]
    have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    omega
  have hout : Dᶜ.Nonempty := by
    by_contra hn
    have hD : D = univ := Set.eq_univ_iff_forall.2 (fun v => by
      by_contra hv
      exact hn ⟨v, hv⟩)
    have hDf : D.Finite := A.finite_toSet
    exact Set.infinite_univ (hD ▸ hDf)
  obtain ⟨z, hz⟩ := hout
  have hesc : ∀ v : Site d, ∃ (w : Site d) (_ : G.Walk v w), w ∉ D := by
    intro v
    obtain ⟨p⟩ := (LatticeProb.Graph.Zd.latticeConnected d).preconnected v z
    exact ⟨z, p, hz⟩
  have hgraph := LatticeProb.Graph.ae_exitTime_ne_top hdeg A hesc x
  have hzeroν : ν (⋂ n, S n) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hgraph)
    intro X hX
    have hstay : ∀ n, X ∈ LatticeProb.Graph.stayIn D n := fun n => mem_iInter.1 hX n
    have heq := (LatticeProb.Graph.exitTime_eq_top_iff D X).2 hstay
    simpa only [mem_ofPred_eq, not_not] using heq
  have hμlim : Tendsto (fun n => μ (S n)) atTop (𝓝 (μ (⋂ n, S n))) := by
    apply tendsto_measure_iInter_atTop (fun n => (LatticeProb.Graph.measurableSet_stayIn D n).nullMeasurableSet)
      (fun _ _ h => LatticeProb.Graph.stayIn_antitone D h)
    exact ⟨0, measure_ne_top _ _⟩
  have hνlim : Tendsto (fun n => ν (S n)) atTop (𝓝 0) := by
    rw [← hzeroν]
    apply tendsto_measure_iInter_atTop (fun n => (LatticeProb.Graph.measurableSet_stayIn D n).nullMeasurableSet)
      (fun _ _ h => LatticeProb.Graph.stayIn_antitone D h)
    exact ⟨0, measure_ne_top _ _⟩
  have hzeroμ : μ (⋂ n, S n) = 0 := by
    apply tendsto_nhds_unique hμlim
    apply hνlim.congr'
    exact Filter.Eventually.of_forall fun n => (siteWalkLaw_stayIn_eq_graphWalkLaw D n x).symm
  rw [ae_iff]
  apply measure_mono_null _ hzeroμ
  intro X hX
  apply mem_iInter.2
  intro n
  change ∀ j ≤ n, X j ∈ D
  intro j _
  by_contra hj
  exact hX ⟨j, hj⟩

end Sandpile.External.Stopping
