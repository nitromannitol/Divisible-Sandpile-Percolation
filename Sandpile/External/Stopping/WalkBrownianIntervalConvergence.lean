import Sandpile.External.Stopping.WalkIntervalCharacteristic
import Sandpile.External.Stopping.BrownianIntervalCharacteristicAll
import LatticeProb.Prob.CramerWold

/-!
# Convergence of walk interval increments to Brownian increments

On finitely many disjoint positive time intervals, projected diffusive walk
increments converge jointly in law to the corresponding Brownian increments.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Joint convergence of projected walk increments on disjoint time intervals. -/
theorem tendstoInDistribution_walk_brownian_interval_increments
    {d m : ℕ} [NeZero d] (a : Fin m → Fin d → ℝ)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i < t i)
    (hdisj : ∀ i j, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) i =>
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t i : ℝ) * (R n) ^ 2⌋₊ -
          ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
          LatticeProb.dotSite (a i) (ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k)))
      atTop (fun ω i => ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ))
      (fun _ => LatticeProb.incPathLaw d) P := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  let X : ℕ → (ℕ → LatticeProb.Site d) → (Fin m → ℝ) := fun n ξ i =>
    (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t i : ℝ) * (R n) ^ 2⌋₊ -
      ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
      LatticeProb.dotSite (a i) (ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k))
  let Y : Ω → Fin m → ℝ := fun ω i =>
    ∑ ℓ, a i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ)
  have hX (n : ℕ) : AEMeasurable (X n) (LatticeProb.incPathLaw d) := by
    apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro i
    dsimp [X]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro k _
    exact (measurable_of_countable (LatticeProb.dotSite (a i))).comp (measurable_pi_apply _)
  have hY : AEMeasurable Y P := by
    apply AEMeasurable.of_eval
    intro i
    dsimp [Y]
    apply Finset.aemeasurable_fun_sum
    intro ℓ _
    exact ((LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (t i) ℓ).sub
      (LatticeProb.Scaling.WalkCLT.aemeasurable_isBrownianSpace_coord hd hB (s i) ℓ)).const_mul _
  have hst' (i : Fin m) : (s i : ℝ) < t i := hst i
  have hdisj' (i j : Fin m) (hij : i ≠ j) :
      (t i : ℝ) ≤ s j ∨ (t j : ℝ) ≤ s i := hdisj i j hij
  apply LatticeProb.CramerWold.tendstoInDistribution_pi_of_forall_dot X Y
    (LatticeProb.incPathLaw d) P hX hY
  intro c
  apply TendstoInDistribution.of_tendsto_charFun
    (fun n => Finset.aemeasurable_fun_sum _ fun i _ => (hX n).eval i |>.mul_const _)
    (Finset.aemeasurable_fun_sum _ fun i _ => (hY.eval i).mul_const _)
  intro u
  let b : Fin m → Fin d → ℝ := fun i ℓ => c i * a i ℓ
  have hwalk := tendsto_charFun_time_interval_increments d b R hR
    (fun i => (s i : ℝ)) (fun i => (t i : ℝ)) (fun i => (s i).property)
    hst' hdisj' u
  have hbrown := charFun_brownian_interval_increments_at hd hB b s t
    (fun i => (hst i).le) hdisj u
  have hx (n : ℕ) : (fun ξ => ∑ i, X n ξ i * c i) =
      fun ξ => ∑ i, (R n)⁻¹ * ∑ k ∈ Finset.range
        (⌊(t i : ℝ) * (R n) ^ 2⌋₊ - ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
          LatticeProb.dotSite (b i) (ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k)) := by
    funext ξ
    apply Finset.sum_congr rfl
    intro i _
    have hdot (z : LatticeProb.Site d) : LatticeProb.dotSite (b i) z =
        c i * LatticeProb.dotSite (a i) z := by
      simp only [LatticeProb.dotSite, b, Finset.mul_sum, mul_assoc]
    simp only [X, hdot, ← Finset.mul_sum]
    ring
  have hy : (fun ω => ∑ i, Y ω i * c i) =
      fun ω => ∑ i, ∑ ℓ, b i ℓ * (B (t i) ω ℓ - B (s i) ω ℓ) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _
    dsimp [Y, b]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ _
    ring
  simp_rw [hx, hy, hbrown]
  exact hwalk

end Sandpile.External.Stopping
