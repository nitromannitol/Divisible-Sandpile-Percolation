import Sandpile.External.Stopping.WalkIndependentBlocks
import Sandpile.External.Stopping.StepWalk

/-!
# Independent increments of the step walk

Successive increments of a step walk are sums over disjoint blocks of its
independent driving increments. Thus the step walk has independent increments
under the driver law, including after deterministic diffusive time scaling.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Consecutive half-open intervals with monotone endpoints are pairwise
disjoint. -/
theorem pairwise_disjoint_Ico_of_monotone {n : ℕ} (b : Fin (n + 1) → ℕ) (hb : Monotone b) :
    Pairwise (fun i j : Fin n => Disjoint
      ((Finset.Ico (b i.castSucc) (b i.succ) : Finset ℕ) : Set ℕ)
      ((Finset.Ico (b j.castSucc) (b j.succ) : Finset ℕ) : Set ℕ)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · have hidx : i.succ ≤ j.castSucc := by
      apply Fin.le_def.2
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have horder := hb hidx
    apply Set.disjoint_left.2
    intro k hk hk'
    have hk₁ := Finset.mem_Ico.1 hk
    have hk₂ := Finset.mem_Ico.1 hk'
    omega
  · have hidx : j.succ ≤ i.castSucc := by
      apply Fin.le_def.2
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have horder := hb hidx
    apply Set.disjoint_left.2
    intro k hk hk'
    have hk₁ := Finset.mem_Ico.1 hk
    have hk₂ := Finset.mem_Ico.1 hk'
    omega

/-- Under the independent increment driver, a step walk has independent
increments. -/
theorem hasIndepIncrements_stepWalk_driver {d : ℕ} [NeZero d] (R : ℝ) (q : Site d) :
    HasIndepIncrements (fun t ξ => stepWalk R t (LatticeProb.sitePath q ξ))
      (LatticeProb.incPathLaw d) := by
  intro n t ht
  let b : Fin (n + 1) → ℕ := fun i => ⌊(t i : ℝ)⌋₊
  have hb : Monotone b := by
    intro i j hij
    apply Nat.floor_mono
    exact_mod_cast ht hij
  let A : Fin n → Finset ℕ := fun i => Finset.Ico (b i.castSucc) (b i.succ)
  have hdisj : Pairwise (fun i j : Fin n => Disjoint (A i : Set ℕ) (A j : Set ℕ)) :=
    pairwise_disjoint_Ico_of_monotone b hb
  have hind := iIndepFun_scaled_site_block_sums (d := d) R A hdisj
  convert hind using 1
  funext i ξ
  have hle : b i.castSucc ≤ b i.succ := hb (by exact Fin.castSucc_le_succ i)
  have hsum : (∑ k ∈ A i, ξ k) =
      LatticeProb.sitePath q ξ (b i.succ) - LatticeProb.sitePath q ξ (b i.castSucc) := by
    dsimp only [A]
    rw [Finset.sum_Ico_eq_sub _ hle]
    simp only [LatticeProb.sitePath]
    abel
  have hscale (v w : Site d) : Lclt.scaledSite R (v - w) =
      Lclt.scaledSite R v - Lclt.scaledSite R w := by
    ext j
    simp only [Lclt.scaledSite, Pi.sub_apply, PiLp.sub_apply, Int.cast_sub]
    ring
  change Lclt.scaledSite R (LatticeProb.sitePath q ξ (b i.succ)) -
      Lclt.scaledSite R (LatticeProb.sitePath q ξ (b i.castSucc)) =
    Lclt.scaledSite R (∑ k ∈ A i, ξ k)
  rw [hsum, hscale]

/-- Deterministic diffusive time scaling preserves the step walk's independent
increments under the driver law. -/
theorem hasIndepIncrements_diffusiveStepWalk_driver {d : ℕ} [NeZero d] (R : ℝ) (q : Site d) :
    HasIndepIncrements (fun t ξ => diffusiveStepWalk R t (LatticeProb.sitePath q ξ))
      (LatticeProb.incPathLaw d) := by
  intro n t ht
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hm : Monotone (fun i => c * t i) := fun i j hij =>
    mul_le_mul_of_nonneg_left (ht hij) (zero_le : 0 ≤ c)
  exact hasIndepIncrements_stepWalk_driver R q n (fun i => c * t i) hm

end Sandpile.External.Stopping
