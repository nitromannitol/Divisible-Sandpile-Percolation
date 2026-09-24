/-
The walk is nearest-neighbour almost surely.

`lem:dgt4-linearization-from-survival` (`sandpile.tex:5615-5660`) states its
covariance bound for deterministic nearest-neighbour paths, while Step 1 of its
proof integrates that bound against the law of two independent simple random
walks.  The bridge is that the law of the walk is carried by nearest-neighbour
paths: `walkLaw d x` is the image of the i.i.d. step law under `walkPath`, the
increments of `walkPath x ξ` are the coordinates of `ξ`, and `stepLaw d`, which
is `LatticeProb.instructionLaw 0`, gives no mass to a displacement that is
neither a unit vector nor the negative of one.  The conclusion is stated for
every time horizon at once, since `IsNNPath n X` constrains only the first `n`
increments and the increments are constrained one at a time.
-/
import Sandpile.Support.StrongMarkov
import Sandpile.Support.LinEarlyVar
import Sandpile.Frozen.DGT4PathSurvival

open MeasureTheory ProbabilityTheory Filter

namespace Sandpile.Support


variable {d : ℕ}

theorem stepLaw_notUnit_eq_zero :
    stepLaw d {e : Site d | ¬ ∃ i : Fin d, e = unit i ∨ e = -unit i} = 0 := by
  classical
  set S : Set (Site d) := {e : Site d | ¬ ∃ i : Fin d, e = unit i ∨ e = -unit i} with hS
  have hmem : ∀ i : Fin d, ((0 : Site d) + unit i) ∉ S ∧ ((0 : Site d) - unit i) ∉ S := by
    intro i
    refine ⟨?_, ?_⟩
    · simp only [hS, Set.mem_setOf_eq, not_not, zero_add]
      exact ⟨i, Or.inl rfl⟩
    · simp only [hS, Set.mem_setOf_eq, not_not, zero_sub]
      exact ⟨i, Or.inr rfl⟩
  simp only [stepLaw, LatticeProb.instructionLaw, Measure.smul_apply, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.coe_add, Pi.add_apply, Measure.dirac_apply]
  rw [Finset.sum_eq_zero, smul_zero]
  intro i _
  rw [Set.indicator_of_notMem (hmem i).1, Set.indicator_of_notMem (hmem i).2, add_zero]

theorem ae_step_mem_units (hd : 1 ≤ d) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d),
      ∀ r : ℕ, ∃ i : Fin d, ξ r = unit i ∨ ξ r = -unit i := by
  classical
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  rw [ae_all_iff]
  intro r
  rw [ae_iff]
  have hS : MeasurableSet {e : Site d | ¬ ∃ i : Fin d, e = unit i ∨ e = -unit i} :=
    MeasurableSet.of_discrete
  have hmap := Measure.map_apply (μ := Measure.infinitePi fun _ : ℕ => stepLaw d)
    (measurable_pi_apply r) hS
  rw [Measure.infinitePi_map_eval, stepLaw_notUnit_eq_zero] at hmap
  exact hmap.symm

theorem walkPath_succ (x : Site d) (ξ : ℕ → Site d) (r : ℕ) :
    walkPath x ξ (r + 1) = walkPath x ξ r + ξ r := by
  simp only [walkPath, Finset.sum_range_succ, add_assoc]

theorem measurableSet_allNN :
    MeasurableSet {X : ℕ → Site d |
      ∀ r : ℕ, ∃ i : Fin d, X (r + 1) = X r + unit i ∨ X (r + 1) = X r - unit i} := by
  classical
  have hrw : {X : ℕ → Site d |
      ∀ r : ℕ, ∃ i : Fin d, X (r + 1) = X r + unit i ∨ X (r + 1) = X r - unit i}
      = ⋂ r : ℕ, ⋃ i : Fin d,
          ({X : ℕ → Site d | X (r + 1) = X r + unit i} ∪
            {X : ℕ → Site d | X (r + 1) = X r - unit i}) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_union]
  have hadd : ∀ (i : Fin d) (r : ℕ), Measurable fun X : ℕ → Site d => X r + unit i := by
    intro i r
    have hcomp : (fun X : ℕ → Site d => X r + unit i)
        = (fun z : Site d => z + unit i) ∘ (fun X : ℕ → Site d => X r) := rfl
    rw [hcomp]
    exact Measurable.of_discrete.comp (measurable_pi_apply r)
  have hsub : ∀ (i : Fin d) (r : ℕ), Measurable fun X : ℕ → Site d => X r - unit i := by
    intro i r
    have hcomp : (fun X : ℕ → Site d => X r - unit i)
        = (fun z : Site d => z - unit i) ∘ (fun X : ℕ → Site d => X r) := rfl
    rw [hcomp]
    exact Measurable.of_discrete.comp (measurable_pi_apply r)
  rw [hrw]
  refine MeasurableSet.iInter fun r => MeasurableSet.iUnion fun i => MeasurableSet.union ?_ ?_
  · exact measurableSet_eq_fun (measurable_pi_apply (r + 1)) (hadd i r)
  · exact measurableSet_eq_fun (measurable_pi_apply (r + 1)) (hsub i r)

theorem ae_walkLaw_isNNPath (hd : 1 ≤ d) (x : Site d) :
    ∀ᵐ X ∂(walkLaw d x), ∀ n : ℕ,
      Frozen.DGT4PathSurvival.IsNNPath n X := by
  classical
  have hgood : ∀ X : ℕ → Site d,
      (∀ r : ℕ, ∃ i : Fin d, X (r + 1) = X r + unit i ∨ X (r + 1) = X r - unit i) →
      ∀ n : ℕ, Frozen.DGT4PathSurvival.IsNNPath n X := by
    intro X hX n r _
    exact hX r
  have hmeas : MeasurableSet {X : ℕ → Site d |
      ∀ n : ℕ, Frozen.DGT4PathSurvival.IsNNPath n X} := by
    have : {X : ℕ → Site d |
        ∀ n : ℕ, Frozen.DGT4PathSurvival.IsNNPath n X}
        = {X : ℕ → Site d |
          ∀ r : ℕ, ∃ i : Fin d, X (r + 1) = X r + unit i ∨ X (r + 1) = X r - unit i} := by
      ext X
      constructor
      · intro h r
        exact h (r + 1) r (Nat.lt_succ_self r)
      · intro h n r _
        exact h r
    rw [this]
    exact measurableSet_allNN
  rw [walkLaw, ae_map_iff (measurable_walkPath x).aemeasurable hmeas]
  filter_upwards [ae_step_mem_units hd] with ξ hξ
  refine hgood _ fun r => ?_
  obtain ⟨i, hi⟩ := hξ r
  refine ⟨i, ?_⟩
  rw [walkPath_succ x ξ r]
  rcases hi with hi | hi
  · exact Or.inl (by rw [hi])
  · exact Or.inr (by rw [hi]; ring)

/-- **Two independent walks are nearest-neighbour almost surely.**  This is the
form Step 1 of `lem:dgt4-linearization-from-survival` consumes: the covariance
bound of the lemma is assumed only for nearest-neighbour paths, and the pairs of
paths it is integrated over satisfy that condition for almost every pair. -/
theorem ae_walkPairLaw_isNNPath [NeZero d] (hd : 1 ≤ d) (x y : Site d) :
    ∀ᵐ p ∂(walkPairLaw d x y), ∀ n : ℕ,
      Frozen.DGT4PathSurvival.IsNNPath n p.1 ∧
      Frozen.DGT4PathSurvival.IsNNPath n p.2 := by
  classical
  have hx := ae_walkLaw_isNNPath hd x
  have hy := ae_walkLaw_isNNPath hd y
  have h1 : ∀ᵐ p ∂(walkPairLaw d x y), ∀ n : ℕ,
      Frozen.DGT4PathSurvival.IsNNPath n p.1 := by
    rw [walkPairLaw]
    exact Measure.quasiMeasurePreserving_fst.ae hx
  have h2 : ∀ᵐ p ∂(walkPairLaw d x y), ∀ n : ℕ,
      Frozen.DGT4PathSurvival.IsNNPath n p.2 := by
    rw [walkPairLaw]
    exact Measure.quasiMeasurePreserving_snd.ae hy
  filter_upwards [h1, h2] with p hp1 hp2 n
  exact ⟨hp1 n, hp2 n⟩

end Sandpile.Support
