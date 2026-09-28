import LatticeProb.Walk.Markov
import LatticeProb.Walk.HitProb
import Sandpile.Walk
import Sandpile.Support.StrongMarkov
import Sandpile.Support.HitProb

/-!
# Return probabilities and last-visit indicators of the simple random walk

The last-visit indicator `I_{i,j}(X) = 1 {X_i ≠ X_r for i < r ≤ j}` is a function of the walk
relative to its position at time `i`: writing `relPath i X k = X (i + k) - X i`, it is the
indicator `visitInd i m` that the relative path avoids its starting point in its first `m` steps,
and `survInd i` is the indicator that it never returns. The relative path has the law of the walk
started at the origin, so the expectation of `visitInd i m` is `retProb d m`, the probability that
the walk avoids the origin for `m` steps, and the expectation of `survInd i` is the escape
probability `escProb d`, independent of `i`. This file records the measurability, monotonicity,
and integral identities for these quantities, and the convergence of `retProb d m` to `escProb d`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The path relative to its position at time `n`. -/
def relPath (n : ℕ) (X : ℕ → Site d) : ℕ → Site d := fun k => X (n + k) - X n

/-- The event that a path avoids its starting point during its first `m` steps. -/
def noRet (d : ℕ) (m : ℕ) : Set (ℕ → Site d) := {Y | ∀ r : ℕ, 1 ≤ r → r ≤ m → Y r ≠ Y 0}

/-- The event that a path never returns to its starting point. -/
def noRetEver (d : ℕ) : Set (ℕ → Site d) := {Y | ∀ r : ℕ, 1 ≤ r → Y r ≠ Y 0}

/-- The relativization map `relPath n` is measurable. -/
theorem measurable_relPath (n : ℕ) : Measurable (relPath (d := d) n) :=
  measurable_pi_lambda _ fun k => (measurable_pi_apply (n + k)).sub (measurable_pi_apply n)

/-- Relativizing a walk path started at the origin at time `n` gives the walk path started at the
origin driven by the increments shifted by `n`. -/
theorem relPath_walkPath (n : ℕ) (ξ : ℕ → Site d) :
    relPath n (walkPath (0 : Site d) ξ) = walkPath (0 : Site d) (LatticeProb.shiftInc n ξ) := by
  funext k
  simp only [relPath, walkPath, LatticeProb.shiftInc, zero_add]
  rw [Finset.sum_range_add]
  abel

/-- Relativizing at time `n` preserves the walk law started at the origin, since it corresponds
to shifting the driving i.i.d. increments, which is measure preserving. -/
theorem measurePreserving_relPath [NeZero d] (n : ℕ) :
    MeasurePreserving (relPath (d := d) n) (walkLaw d 0) (walkLaw d 0) := by
  constructor
  · exact measurable_relPath n
  · have hbase : walkLaw d 0 = (LatticeProb.incPathLaw d).map (walkPath (0 : Site d)) := rfl
    rw [hbase, Measure.map_map (measurable_relPath n) (measurable_walkPath 0)]
    have hcomp : (relPath (d := d) n) ∘ (walkPath (0 : Site d))
        = (walkPath (0 : Site d)) ∘ (LatticeProb.shiftInc (d := d) n) := by
      funext ξ; exact relPath_walkPath n ξ
    rw [hcomp, ← Measure.map_map (measurable_walkPath 0) (LatticeProb.measurable_shiftInc n),
      (LatticeProb.measurePreserving_shiftInc d n).map_eq]

/-- The event `noRet d m` is measurable. -/
theorem measurableSet_noRet (m : ℕ) : MeasurableSet (noRet d m) := by
  have h : noRet d m
      = ⋂ r : ℕ, ⋂ _ : 1 ≤ r, ⋂ _ : r ≤ m, {Y : ℕ → Site d | Y r ≠ Y 0} := by
    ext Y; simp [noRet]
  rw [h]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_pi_apply r) (measurable_pi_apply 0)).compl

/-- The event `noRetEver d` is measurable. -/
theorem measurableSet_noRetEver : MeasurableSet (noRetEver d) := by
  have h : noRetEver d = ⋂ r : ℕ, ⋂ _ : 1 ≤ r, {Y : ℕ → Site d | Y r ≠ Y 0} := by
    ext Y; simp [noRetEver]
  rw [h]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ =>
      (measurableSet_eq_fun (measurable_pi_apply r) (measurable_pi_apply 0)).compl

/-- `noRet d` is antitone in `m`: avoiding the origin for longer is a stronger requirement, so
`noRet d m₂ ⊆ noRet d m₁` whenever `m₁ ≤ m₂`. -/
theorem noRet_antitone : Antitone (noRet d) := by
  intro m₁ m₂ hm Y hY r hr1 hr2
  exact hY r hr1 (le_trans hr2 hm)

/-- The intersection over all `m` of `noRet d m` is `noRetEver d`. -/
theorem iInter_noRet : (⋂ m : ℕ, noRet d m) = noRetEver d := by
  ext Y
  simp only [Set.mem_iInter, noRet, noRetEver, Set.mem_setOf_eq]
  exact ⟨fun h r hr1 => h r r hr1 le_rfl, fun h _ r hr1 _ => h r hr1⟩

/-- The walk law `walkLaw d x` is a probability measure. -/
instance instIsProbabilityMeasure_walkLaw [NeZero d] (x : Site d) :
    IsProbabilityMeasure (walkLaw d x) := by
  rw [show walkLaw d x = LatticeProb.siteWalkLaw d x from rfl]
  infer_instance

/-- `ρ_m = P_0(the walk avoids the origin at the times 1, …, m)`. -/
noncomputable def retProb (d : ℕ) (m : ℕ) : ℝ := (walkLaw d 0 (noRet d m)).toReal

/-- `ρ_∞ = P_0(the walk never returns to the origin)`. -/
noncomputable def escProb (d : ℕ) : ℝ := (walkLaw d 0 (noRetEver d)).toReal

/-- A path that never returns to the origin also avoids it for the first `m` steps. -/
theorem noRetEver_subset_noRet (m : ℕ) : noRetEver d ⊆ noRet d m := fun _ hY r hr1 _ => hY r hr1

/-- The escape probability `escProb d` is at most `retProb d m` for every `m`, since
`noRetEver d ⊆ noRet d m`. -/
theorem escProb_le_retProb [NeZero d] (m : ℕ) : escProb d ≤ retProb d m :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (noRetEver_subset_noRet m))

/-- The return probability `retProb d m` is at most `1`. -/
theorem retProb_le_one [NeZero d] (m : ℕ) : retProb d m ≤ 1 := by
  simpa [retProb] using ENNReal.toReal_mono (by finiteness) (prob_le_one (μ := walkLaw d 0))

/-- The escape probability `escProb d` is nonnegative. -/
theorem escProb_nonneg : 0 ≤ escProb d := ENNReal.toReal_nonneg

/-- The return probability `retProb d m` converges to the escape probability `escProb d` as
`m → ∞`, by continuity of measure along the decreasing sequence of events `noRet d m`. -/
theorem tendsto_retProb [NeZero d] :
    Tendsto (fun m => retProb d m - escProb d) atTop (nhds 0) := by
  have hmeas := tendsto_measure_iInter_atTop
      (μ := walkLaw d 0) (s := fun m => noRet (d := d) m)
      (fun m => (measurableSet_noRet m).nullMeasurableSet) noRet_antitone
      ⟨0, measure_ne_top _ _⟩
  rw [iInter_noRet] at hmeas
  have h2 : Tendsto (fun m => retProb d m) atTop (nhds (escProb d)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hmeas
  simpa using h2.sub_const (escProb d)

/-! ### The two indicators along a path -/

/-- The indicator that the walk avoids its position at time `i` during the next
`m` steps.  For `i ≤ j` and `m = j - i` this is the paper's `I_{i,j}`. -/
noncomputable def visitInd (i m : ℕ) (X : ℕ → Site d) : ℝ :=
  Set.indicator (noRet d m) (fun _ => (1 : ℝ)) (relPath i X)

/-- The indicator that the walk never returns to its position at time `i`.  This
is the paper's `I_i^∞`. -/
noncomputable def survInd (i : ℕ) (X : ℕ → Site d) : ℝ :=
  Set.indicator (noRetEver d) (fun _ => (1 : ℝ)) (relPath i X)

/-- Relativizing twice composes additively: relativizing at `i` and then at `k` is the same as
relativizing once at `i + k`. -/
theorem relPath_relPath {i k : ℕ} (X : ℕ → Site d) :
    relPath k (relPath i X) = relPath (i + k) X := by
  funext j
  simp only [relPath]
  rw [show i + (k + j) = i + k + j from (Nat.add_assoc i k j).symm]
  abel

/-- The preimage of `noRet d m` under `relPath 0` is `noRet d m` itself, since `relPath 0` shifts
a path by its own value at the origin without changing which coordinates avoid it. -/
theorem preimage_relPath_zero_noRet (m : ℕ) :
    relPath (d := d) 0 ⁻¹' noRet d m = noRet d m := by
  ext X
  simp only [Set.mem_preimage, noRet, Set.mem_setOf_eq, relPath, Nat.zero_add, sub_self]
  exact ⟨fun h r hr1 hr2 => sub_ne_zero.mp (h r hr1 hr2),
    fun h r hr1 hr2 => sub_ne_zero.mpr (h r hr1 hr2)⟩

/-- The preimage of `noRetEver d` under `relPath 0` is `noRetEver d` itself, by the same
argument as `preimage_relPath_zero_noRet`. -/
theorem preimage_relPath_zero_noRetEver :
    relPath (d := d) 0 ⁻¹' noRetEver d = noRetEver d := by
  ext X
  simp only [Set.mem_preimage, noRetEver, Set.mem_setOf_eq, relPath, Nat.zero_add, sub_self]
  exact ⟨fun h r hr1 => sub_ne_zero.mp (h r hr1), fun h r hr1 => sub_ne_zero.mpr (h r hr1)⟩

/-- Never returning to the origin implies avoiding it for the first `m` steps, so `survInd i X`
is at most `visitInd i m X` for every `m`. -/
theorem survInd_le_visitInd (i m : ℕ) (X : ℕ → Site d) : survInd i X ≤ visitInd i m X := by
  simp only [visitInd, survInd]
  by_cases h : relPath i X ∈ noRetEver d
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (noRetEver_subset_noRet m h)]
  · rw [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The indicator `visitInd i m X` is nonnegative. -/
theorem visitInd_nonneg (i m : ℕ) (X : ℕ → Site d) : 0 ≤ visitInd i m X :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The indicator `visitInd i m X` is at most one. -/
theorem visitInd_le_one (i m : ℕ) (X : ℕ → Site d) : visitInd i m X ≤ 1 := by
  simp only [visitInd]
  by_cases h : relPath i X ∈ noRet d m
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; norm_num

/-- The indicator `survInd i X` is nonnegative. -/
theorem survInd_nonneg (i : ℕ) (X : ℕ → Site d) : 0 ≤ survInd i X :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- The indicator `survInd i X` is at most one. -/
theorem survInd_le_one (i : ℕ) (X : ℕ → Site d) : survInd i X ≤ 1 := by
  simp only [survInd]
  by_cases h : relPath i X ∈ noRetEver d
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]; norm_num

/-- The indicator `visitInd i m` is a measurable function of the path. -/
theorem measurable_visitInd (i m : ℕ) : Measurable (visitInd (d := d) i m) :=
  (measurable_const.indicator (measurableSet_noRet m)).comp (measurable_relPath i)

/-- The indicator `survInd i` is a measurable function of the path. -/
theorem measurable_survInd (i : ℕ) : Measurable (survInd (d := d) i) :=
  (measurable_const.indicator measurableSet_noRetEver).comp (measurable_relPath i)

/-- The expectation of `visitInd i m` under the walk law started at the origin is `retProb d m`,
independent of `i`. -/
theorem integral_visitInd [NeZero d] (i m : ℕ) :
    ∫ X, visitInd i m X ∂(walkLaw d 0) = retProb d m := by
  have h1 : (fun X => visitInd (d := d) i m X)
      = Set.indicator (relPath (d := d) i ⁻¹' noRet d m) (fun _ => (1 : ℝ)) := by
    funext X
    simp only [visitInd, Set.indicator]
    rfl
  rw [h1]
  have h2 : MeasurableSet (relPath (d := d) i ⁻¹' noRet d m) :=
    (measurable_relPath i) (measurableSet_noRet m)
  rw [show (fun _ => (1:ℝ)) = (1 : (ℕ → Site d) → ℝ) from rfl, integral_indicator_one h2,
    measureReal_def,
    (measurePreserving_relPath i).measure_preimage (measurableSet_noRet m).nullMeasurableSet]
  rfl

/-- The expectation of `survInd i` under the walk law started at the origin is `escProb d`,
independent of `i`. -/
theorem integral_survInd [NeZero d] (i : ℕ) :
    ∫ X, survInd i X ∂(walkLaw d 0) = escProb d := by
  have h1 : (fun X => survInd (d := d) i X)
      = Set.indicator (relPath (d := d) i ⁻¹' noRetEver d) (fun _ => (1 : ℝ)) := by
    funext X
    simp only [survInd, Set.indicator]
    rfl
  rw [h1]
  have h2 : MeasurableSet (relPath (d := d) i ⁻¹' noRetEver d) :=
    (measurable_relPath i) measurableSet_noRetEver
  rw [show (fun _ => (1:ℝ)) = (1 : (ℕ → Site d) → ℝ) from rfl, integral_indicator_one h2,
    measureReal_def,
    (measurePreserving_relPath i).measure_preimage measurableSet_noRetEver.nullMeasurableSet]
  rfl

end Sandpile
