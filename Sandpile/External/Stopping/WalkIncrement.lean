import Sandpile.Walk
import LatticeProb.Walk.MaxDisp

/-!
# Displacement after a bounded stopping time

The maximal displacement estimate for simple random walk remains valid after a
bounded stopping time by the strong Markov property. This is the increment
estimate used in the Aldous tightness condition in Coquet and Toldo,
*Convergence of values in optimal stopping and convergence of optimal stopping
times*, Section 2.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- The paths with a displacement of at least `a` from their initial position
within `n` steps. -/
def largeIncrement {d : ℕ} (n : ℕ) (a : ℝ) : Set (ℕ → Site d) :=
  {X | ∃ k ≤ n, a ≤ ((LatticeProb.graphNorm (X k - X 0) : ℕ) : ℝ)}

private theorem measurableSet_incrementAt {d : ℕ} (k : ℕ) (a : ℝ) :
    MeasurableSet {X : ℕ → Site d |
      a ≤ ((LatticeProb.graphNorm (X k - X 0) : ℕ) : ℝ)} := by
  have hm : Measurable (LatticeProb.graphNorm (d := d)) := measurable_of_countable _
  have hc : Measurable (fun m : ℕ => (m : ℝ)) := measurable_of_countable _
  have hp : Measurable fun X : ℕ → Site d => X k - X 0 :=
    (measurable_pi_apply k).sub (measurable_pi_apply 0)
  exact measurableSet_le measurable_const (hc.comp (hm.comp hp))

/-- The large increment event depends only on finitely many positions. -/
theorem measurableSet_largeIncrement {d : ℕ} (n : ℕ) (a : ℝ) :
    MeasurableSet (largeIncrement (d := d) n a) := by
  have heq : largeIncrement (d := d) n a =
      ⋃ k ∈ Finset.range (n + 1), {X : ℕ → Site d |
        a ≤ ((LatticeProb.graphNorm (X k - X 0) : ℕ) : ℝ)} := by
    ext X
    simp only [largeIncrement, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range,
      exists_prop, Nat.lt_succ_iff]
  rw [heq]
  exact MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet
    (fun k _ => measurableSet_incrementAt k a)

/-- The large-increment probability has a Gaussian bound uniformly in the
starting site and in the bounded stopping time. -/
theorem exists_stopped_maxDisplacement_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N n : ℕ) (a : ℝ), 1 ≤ n → 1 ≤ a → ∀ (x : Site d)
        (τ : (ℕ → Site d) → ℕ), IsWalkStopping τ → (∀ X, τ X ≤ N) →
        walkLaw d x {X | ∃ k ≤ n, a ≤ ((LatticeProb.graphNorm (X (τ X + k) - X (τ X)) : ℕ) : ℝ)} ≤
          ENNReal.ofReal (C * Real.exp (-c * a ^ 2 / n)) := by
  classical
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, c, hC, hc, hb⟩ := LatticeProb.exists_maxDisp_bound d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro N n a hn ha x τ hτ hτN
  let : IsProbabilityMeasure (walkLaw d x) := by
    change IsProbabilityMeasure (LatticeProb.siteWalkLaw d x)
    infer_instance
  let S := largeIncrement (d := d) n a
  let F : (ℕ → Site d) → ℝ := S.indicator 1
  have hSm : MeasurableSet S := measurableSet_largeIncrement n a
  have hFm : Measurable F := measurable_const.indicator hSm
  have hFb : ∀ X, ‖F X‖ ≤ (1 : ℝ) := by
    intro X
    by_cases hX : X ∈ S <;> simp [F, hX]
  have hpath : ∀ y : Site d, LatticeProb.pathExpect d F y ≤
      C * Real.exp (-c * a ^ 2 / n) := by
    intro y
    let A : Set (ℕ → Site d) := {X | ∃ k ≤ n, a ≤ ((LatticeProb.graphNorm (X k - y) : ℕ) : ℝ)}
    have hAe : S =ᵐ[walkLaw d y] A := by
      have hstart : ∀ᵐ X ∂(walkLaw d y), X 0 = y := by
        have hm : MeasurableSet {X : ℕ → Site d | X 0 = y} := by
          change MeasurableSet ((fun X : ℕ → Site d => X 0) ⁻¹' {y})
          exact (measurable_pi_apply 0) (Set.to_countable _).measurableSet
        rw [show walkLaw d y = LatticeProb.siteWalkLaw d y from rfl,
          LatticeProb.siteWalkLaw_eq, ae_map_iff (LatticeProb.measurable_sitePath y).aemeasurable hm]
        exact Filter.Eventually.of_forall fun ξ => LatticeProb.sitePath_zero y ξ
      filter_upwards [hstart] with X hX
      simp only [S, largeIncrement, Set.mem_ofPred_eq]
      rw [hX]
      rfl
    have hSmeas := measurableSet_largeIncrement (d := d) n a
    have hprob := hb n a hn (by linarith) y
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
    have hQ : 0 ≤ C * Real.exp (-c * a ^ 2 / n) := by positivity
    rw [ENNReal.toReal_ofReal hQ] at hreal
    have heq : (walkLaw d y).real S = (walkLaw d y).real A := by
      simp only [measureReal_def]
      exact congrArg ENNReal.toReal (measure_congr hAe)
    change (∫ X, S.indicator (1 : (ℕ → Site d) → ℝ) X ∂walkLaw d y) ≤ _
    rw [integral_indicator_one hSmeas, heq, measureReal_def]
    exact hreal
  have hmark := LatticeProb.markov_stopping d N x τ hτ hτN F hFm hFb
    (CG := 1) (fun _ => (1 : ℝ)) (by intro X; simp) (by intros; rfl)
  have hshift : Measurable fun X : ℕ → Site d => LatticeProb.shiftPath (τ X) X := by
    refine Measurable.of_eval fun k => ?_
    apply LatticeProb.measurable_of_dependsUpTo (n := N + k)
    intro X Y hXY
    have ht := LatticeProb.dependsUpTo_of_isWalkStopping hτ hτN X Y
      (fun j hj => hXY j (by omega))
    change X (τ X + k) = Y (τ Y + k)
    rw [← ht]
    exact hXY _ (Nat.add_le_add_right (hτN X) k)
  have hevent : {X : ℕ → Site d | ∃ k ≤ n, a ≤ ((LatticeProb.graphNorm (X (τ X + k) - X (τ X)) : ℕ) : ℝ)} =
      (fun X => LatticeProb.shiftPath (τ X) X) ⁻¹' S := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, largeIncrement, LatticeProb.shiftPath,
      add_zero]
  have hm := hSm.preimage hshift
  have hcont : Integrable (fun X : ℕ → Site d => LatticeProb.pathExpect d F (X (τ X)))
      (walkLaw d x) := by
    have hmval : Measurable fun X : ℕ → Site d => X (τ X) := by
      simpa only [LatticeProb.shiftPath, add_zero] using hshift.eval (a := 0)
    have hm' := (LatticeProb.measurable_pathExpect d F).comp hmval
    apply Integrable.of_bound hm'.aestronglyMeasurable 1
    filter_upwards with X
    change ‖∫ Y, F Y ∂LatticeProb.siteWalkLaw d (X (τ X))‖ ≤ 1
    have hi := norm_integral_le_of_norm_le_const
      (μ := LatticeProb.siteWalkLaw d (X (τ X))) (Filter.Eventually.of_forall hFb)
    simpa using hi
  have hint : (∫ X, F (LatticeProb.shiftPath (τ X) X) ∂(walkLaw d x)) ≤
      C * Real.exp (-c * a ^ 2 / n) := by
    have hbound := integral_mono hcont (integrable_const (C * Real.exp (-c * a ^ 2 / n)))
      (fun X => hpath (X (τ X)))
    simp only [mul_one, show LatticeProb.siteWalkLaw d x = walkLaw d x from rfl] at hmark
    rw [hmark]
    simpa only [integral_const, probReal_univ, one_smul] using hbound
  rw [hevent]
  have hint' : (walkLaw d x).real ((fun X => LatticeProb.shiftPath (τ X) X) ⁻¹' S) ≤
      C * Real.exp (-c * a ^ 2 / n) := by
    convert hint using 1
    rw [← integral_indicator_one hm]
    congr 1
  rw [measureReal_def] at hint'
  calc walkLaw d x ((fun X => LatticeProb.shiftPath (τ X) X) ⁻¹' S)
      = ENNReal.ofReal ((walkLaw d x
          ((fun X => LatticeProb.shiftPath (τ X) X) ⁻¹' S)).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * a ^ 2 / n)) := ENNReal.ofReal_le_ofReal hint'

end Sandpile.External.Stopping
