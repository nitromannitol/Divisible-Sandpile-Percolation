import Sandpile.Support.Membrane

/-!
# The one-step Markov property of the walk

Towards the Markov property of the walk of `Sandpile/Walk.lean`.

The optimal-stopping statements of `sandpile.tex` (`thm:RW`,
`lem:difference-representation`, `lem:localization-killing`) all rest on one
identity: for a bounded stopping time `τ ≤ t`,

  `E_x[∑_{j<τ} ζ(X_j) + V_{t-τ}(X_τ)] = V_t(x)`.

Written out, `M_n := ∑_{j<n} ζ(X_j) + V_{t-n}(X_n)` and the membrane recursion
`V_{m+1} = ζ + P V_m` give

  `M_{n+1} - M_n = V_{t-n-1}(X_{n+1}) - P V_{t-n-1}(X_n)`,

so the whole identity follows by summation over `n < t` from the ONE-STEP Markov
property: for a set of paths `A` determined by the first `n + 1` positions and a
finitely supported `f`,

  `E_x[1_A · f(X_{n+1})] = E_x[1_A · Pf(X_n)]`.

This file proves that one-step property, `walk_one_step`, and the pieces it is
built from:

- `measurable_walkPath`, so that path space and increment space may be exchanged;
- `isProbabilityMeasure_stepLaw`, the step law has total mass one;
- `integral_stepLaw`, that `∫ f(y + e) dstepLaw(e) = Pf(y)`, which is the whole
  content of the operator `P`;
- `integral_walkLaw`, the change of variables itself;
- `indepFun_prefix_step`, that the first `n` increments are independent of the
  `n`-th, from Mathlib's `iIndepFun_infinitePi` and `iIndepFun.indepFun_finset`;
- `integral_prefix_step`, Fubini for that split.

Note that the FULL strong Markov property is never needed.  A bounded stopping
time is handled by summing over the finitely many times it can take, and each
term uses only the one-step property at a deterministic time.

`walk_one_step` asks for a bounded field.  The membrane field is not bounded on
all of `ℤ^d`, but the walk at time `n` is confined to the box of radius `n` about
its start, so replacing the field by its truncation to that box changes neither
side; that truncation is the remaining step towards
`lem:difference-representation` and `lem:localization-killing`, together with the
observation that a stopping time bounded by `t` factors through the first `t`
increments.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- `walkPath x`, the walk started at `x` as a function of its increment sequence, is measurable:
each coordinate is a finite sum of measurable coordinate projections. -/
theorem measurable_walkPath (x : Site d) : Measurable (walkPath x) := by
  refine measurable_pi_lambda _ fun k => ?_
  unfold walkPath
  fun_prop

/-- The step law `stepLaw d`, the uniform distribution on the `2d` unit vectors, is a probability
measure: its total mass `d · (1 + 1) / (2d)` simplifies to `1`. -/
theorem isProbabilityMeasure_stepLaw (hd : 1 ≤ d) :
    IsProbabilityMeasure (stepLaw d) := by
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr (by omega : d ≠ 0)
  constructor
  unfold stepLaw LatticeProb.instructionLaw
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_add,
    Pi.add_apply, measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, nsmul_eq_mul]
  have hmul : (d : ℝ≥0∞) * (1 + 1) = 2 * (d : ℝ≥0∞) := by ring
  rw [hmul, ENNReal.inv_mul_cancel (mul_ne_zero two_ne_zero hd0) (by finiteness)]

/-- Integration against the step law is the finite average over the `2d`
neighbours of the origin. -/
theorem integral_stepLaw_apply (g : Site d → ℝ) :
    ∫ e, g e ∂(stepLaw d) = (∑ i : Fin d, (g (unit i) + g (-unit i))) / (2 * d) := by
  have hint : ∀ i : Fin d, Integrable g
      (Measure.dirac ((0 : Site d) + unit i) + Measure.dirac ((0 : Site d) - unit i)) := by
    intro i
    exact (integrable_add_measure).mpr
      ⟨integrable_dirac (by finiteness), integrable_dirac (by finiteness)⟩
  unfold stepLaw LatticeProb.instructionLaw
  rw [integral_smul_measure, integral_finsetSum_measure fun i _ => hint i]
  have hterm : ∀ i : Fin d,
      ∫ e, g e ∂(Measure.dirac ((0 : Site d) + unit i) + Measure.dirac ((0 : Site d) - unit i))
        = g (unit i) + g (-unit i) := by
    intro i
    rw [integral_add_measure (integrable_dirac (by finiteness))
      (integrable_dirac (by finiteness)), integral_dirac, integral_dirac]
    simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, smul_eq_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  rw [← div_eq_inv_mul]

/-- The step law integrates a field into its neighbour average: this is the whole
content of the operator `P`. -/
theorem integral_stepLaw (f : Site d → ℝ) (y : Site d) :
    ∫ e, f (y + e) ∂(stepLaw d) = avg f y := by
  rw [integral_stepLaw_apply (fun e => f (y + e))]
  unfold avg LatticeProb.walkOp nbrSum
  simp [sub_eq_add_neg]

/-- Change of variables from path space to increment space. -/
theorem integral_walkLaw (x : Site d) {F : (ℕ → Site d) → ℝ}
    (hF : AEStronglyMeasurable F (walkLaw d x)) :
    ∫ X, F X ∂(walkLaw d x) =
      ∫ ξ, F (walkPath x ξ) ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  unfold walkLaw
  exact integral_map (measurable_walkPath x).aemeasurable hF

/-- Under the increment law, the first `n` increments are independent of the
`n`-th.  This is the probabilistic input to the one-step Markov property; the
rest of that property is Fubini for this split together with `integral_stepLaw`. -/
theorem indepFun_prefix_step (hd : 1 ≤ d) (n : ℕ) :
    IndepFun (fun ξ : ℕ → Site d => (Finset.range n).restrict ξ)
      (fun ξ : ℕ → Site d => ξ n)
      (Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hcoord : iIndepFun (fun (i : ℕ) (ξ : ℕ → Site d) => ξ i)
      (Measure.infinitePi fun _ : ℕ => stepLaw d) :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (ω : Site d) => ω) fun _ => measurable_id
  have hdisj : Disjoint (Finset.range n) ({n} : Finset ℕ) := by
    simp [Finset.disjoint_singleton_right]
  have h := hcoord.indepFun_finset (Finset.range n) {n} hdisj fun i => measurable_pi_apply i
  exact h.comp measurable_id (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ :
    ({n} : Finset ℕ)))

/-- Fubini for the split of the increment law into the first `n` increments and
the `n`-th: a bounded functional of the pair may be integrated in the `n`-th
increment first, against the step law. -/
theorem integral_prefix_step (hd : 1 ≤ d) (n : ℕ)
    (Ψ : (↥(Finset.range n) → Site d) → Site d → ℝ) (M : ℝ)
    (hΨ : ∀ u e, |Ψ u e| ≤ M) :
    ∫ ξ, Ψ ((Finset.range n).restrict ξ) (ξ n)
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d)
      = ∫ ξ, (∫ e, Ψ ((Finset.range n).restrict ξ) e ∂(stepLaw d))
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  set P : Measure (ℕ → Site d) := Measure.infinitePi fun _ : ℕ => stepLaw d with hP
  have hpre : Measurable fun ξ : ℕ → Site d => (Finset.range n).restrict ξ :=
    Finset.measurable_restrict _
  have hev : Measurable fun ξ : ℕ → Site d => ξ n := measurable_pi_apply n
  have hunc : Measurable (Function.uncurry Ψ) := measurable_of_countable _
  have hpair : P.map (fun ξ => ((Finset.range n).restrict ξ, ξ n))
      = (P.map fun ξ => (Finset.range n).restrict ξ).prod (P.map fun ξ => ξ n) :=
    (indepFun_prefix_step hd n).map_prod_eq_prod_map_map hpre.aemeasurable hev.aemeasurable
  have heval : P.map (fun ξ : ℕ → Site d => ξ n) = stepLaw d :=
    Measure.infinitePi_map_eval _ n
  haveI : IsProbabilityMeasure (P.map fun ξ : ℕ → Site d => (Finset.range n).restrict ξ) :=
    Measure.isProbabilityMeasure_map hpre.aemeasurable
  have hint : Integrable (Function.uncurry Ψ)
      ((P.map fun ξ => (Finset.range n).restrict ξ).prod (stepLaw d)) := by
    refine (integrable_const M).mono' hunc.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro p
    simpa [Function.uncurry] using hΨ p.1 p.2
  have hL : ∫ ξ, Ψ ((Finset.range n).restrict ξ) (ξ n) ∂P
      = ∫ p, Function.uncurry Ψ p
        ∂((P.map fun ξ => (Finset.range n).restrict ξ).prod (stepLaw d)) := by
    rw [← heval, ← hpair, integral_map (by fun_prop) hunc.aestronglyMeasurable]
    rfl
  have hR : ∫ ξ, (∫ e, Ψ ((Finset.range n).restrict ξ) e ∂(stepLaw d)) ∂P
      = ∫ u, (∫ e, Ψ u e ∂(stepLaw d))
        ∂(P.map fun ξ => (Finset.range n).restrict ξ) := by
    rw [integral_map hpre.aemeasurable]
    exact (measurable_of_countable _).aestronglyMeasurable
  rw [hL, hR, integral_prod _ hint]
  rfl

/-- The position at time `n`, as a function of the first `n` increments. -/
def prefixPos (x : Site d) (n : ℕ) (u : ↥(Finset.range n) → Site d) : Site d :=
  x + ∑ j ∈ (Finset.range n).attach, u j

/-- The walk's position at time `n` depends on the increment sequence `ξ` only through its
restriction to the first `n` indices, matching `prefixPos`. -/
theorem walkPath_eq_prefixPos (x : Site d) (n : ℕ) (ξ : ℕ → Site d) :
    walkPath x ξ n = prefixPos x n ((Finset.range n).restrict ξ) := by
  unfold walkPath prefixPos
  congr 1
  exact (Finset.sum_attach (Finset.range n) ξ).symm

/-- The one-step Markov property of the walk: a bounded functional of the first
`n` increments, multiplied by a bounded field read at time `n + 1`, integrates to
the same functional multiplied by the neighbour average of the field read at time
`n`.  This is the identity every optimal-stopping statement of the paper rests
on; a bounded stopping time needs no more than this, by summation. -/
theorem walk_one_step (hd : 1 ≤ d) (x : Site d) (n : ℕ)
    (G : (↥(Finset.range n) → Site d) → ℝ) (f : Site d → ℝ) (Mg Mf : ℝ)
    (hG : ∀ u, |G u| ≤ Mg) (hf : ∀ y, |f y| ≤ Mf) :
    ∫ ξ, G ((Finset.range n).restrict ξ) * f (walkPath x ξ (n + 1))
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d)
      = ∫ ξ, G ((Finset.range n).restrict ξ) * avg f (walkPath x ξ n)
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hsucc : ∀ ξ : ℕ → Site d,
      walkPath x ξ (n + 1) = prefixPos x n ((Finset.range n).restrict ξ) + ξ n := by
    intro ξ
    rw [← walkPath_eq_prefixPos]
    unfold walkPath
    rw [Finset.sum_range_succ, ← add_assoc]
  have hbound : ∀ (u : ↥(Finset.range n) → Site d) (e : Site d),
      |G u * f (prefixPos x n u + e)| ≤ Mg * Mf := by
    intro u e
    rw [abs_mul]
    exact mul_le_mul (hG u) (hf _) (abs_nonneg _) (le_trans (abs_nonneg _) (hG u))
  have key := integral_prefix_step hd n
    (fun u e => G u * f (prefixPos x n u + e)) (Mg * Mf) hbound
  calc ∫ ξ, G ((Finset.range n).restrict ξ) * f (walkPath x ξ (n + 1))
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d)
      = ∫ ξ, G ((Finset.range n).restrict ξ) *
          f (prefixPos x n ((Finset.range n).restrict ξ) + ξ n)
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
          simp only []; rw [hsucc ξ])
    _ = ∫ ξ, (∫ e, G ((Finset.range n).restrict ξ) *
          f (prefixPos x n ((Finset.range n).restrict ξ) + e) ∂(stepLaw d))
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := key
    _ = ∫ ξ, G ((Finset.range n).restrict ξ) * avg f (walkPath x ξ n)
          ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only []
        rw [integral_const_mul, integral_stepLaw, walkPath_eq_prefixPos]

/-- The walk started at `x` is at `x` at time `0`, regardless of the increment sequence. -/
theorem walkPath_zero (x : Site d) (ξ : ℕ → Site d) : walkPath x ξ 0 = x := by
  simp [walkPath]

/-- A stopping time is decided by the path up to the time in question: whether it
has already occurred by time `n` depends only on the first `n + 1` positions.
This is what makes the indicator of `{n < τ}` an admissible past functional in
`walk_one_step`. -/
theorem IsWalkStopping.le_iff {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    (n : ℕ) {X Y : ℕ → Site d} (h : ∀ j ≤ n, X j = Y j) : τ X ≤ n ↔ τ Y ≤ n := by
  constructor
  · intro hX
    have := hτ (τ X) X Y (fun j hj => h j (hj.trans hX)) rfl
    omega
  · intro hY
    have := hτ (τ Y) Y X (fun j hj => (h j (hj.trans hY)).symm) rfl
    omega

/-! ### Confinement of the walk

`walk_one_step` asks for a bounded field, and the membrane field is not bounded
on `ℤ^d`.  What repairs this is that the walk is confined: at time `n` it lies in
the box of radius `n` about its start, for almost every increment sequence.  A
field may therefore be replaced by its truncation to a box, which is bounded
because the box is finite. -/

/-- Translating by a vector of box-norm at most one moves the box distance by at
most one. -/
theorem boxDist_add_le_of_unit (x y u : Site d) (hu : ∀ j, (u j).natAbs ≤ 1) :
    boxDist x (y + u) ≤ boxDist x y + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hj : (x j - y j).natAbs ≤ boxDist x y :=
    Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ j)
  have hj' := hu j
  show (x j - (y + u) j).natAbs ≤ boxDist x y + 1
  simp only [Pi.add_apply]
  omega

/-- Every coordinate of a unit vector `unit i` has absolute value at most one: it is `1` at
coordinate `i` and `0` elsewhere. -/
theorem natAbs_unit_le (i j : Fin d) : ((unit i : Site d) j).natAbs ≤ 1 := by
  by_cases h : i = j
  · simp [unit, h]
  · simp [unit, Pi.single_eq_of_ne (Ne.symm h)]

/-- The `2d` steps the walk can take. -/
def stepSet (d : ℕ) : Set (Site d) := {v | ∃ i : Fin d, v = unit i ∨ v = -unit i}

/-- The step law gives zero mass to the complement of `stepSet d`: it is a finite sum of Dirac
masses each already concentrated on `stepSet d`. -/
theorem stepLaw_stepSet_compl (d : ℕ) : stepLaw d (stepSet d)ᶜ = 0 := by
  unfold stepLaw LatticeProb.instructionLaw
  simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, Measure.coe_add,
    Pi.add_apply, smul_eq_mul]
  have hz : ∀ i : Fin d, Measure.dirac ((0 : Site d) + unit i) (stepSet d)ᶜ
      + Measure.dirac ((0 : Site d) - unit i) (stepSet d)ᶜ = 0 := by
    intro i
    rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
      Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
    have h1 : (0 : Site d) + unit i ∉ (stepSet d)ᶜ := by
      simp only [Set.mem_compl_iff, not_not]
      exact ⟨i, Or.inl (by simp)⟩
    have h2 : (0 : Site d) - unit i ∉ (stepSet d)ᶜ := by
      simp only [Set.mem_compl_iff, not_not]
      exact ⟨i, Or.inr (by simp)⟩
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hz i]
  simp

/-- Almost every increment sequence takes its values in the step set. -/
theorem ae_mem_stepSet (hd : 1 ≤ d) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d), ∀ j : ℕ, ξ j ∈ stepSet d := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  rw [ae_iff]
  have hcover : {ξ : ℕ → Site d | ¬ ∀ j : ℕ, ξ j ∈ stepSet d}
      ⊆ ⋃ j : ℕ, {ξ : ℕ → Site d | ξ j ∈ (stepSet d)ᶜ} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq, not_forall] at hξ
    obtain ⟨j, hj⟩ := hξ
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine measure_mono_null hcover (measure_iUnion_null fun j => ?_)
  show (Measure.infinitePi fun _ : ℕ => stepLaw d)
      ((fun ξ : ℕ → Site d => ξ j) ⁻¹' (stepSet d)ᶜ) = 0
  rw [← Measure.map_apply (measurable_pi_apply j) (Set.to_countable _).measurableSet,
    Measure.infinitePi_map_eval, stepLaw_stepSet_compl]

/-- The walk is confined: at time `n` it lies in the box of radius `n` about its
start, for almost every increment sequence. -/
theorem ae_boxDist_walkPath (hd : 1 ≤ d) (x : Site d) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d),
      ∀ n : ℕ, boxDist x (walkPath x ξ n) ≤ n := by
  filter_upwards [ae_mem_stepSet hd] with ξ hξ n
  induction n with
  | zero => simp [walkPath_zero, boxDist_self]
  | succ m ih =>
      have hstep : walkPath x ξ (m + 1) = walkPath x ξ m + ξ m := by
        unfold walkPath; rw [Finset.sum_range_succ, ← add_assoc]
      obtain ⟨i, hi | hi⟩ := hξ m
      · rw [hstep, hi]
        exact le_trans (boxDist_add_le_of_unit x _ _ fun j => natAbs_unit_le i j) (by omega)
      · rw [hstep, hi]
        refine le_trans (boxDist_add_le_of_unit x _ _ fun j => ?_) (by omega)
        have := natAbs_unit_le (d := d) i j
        simp only [Pi.neg_apply, Int.natAbs_neg]
        exact this

/-- The confinement bound `ae_boxDist_walkPath` specialized to a single fixed time `n`. -/
theorem boxDist_walkPath_le (hd : 1 ≤ d) (x : Site d) (n : ℕ) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d),
      boxDist x (walkPath x ξ n) ≤ n := by
  filter_upwards [ae_boxDist_walkPath hd x] with ξ hξ using hξ n

end Sandpile
