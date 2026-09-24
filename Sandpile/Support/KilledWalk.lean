/-
The killed kernel is the walk's transition probability before the exit.

`sandpile.tex:3863-3877` builds `𝓑_{r,N}(z)` from `g_N^{Q(0,r)}` and reads it
against the odometer through the optimal-stopping representation, so the
definition of `killedKernel` has to be identified with the walk.  This file
proves that identification: pairing the killed kernel with a bounded field is
the expectation of the field at time `k` on the event that the walk has not left
the domain.  The induction runs on the LAST step, which is the recursion
`killedPair_succ_shift`, and the Markov property at the deterministic time `k`
is what supplies it.
-/
import Sandpile.Support.Killed
import Sandpile.Support.Localization
import Sandpile.Support.Smoothed
import Sandpile.Support.MembraneStopping

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

open scoped Classical in
/-- The indicator that the walk has stayed in `D` through time `k`. -/
noncomputable def pastIn (D : Set (Site d)) (k : ℕ) (X : ℕ → Site d) : ℝ :=
  if ∀ i ≤ k, X i ∈ D then 1 else 0

theorem pastIn_nonneg (D : Set (Site d)) (k : ℕ) (X : ℕ → Site d) : 0 ≤ pastIn D k X := by
  unfold pastIn; split <;> norm_num

theorem abs_pastIn_le_one (D : Set (Site d)) (k : ℕ) (X : ℕ → Site d) :
    |pastIn D k X| ≤ 1 := by
  unfold pastIn; split <;> norm_num

theorem pastIn_congr (D : Set (Site d)) (k : ℕ) {X Y : ℕ → Site d}
    (h : ∀ j ≤ k, X j = Y j) : pastIn D k X = pastIn D k Y := by
  unfold pastIn
  have hiff : (∀ i ≤ k, X i ∈ D) ↔ ∀ i ≤ k, Y i ∈ D := by
    constructor
    · intro hX i hi; rw [← h i hi]; exact hX i hi
    · intro hY i hi; rw [h i hi]; exact hY i hi
  by_cases hX : ∀ i ≤ k, X i ∈ D
  · rw [if_pos hX, if_pos (hiff.mp hX)]
  · rw [if_neg hX, if_neg (fun hc => hX (hiff.mpr hc))]

theorem measurable_pastIn (D : Set (Site d)) (k : ℕ) : Measurable (pastIn D k) :=
  measurable_of_dependsOn k _ fun _X _Y h => pastIn_congr D k h

/-- `pastIn` at time `k + 1` splits into the past through `k` and membership at
the new site. -/
theorem pastIn_succ (D : Set (Site d)) (k : ℕ) (X : ℕ → Site d) (f : Site d → ℝ) :
    pastIn D (k + 1) X * f (X (k + 1))
      = pastIn D k X * Set.indicator D f (X (k + 1)) := by
  classical
  unfold pastIn
  by_cases hk : ∀ i ≤ k, X i ∈ D
  · rw [if_pos hk]
    by_cases hnew : X (k + 1) ∈ D
    · have hall : ∀ i ≤ k + 1, X i ∈ D := by
        intro i hi
        rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact hk i (by omega)
        · have : i = k + 1 := by omega
          rw [this]; exact hnew
      rw [if_pos hall, Set.indicator_of_mem hnew]
    · have hnot : ¬ ∀ i ≤ k + 1, X i ∈ D := fun hc => hnew (hc (k + 1) le_rfl)
      rw [if_neg hnot, Set.indicator_of_notMem hnew]
      ring
  · have hnot : ¬ ∀ i ≤ k + 1, X i ∈ D := fun hc => hk fun i hi => hc i (by omega)
    rw [if_neg hnot, if_neg hk]
    ring

/-- One step of the walk averages the field. -/
theorem integral_eval_one (hd : 1 ≤ d) (z : Site d) (g : Site d → ℝ) {Mg : ℝ}
    (hg : ∀ y, |g y| ≤ Mg) : (∫ Y, g (Y 1) ∂(walkLaw d z)) = avg g z := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hmble : Measurable fun Y : ℕ → Site d => g (Y 1) :=
    Measurable.fun_comp (Measurable.of_discrete (f := g)) (measurable_pi_apply 1)
  rw [integral_walkLaw z hmble.aestronglyMeasurable]
  have hstep := walk_one_step hd z 0 (fun _ => (1 : ℝ)) g 1 Mg
    (fun _ => by norm_num) (fun y => hg y)
  simp only [one_mul] at hstep
  rw [hstep]
  simp [walkPath_zero]

/-- **The killed kernel is the walk's transition law before the exit.**  Pairing
`p_k^D(x, ·)` with a bounded field is the expectation of the field at time `k`
on the event that the walk has stayed in `D` through time `k`. -/
theorem integral_pastIn_mul (hd : 1 ≤ d) (D : Set (Site d)) :
    ∀ (k : ℕ) (x : Site d) (f : Site d → ℝ) (Mf : ℝ), (∀ y, |f y| ≤ Mf) →
      (∫ X, pastIn D k X * f (X k) ∂(walkLaw d x)) = killedPair D k f x := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  intro k
  induction k with
  | zero =>
      intro x f Mf _
      have hmble : Measurable fun X : ℕ → Site d => pastIn D 0 X * f (X 0) :=
        (measurable_pastIn D 0).mul
          (Measurable.fun_comp (Measurable.of_discrete (f := f)) (measurable_pi_apply 0))
      have hconst : ∀ X : ℕ → Site d, X 0 = x →
          pastIn D 0 X * f (X 0) = Set.indicator D f x := by
        intro X hX
        unfold pastIn
        by_cases hx : x ∈ D
        · rw [if_pos (by intro i hi; rw [show i = 0 by omega, hX]; exact hx), one_mul, hX,
            Set.indicator_of_mem hx]
        · rw [if_neg (fun hc => hx (by have h0 := hc 0 le_rfl; rwa [hX] at h0)), zero_mul,
            Set.indicator_of_notMem hx]
      rw [integral_walkLaw x hmble.aestronglyMeasurable,
        integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
          hconst (walkPath x ξ) (walkPath_zero x ξ)),
        killedPair_zero]
      simp
  | succ n ih =>
      intro x f Mf hf
      have hMf0 : (0 : ℝ) ≤ Mf := le_trans (abs_nonneg _) (hf 0)
      set g : Site d → ℝ := Set.indicator D f with hgdef
      have hgb : ∀ y, |g y| ≤ Mf := by
        intro y
        rw [hgdef]
        by_cases hy : y ∈ D
        · rw [Set.indicator_of_mem hy]; exact hf y
        · rw [Set.indicator_of_notMem hy, abs_zero]; exact hMf0
      have hrw : ∀ X : ℕ → Site d,
          pastIn D (n + 1) X * f (X (n + 1)) = pastIn D n X * g (X (n + 1)) :=
        fun X => pastIn_succ D n X f
      rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
      -- the Markov property at the deterministic time `n`
      set Φ : ℕ → (ℕ → Site d) → (ℕ → Site d) → ℝ :=
        fun j X Y => pastIn D j X * g (Y 1) with hΦdef
      have hΦm : ∀ j, Measurable (Function.uncurry (Φ j)) := by
        intro j
        have h1 : Measurable fun a : (ℕ → Site d) × (ℕ → Site d) => pastIn D j a.1 :=
          (measurable_pastIn D j).comp measurable_fst
        have h2 : Measurable fun a : (ℕ → Site d) × (ℕ → Site d) => g (a.2 1) :=
          Measurable.fun_comp (Measurable.of_discrete (f := g))
            ((measurable_pi_apply 1).comp measurable_snd)
        exact h1.mul h2
      have hΦb : ∀ (j : ℕ) (X Y : ℕ → Site d), ‖Φ j X Y‖ ≤ Mf := by
        intro j X Y
        rw [hΦdef]
        simp only [Real.norm_eq_abs, abs_mul]
        calc |pastIn D j X| * |g (Y 1)| ≤ 1 * Mf :=
              mul_le_mul (abs_pastIn_le_one D j X) (hgb (Y 1)) (abs_nonneg _) zero_le_one
          _ = Mf := one_mul Mf
      have hpast : ∀ (j : ℕ) (X X' Y : ℕ → Site d), (∀ i ≤ j, X i = X' i) →
          Φ j X Y = Φ j X' Y := by
        intro j X X' Y h
        rw [hΦdef]
        simp only
        rw [pastIn_congr D j h]
      have hmk := LatticeProb.markov_stopping_family d n x (fun _ => n)
        (isWalkStopping_const n) (fun _ => le_rfl) Φ hΦm hΦb hpast
      simp only [show ∀ y : Site d, LatticeProb.siteWalkLaw d y = walkLaw d y from
        fun _ => rfl] at hmk
      have hleft : ∀ X : ℕ → Site d,
          Φ n X (LatticeProb.shiftPath n X) = pastIn D n X * g (X (n + 1)) := by
        intro X
        rw [hΦdef]
        rfl
      have hright : ∀ X : ℕ → Site d,
          (∫ Y, Φ n X Y ∂(walkLaw d (X n))) = pastIn D n X * avg g (X n) := by
        intro X
        rw [hΦdef]
        simp only
        rw [MeasureTheory.integral_const_mul, integral_eval_one hd (X n) g hgb]
      rw [show (∫ X, pastIn D n X * g (X (n + 1)) ∂(walkLaw d x))
          = ∫ X, Φ n X (LatticeProb.shiftPath n X) ∂(walkLaw d x) from
        integral_congr_ae (Filter.Eventually.of_forall fun X => (hleft X).symm), hmk,
        integral_congr_ae (Filter.Eventually.of_forall hright),
        ih x (fun z => avg g z) Mf (fun y => abs_avg_le hd hgb y),
        ← killedPair_succ_shift]

/-- The pairing does not see the field outside the box the walk cannot leave. -/
theorem killedPair_trunc (D : Set (Site d)) {j N : ℕ} (hjN : j ≤ N) (x : Site d)
    (ζ : Site d → ℝ) :
    killedPair D j (trunc (boxFinset x N) ζ) x = killedPair D j ζ x := by
  classical
  rw [killedPair_eq_sum, killedPair_eq_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hmem : y ∈ boxFinset x N :=
    mem_boxFinset (le_trans (mem_boxFinset_iff.mp hy) hjN)
  rw [trunc_eq_of_mem hmem]

/-- **The killed Green field is the expectation of the scenery collected before
the exit.**  This is the identity that `𝓑_{r,N}` of `sandpile.tex:3858-3861`
rests on. -/
theorem integral_pastIn_sum (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ) (x : Site d)
    (ζ : Site d → ℝ) :
    (∫ X, ∑ j ∈ Finset.range N, pastIn D j X * ζ (X j) ∂(walkLaw d x))
      = killedGreenPair D N ζ x := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  set s : Finset (Site d) := boxFinset x N with hsdef
  obtain ⟨M, hM⟩ := exists_bound_trunc s ζ
  have hmble : ∀ j : ℕ, Measurable fun X : ℕ → Site d => pastIn D j X * trunc s ζ (X j) :=
    fun j => (measurable_pastIn D j).mul
      (Measurable.fun_comp (Measurable.of_discrete (f := trunc s ζ)) (measurable_pi_apply j))
  have hint : ∀ j : ℕ,
      Integrable (fun X : ℕ → Site d => pastIn D j X * trunc s ζ (X j)) (walkLaw d x) := by
    intro j
    refine (integrable_const M).mono' (hmble j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |pastIn D j X| * |trunc s ζ (X j)| ≤ 1 * M :=
          mul_le_mul (abs_pastIn_le_one D j X) (hM _) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hae : (fun X : ℕ → Site d => ∑ j ∈ Finset.range N, pastIn D j X * ζ (X j))
      =ᵐ[walkLaw d x] fun X => ∑ j ∈ Finset.range N, pastIn D j X * trunc s ζ (X j) := by
    filter_upwards [ae_boxDist_walk hd x] with X hX
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjN : j < N := Finset.mem_range.mp hj
    have hmem : X j ∈ s := mem_boxFinset (le_trans (hX j) (le_of_lt hjN))
    rw [trunc_eq_of_mem hmem]
  rw [integral_congr_ae hae, integral_finsetSum _ fun j _ => hint j,
    killedGreenPair_eq_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j < N := Finset.mem_range.mp hj
  rw [integral_pastIn_mul hd D j x (trunc s ζ) M hM, hsdef,
    killedPair_trunc D (le_of_lt hjN) x ζ]

/-- The same identity with the scenery sum stopped at the exit, which is the
form `lem:localization-killing` writes it in. -/
theorem integral_stoppedScenery_killed (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (x : Site d) (ζ : Site d → ℝ) :
    (∫ X, sceneryPartialSum ζ (stopBeforeExit D N (fun _ => N) X) X ∂(walkLaw d x))
      = killedGreenPair D N ζ x := by
  classical
  rw [← integral_pastIn_sum hd D N x ζ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show sceneryPartialSum ζ (stopBeforeExit D N (fun _ => N) X) X
      = ∑ j ∈ Finset.range N, pastIn D j X * ζ (X j)
  rw [← localizedSum_eq D N ζ (fun _ => le_rfl) X]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold pastIn
  by_cases hj : ∀ i ≤ j, X i ∈ D
  · rw [Set.indicator_of_mem (show j ∈ {j : ℕ | ∀ i ≤ j, X i ∈ D} from hj), if_pos hj,
      one_mul]
  · rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | ∀ i ≤ j, X i ∈ D} from hj), if_neg hj,
      zero_mul]

end Sandpile
