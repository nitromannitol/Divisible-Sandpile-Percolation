import Sandpile.External.GreenBoundsHighProved
import Sandpile.Support.LinIntersect
import Sandpile.Support.Localization

/-!
# The second intersection moment is proved

The second intersection moment `Sandpile.External.IntersectionSecondMoment`,
Lawler, *Intersections of Random Walks*, proof of Theorem 3.3.2 (pp. 95-97),
is no longer assumed.

The paper's proof (`sandpile.tex:1331-1336`) splits the second moment of the
intersection count of two independent walks into the four relative orderings
of the two intersection times, bounds the two "matching" orderings by the
first intersection moment times the expected number of intersections of two
walks started together (finite by Lawler Proposition 3.2.1), and bounds each
"crossed" ordering by the Green-function sum already proved unconditionally in
`Sandpile.External.GreenBoundsHighProved`.

The route taken here factors the intersection count through the local times,
exactly as `Sandpile.Support.LinIntersect` already does for the first moment:
`I(X,Y) = ∑_z L_X(z) L_Y(z)`, so
`I(X,Y)^2 = ∑_{z,w} [L_X(z)L_X(w)] · [L_Y(z)L_Y(w)]`.
Independence of `X` and `Y` turns the double expectation into a product,
`E_x E_y[I(X,Y)^2] = ∑_{z,w} E_x[L_X(z)L_X(w)] · E_y[L_Y(z)L_Y(w)]`, and the
one remaining walk-level fact is the second moment of the local times of a
SINGLE walk at two sites, `E_x[L_X(z)L_X(w)]`. Splitting the pair of visit
times `(i,i')` by `i ≤ i'` or `i' ≤ i` (a cover, not a partition, which is
enough for an upper bound) and using the two-time joint law of the walk -
`P_x(X_i=z,X_{i+m}=w) = p_i(x,z)p_m(z,w)`, the ordinary Markov property at a
deterministic time, `LatticeProb.Walk.Markov.markov_fixed` - gives
`E_x[L_X(z)L_X(w)] ≤ G(x,z)G(z,w) + G(x,w)G(z,w)`.

Substituting this bound for both walks and expanding the product gives four
terms; by the symmetry `z ↔ w` two of them coincide with `M · ∑_z G(x,z)G(y,z)`
(`M := ∑_w G(0,w)^2 < ∞`, the same finite quantity as Lawler's Proposition
3.2.1, by `Sandpile.External.GreenBoundsHigh`'s square-summability clause and
translation invariance of the Green function) and the other two coincide with
`∑_{z,w} G(x,z)G(z,w)^2G(y,w)`, the crossed-ordering sum bounded directly by
`Sandpile.External.GreenBoundsHigh`. No new external input is used: every
ingredient is either already in `Sandpile.Support.LinIntersect` or is the
ordinary (not strong) Markov property of the walk at a fixed time, already
proved in the shared library for the optimal-stopping development.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### A reindexing helper for `ℝ≥0∞`-valued sums -/

/-- Summing a `ℝ≥0∞`-valued family over the tail `{i' : i ≤ i'}` is summing the
family shifted by `i`. -/
theorem tsum_ite_ge_eq_shift (i : ℕ) (g : ℕ → ℝ≥0∞) :
    (∑' i' : ℕ, if i ≤ i' then g i' else 0) = ∑' n : ℕ, g (i + n) := by
  classical
  have hind : (fun i' : ℕ => if i ≤ i' then g i' else 0)
      = {i' : ℕ | i ≤ i'}.indicator g := by
    funext i'
    by_cases h : i ≤ i' <;> simp [Set.indicator, h]
  rw [hind, ← tsum_subtype {i' : ℕ | i ≤ i'} g]
  let e : ℕ ≃ {i' : ℕ // i ≤ i'} :=
    { toFun := fun n => ⟨i + n, Nat.le_add_right i n⟩
      invFun := fun q => (q : ℕ) - i
      left_inv := fun n => by simp
      right_inv := fun q => by
        obtain ⟨i', hi'⟩ := q
        simp only [Subtype.mk.injEq]
        omega }
  exact (Equiv.tsum_eq e (fun q : {i' : ℕ // i ≤ i'} => g (q : ℕ))).symm

/-- The conjunction of two coordinate cylinders is measurable, stated in the
`setOf`-and shape that the rest of this file needs to match syntactically. -/
theorem measurableSet_path_eq_and (i : ℕ) (z : Site d) (i' : ℕ) (w : Site d) :
    MeasurableSet {X : ℕ → Site d | X i = z ∧ X i' = w} :=
  (measurableSet_path_eq i z).inter (measurableSet_path_eq i' w)

/-! ### The two-time joint law of a single walk -/

/-- **The two-time joint law of the walk.**  `P_x(X_i=z, X_{i+m}=w) =
p_i(x,z)p_m(z,w)`, the ordinary Markov property of simple random walk at the
deterministic time `i`. -/
theorem walkLaw_apply_two_site [NeZero d] (hd : 1 ≤ d) (x z w : Site d) (i m : ℕ) :
    (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X (i + m) = w}
      = ENNReal.ofReal (heatKernel d i x z) * ENNReal.ofReal (heatKernel d m z w) := by
  classical
  set F : (ℕ → Site d) → ℝ := fun Y => if Y m = w then (1 : ℝ) else 0 with hFdef
  set H : (ℕ → Site d) → ℝ := fun X => if X i = z then (1 : ℝ) else 0 with hHdef
  have hFeq : F = Set.indicator {Y : ℕ → Site d | Y m = w} (fun _ => (1 : ℝ)) := by
    funext Y; rw [hFdef]; by_cases h : Y m = w <;> simp [h, Set.indicator]
  have hHeq : H = Set.indicator {X : ℕ → Site d | X i = z} (fun _ => (1 : ℝ)) := by
    funext X; rw [hHdef]; by_cases h : X i = z <;> simp [h, Set.indicator]
  have hFm : Measurable F := by
    rw [hFeq]; exact measurable_const.indicator (measurableSet_path_eq m w)
  have hHm : Measurable H := by
    rw [hHeq]; exact measurable_const.indicator (measurableSet_path_eq i z)
  have hFb : ∀ Y, ‖F Y‖ ≤ (1 : ℝ) := by
    intro Y; rw [hFdef]; dsimp only; split_ifs <;> simp
  have hHb : ∀ X, ‖H X‖ ≤ (1 : ℝ) := by
    intro X; rw [hHdef]; dsimp only; split_ifs <;> simp
  have hHdep : LatticeProb.DependsUpTo i H := by
    intro X Y hXY
    rw [hHdef]
    dsimp only
    rw [hXY i le_rfl]
  have hmk := LatticeProb.markov_fixed d i x F hFm hFb H hHb hHdep
  rw [show LatticeProb.siteWalkLaw d x = walkLaw d x from (walkLaw_eq_siteWalkLaw d x).symm] at hmk
  -- Identify both sides of `hmk` with real integrals of indicator products.
  have hLHS : ∀ X : ℕ → Site d,
      F (LatticeProb.shiftPath i X) * H X
        = Set.indicator {X : ℕ → Site d | X i = z ∧ X (i + m) = w} (fun _ => (1 : ℝ)) X := by
    intro X
    rw [hFdef, hHdef]
    dsimp only [LatticeProb.shiftPath]
    by_cases h1 : X i = z <;> by_cases h2 : X (i + m) = w <;>
      simp [h1, h2, Set.indicator, Set.mem_setOf_eq]
  have hpathExpect : ∀ v : Site d, LatticeProb.pathExpect d F v = heatKernel d m v w := by
    intro v
    rw [LatticeProb.pathExpect, hFdef]
    dsimp only
    have heq : (fun Y : ℕ → Site d => if Y m = w then (1 : ℝ) else 0)
        = Set.indicator {Y : ℕ → Site d | Y m = w} (fun _ => (1 : ℝ)) := by
      funext Y; by_cases h : Y m = w <;> simp [h, Set.indicator]
    rw [heq, show LatticeProb.siteWalkLaw d v = walkLaw d v from (walkLaw_eq_siteWalkLaw d v).symm,
      integral_indicator_const (μ := walkLaw d v) (1 : ℝ) (measurableSet_path_eq m w),
      smul_eq_mul, mul_one, measureReal_def, walkLaw_apply_site hd v m w,
      ENNReal.toReal_ofReal (heatKernel_nonneg m v w)]
  have hRHS : ∀ X : ℕ → Site d,
      LatticeProb.pathExpect d F (X i) * H X
        = heatKernel d m z w * Set.indicator {X : ℕ → Site d | X i = z} (fun _ => (1 : ℝ)) X := by
    intro X
    rw [hpathExpect, hHdef]
    dsimp only
    by_cases h : X i = z <;> simp [h, Set.indicator, Set.mem_setOf_eq]
  rw [funext hLHS, funext hRHS] at hmk
  rw [integral_const_mul] at hmk
  have hint1 : ∫ X, Set.indicator {X : ℕ → Site d | X i = z ∧ X (i + m) = w} (fun _ => (1 : ℝ)) X
      ∂(walkLaw d x) = (walkLaw d x).real {X : ℕ → Site d | X i = z ∧ X (i + m) = w} := by
    rw [integral_indicator_const (μ := walkLaw d x) (1 : ℝ)
        (measurableSet_path_eq_and i z (i + m) w),
      smul_eq_mul, mul_one]
  have hint2 : ∫ X, Set.indicator {X : ℕ → Site d | X i = z} (fun _ => (1 : ℝ)) X
      ∂(walkLaw d x) = heatKernel d i x z := by
    rw [integral_indicator_const (μ := walkLaw d x) (1 : ℝ) (measurableSet_path_eq i z),
      smul_eq_mul, mul_one, measureReal_def, walkLaw_apply_site hd x i z,
      ENNReal.toReal_ofReal (heatKernel_nonneg i x z)]
  rw [hint1, hint2] at hmk
  rw [measureReal_def] at hmk
  have hne : (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X (i + m) = w} ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hne, hmk, ENNReal.ofReal_mul (heatKernel_nonneg m z w)]
  ring

/-! ### The second moment of the local times of a single walk -/

/-- **The single-walk two-site local-time bound.**  Covering the pairs of
visit times by `i ≤ i'` and `i' ≤ i` and applying the two-time joint law to
each cover set. -/
theorem lintegral_localTime_mul_le [NeZero d] (hd : 3 ≤ d) (x z w : Site d) :
    ∫⁻ X, localTime z X * localTime w X ∂(walkLaw d x)
      ≤ ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d z w)
        + ENNReal.ofReal (green d x w) * ENNReal.ofReal (green d z w) := by
  classical
  have hP : ∀ i i' : ℕ,
      (∫⁻ X, (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0)
        ∂(walkLaw d x))
        = (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} := by
    intro i i'
    have heq : (fun X : ℕ → Site d =>
        (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0))
        = Set.indicator {X : ℕ → Site d | X i = z ∧ X i' = w} (fun _ => (1 : ℝ≥0∞)) := by
      funext X
      by_cases h1 : X i = z <;> by_cases h2 : X i' = w <;>
        simp [h1, h2, Set.indicator, Set.mem_setOf_eq]
    rw [heq, lintegral_indicator_const (measurableSet_path_eq_and i z i' w)]
    simp
  have hexpand : ∀ X : ℕ → Site d, localTime z X * localTime w X
      = ∑' i : ℕ, ∑' i' : ℕ,
          (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0) := by
    intro X
    rw [localTime, localTime, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun i => (ENNReal.tsum_mul_left).symm
  have hmeas : ∀ i i' : ℕ, Measurable (fun X : ℕ → Site d =>
      (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0)) := by
    intro i i'
    rw [show (fun X : ℕ → Site d =>
        (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0))
        = Set.indicator {X : ℕ → Site d | X i = z ∧ X i' = w} (fun _ => (1 : ℝ≥0∞)) from by
      funext X
      by_cases h1 : X i = z <;> by_cases h2 : X i' = w <;>
        simp [h1, h2, Set.indicator, Set.mem_setOf_eq]]
    exact measurable_const.indicator (measurableSet_path_eq_and i z i' w)
  calc ∫⁻ X, localTime z X * localTime w X ∂(walkLaw d x)
      = ∫⁻ X, ∑' i : ℕ, ∑' i' : ℕ,
          (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0)
          ∂(walkLaw d x) := lintegral_congr hexpand
    _ = ∑' i : ℕ, ∫⁻ X, ∑' i' : ℕ,
          (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0)
          ∂(walkLaw d x) :=
        lintegral_tsum fun i => (Measurable.tsum fun i' => hmeas i i').aemeasurable
    _ = ∑' i : ℕ, ∑' i' : ℕ, ∫⁻ X,
          (if X i = z then (1 : ℝ≥0∞) else 0) * (if X i' = w then (1 : ℝ≥0∞) else 0)
          ∂(walkLaw d x) :=
        tsum_congr fun i => lintegral_tsum fun i' => (hmeas i i').aemeasurable
    _ = ∑' i : ℕ, ∑' i' : ℕ, (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} :=
        tsum_congr fun i => tsum_congr fun i' => hP i i'
    _ ≤ (∑' i : ℕ, ∑' i' : ℕ,
          (if i ≤ i' then (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} else 0))
        + (∑' i : ℕ, ∑' i' : ℕ,
          (if i' ≤ i then (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} else 0)) := by
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun i' => ?_
        rcases Nat.le_total i i' with h | h
        · simp [h]
        · simp [h]
    _ = ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d z w)
        + ENNReal.ofReal (green d x w) * ENNReal.ofReal (green d z w) := by
        congr 1
        · calc ∑' i : ℕ, ∑' i' : ℕ,
              (if i ≤ i' then (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} else 0)
              = ∑' i : ℕ, ∑' n : ℕ, (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X (i + n) = w} :=
                tsum_congr fun i => tsum_ite_ge_eq_shift i
                  (fun i' => (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w})
            _ = ∑' i : ℕ, ∑' n : ℕ,
                ENNReal.ofReal (heatKernel d i x z) * ENNReal.ofReal (heatKernel d n z w) :=
                tsum_congr fun i => tsum_congr fun n => walkLaw_apply_two_site (by omega) x z w i n
            _ = (∑' i : ℕ, ENNReal.ofReal (heatKernel d i x z))
                * (∑' n : ℕ, ENNReal.ofReal (heatKernel d n z w)) := by
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun i => ENNReal.tsum_mul_left
            _ = ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d z w) := by
                rw [green, green,
                  ENNReal.ofReal_tsum_of_nonneg (fun i => heatKernel_nonneg i x z)
                    (summable_heatKernel_transient (by omega) x z),
                  ENNReal.ofReal_tsum_of_nonneg (fun n => heatKernel_nonneg n z w)
                    (summable_heatKernel_transient (by omega) z w)]
        · calc ∑' i : ℕ, ∑' i' : ℕ,
              (if i' ≤ i then (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} else 0)
              = ∑' i' : ℕ, ∑' i : ℕ,
                (if i' ≤ i then (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w} else 0) :=
                ENNReal.tsum_comm
            _ = ∑' i' : ℕ, ∑' n : ℕ,
                (walkLaw d x) {X : ℕ → Site d | X (i' + n) = z ∧ X i' = w} :=
                tsum_congr fun i' => tsum_ite_ge_eq_shift i'
                  (fun i => (walkLaw d x) {X : ℕ → Site d | X i = z ∧ X i' = w})
            _ = ∑' i' : ℕ, ∑' n : ℕ,
                ENNReal.ofReal (heatKernel d i' x w) * ENNReal.ofReal (heatKernel d n w z) := by
                refine tsum_congr fun i' => tsum_congr fun n => ?_
                have := walkLaw_apply_two_site (d := d) (by omega) x w z i' n
                have hset : {X : ℕ → Site d | X (i' + n) = z ∧ X i' = w}
                    = {X : ℕ → Site d | X i' = w ∧ X (i' + n) = z} := by
                  ext X; exact and_comm
                rw [hset]
                exact this
            _ = (∑' i' : ℕ, ENNReal.ofReal (heatKernel d i' x w))
                * (∑' n : ℕ, ENNReal.ofReal (heatKernel d n w z)) := by
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun i' => ENNReal.tsum_mul_left
            _ = ENNReal.ofReal (green d x w) * ENNReal.ofReal (green d z w) := by
                have e1 : (∑' i' : ℕ, ENNReal.ofReal (heatKernel d i' x w))
                    = ENNReal.ofReal (green d x w) := by
                  rw [green]
                  exact (ENNReal.ofReal_tsum_of_nonneg (fun i' => heatKernel_nonneg i' x w)
                    (summable_heatKernel_transient (by omega) x w)).symm
                have e2 : (∑' n : ℕ, ENNReal.ofReal (heatKernel d n w z))
                    = ENNReal.ofReal (green d z w) := by
                  rw [← green_symm (by omega) w z, green]
                  exact (ENNReal.ofReal_tsum_of_nonneg (fun n => heatKernel_nonneg n w z)
                    (summable_heatKernel_transient (by omega) w z)).symm
                rw [e1, e2]

/-! ### Translation invariance of the `ℓ²` Green mass -/

/-- The two-point Green function is translation invariant: shifting both endpoints by the
same `w'` does not change its value, by translation invariance of the heat kernel. -/
theorem green_add_right (x y w' : Site d) : green d (x + w') (y + w') = green d x y :=
  tsum_congr fun k => heatKernel_add_right k x y w'

/-- The `ℓ²` mass of the Green function does not depend on the base point. -/
theorem tsum_green_sq_eq (z : Site d) :
    ∑' w : Site d, green d z w ^ 2 = ∑' w : Site d, green d 0 w ^ 2 := by
  rw [← (Equiv.addRight z).tsum_eq fun w : Site d => green d z w ^ 2]
  refine tsum_congr fun c => ?_
  have hg : green d z (c + z) = green d 0 c := by
    simpa using green_add_right 0 c z
  simpa using congrArg (fun r : ℝ => r ^ 2) hg

/-- Square-summability of the Green function transports from the origin to any base point,
by the same translation `green_add_right` uses. -/
theorem summable_green_sq_of (hM : Summable fun w : Site d => green d 0 w ^ 2) (z : Site d) :
    Summable fun w : Site d => green d z w ^ 2 := by
  have h1 : Summable fun c : Site d => green d z (c + z) ^ 2 := by
    have hcongr : (fun c : Site d => green d z (c + z) ^ 2)
        = fun c : Site d => green d 0 c ^ 2 := by
      funext c
      have hg : green d z (c + z) = green d 0 c := by simpa using green_add_right 0 c z
      rw [hg]
    rw [hcongr]; exact hM
  exact (Equiv.addRight z).summable_iff.mp h1

/-! ### The second moment of the intersection count, via the local times of a
pair of sites -/

/-- `L_X(z)L_X(w)`, at a pair of sites bundled as one point of `Site d × Site
d`, so that the Tonelli argument below needs only a single `tsum`. -/
noncomputable def pairLT (p : Site d × Site d) (X : ℕ → Site d) : ℝ≥0∞ :=
  localTime p.1 X * localTime p.2 X

/-- `pairLT` is measurable, being a product of the measurable local-time functionals at its
two coordinates. -/
theorem measurable_pairLT (p : Site d × Site d) : Measurable (pairLT p) :=
  (measurable_localTime p.1).mul (measurable_localTime p.2)

/-- The second moment of the intersection count factors through the local
times at a pair of sites: `I(X,Y)^2 = ∑_{z,w} L_X(z)L_X(w) · L_Y(z)L_Y(w)`. -/
theorem interCount_sq_eq_tsum_pairLT (X Y : ℕ → Site d) :
    Sandpile.External.interCount X Y ^ 2 = ∑' p : Site d × Site d, pairLT p X * pairLT p Y := by
  have h1 : Sandpile.External.interCount X Y
      = ∑' z : Site d, localTime z X * localTime z Y := interCount_eq_tsum_localTime X Y
  rw [h1, pow_two, ← ENNReal.tsum_mul_right, ENNReal.tsum_prod']
  refine tsum_congr fun z => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun w => ?_
  show (localTime z X * localTime z Y) * (localTime w X * localTime w Y)
      = pairLT (z, w) X * pairLT (z, w) Y
  rw [pairLT, pairLT]
  ring

/-- **The Tonelli identity for the second intersection moment.**  Independence
of the two walks turns the double expectation of the squared intersection
count into a sum, over pairs of sites, of a product of two single-walk
expectations. -/
theorem lintegral_interCount_sq_eq [NeZero d] (x y : Site d) :
    (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y) ∂(walkLaw d x))
      = ∑' p : Site d × Site d,
          (∫⁻ X, pairLT p X ∂(walkLaw d x)) * ∫⁻ Y, pairLT p Y ∂(walkLaw d y) := by
  classical
  have hinner : ∀ X : ℕ → Site d,
      ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y)
        = ∑' p : Site d × Site d, pairLT p X * ∫⁻ Y, pairLT p Y ∂(walkLaw d y) := by
    intro X
    calc ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y)
        = ∫⁻ Y, ∑' p : Site d × Site d, pairLT p X * pairLT p Y ∂(walkLaw d y) :=
          lintegral_congr fun Y => interCount_sq_eq_tsum_pairLT X Y
      _ = ∑' p : Site d × Site d, ∫⁻ Y, pairLT p X * pairLT p Y ∂(walkLaw d y) :=
          lintegral_tsum fun p => ((measurable_pairLT p).const_mul (pairLT p X)).aemeasurable
      _ = ∑' p : Site d × Site d, pairLT p X * ∫⁻ Y, pairLT p Y ∂(walkLaw d y) :=
          tsum_congr fun p => lintegral_const_mul _ (measurable_pairLT p)
  calc ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y) ∂(walkLaw d x)
      = ∫⁻ X, ∑' p : Site d × Site d, pairLT p X * ∫⁻ Y, pairLT p Y ∂(walkLaw d y)
          ∂(walkLaw d x) := lintegral_congr hinner
    _ = ∑' p : Site d × Site d, ∫⁻ X, pairLT p X * ∫⁻ Y, pairLT p Y ∂(walkLaw d y)
          ∂(walkLaw d x) :=
        lintegral_tsum fun p => ((measurable_pairLT p).mul_const _).aemeasurable
    _ = ∑' p : Site d × Site d,
          (∫⁻ X, pairLT p X ∂(walkLaw d x)) * ∫⁻ Y, pairLT p Y ∂(walkLaw d y) :=
        tsum_congr fun p => lintegral_mul_const _ (measurable_pairLT p)

/-! ### The `z ↔ w` swap of the four relative orderings -/

/-- Swapping the two coordinates of the summation variable does not change
this sum: the "matching orderings" pattern, with the same base point read at
both `p.1` and `p.2`. Proved once, standalone, so that using it twice below
does not re-elaborate the Tonelli manipulation in an ever-larger context. -/
theorem tsum_green_swap_match (hd1 : 1 ≤ d) (a b : Site d) :
    (∑' p : Site d × Site d,
        ENNReal.ofReal (green d a p.2) * ENNReal.ofReal (green d b p.2)
          * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
      = ∑' p : Site d × Site d,
          ENNReal.ofReal (green d a p.1) * ENNReal.ofReal (green d b p.1)
            * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)) := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun u => tsum_congr fun v => ?_
  rw [green_symm hd1 v u]

/-- The same reindexing for the "crossed orderings" pattern, where the two
base points are read at the two different coordinates. -/
theorem tsum_green_swap_cross (hd1 : 1 ≤ d) (a b : Site d) :
    (∑' p : Site d × Site d,
        ENNReal.ofReal (green d a p.2) * ENNReal.ofReal (green d b p.1)
          * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
      = ∑' p : Site d × Site d,
          ENNReal.ofReal (green d a p.1) * ENNReal.ofReal (green d b p.2)
            * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)) := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun u => tsum_congr fun v => ?_
  rw [green_symm hd1 v u]

/-- **The matching-orderings sum.**  The "matching orderings" pattern sums to
`M` (the finite quantity of Lawler's Proposition 3.2.1, `∑_w G(0,w)^2`, by
translation invariance of the Green function) times the first intersection
moment `∑_z G(x,z)G(y,z)`. -/
theorem tsum_green_matching_eq (_hd1 : 1 ≤ d)
    (hL2 : Summable fun w : Site d => green d 0 w ^ 2) (x y : Site d)
    (hsum : Summable fun z : Site d => green d x z * green d y z) :
    (∑' p : Site d × Site d,
        ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d y p.1)
          * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
      = ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2)
        * ENNReal.ofReal (∑' z : Site d, green d x z * green d y z) := by
  rw [ENNReal.tsum_prod']
  have hz : ∀ z : Site d, (∑' w : Site d,
      ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d y z)
        * (ENNReal.ofReal (green d z w) * ENNReal.ofReal (green d z w)))
      = ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d y z)
        * ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2) := by
    intro z
    rw [ENNReal.tsum_mul_left]
    congr 1
    have hw : ∀ w : Site d, ENNReal.ofReal (green d z w) * ENNReal.ofReal (green d z w)
        = ENNReal.ofReal (green d z w ^ 2) := by
      intro w; rw [← ENNReal.ofReal_mul (green_nonneg z w), sq]
    rw [tsum_congr hw,
      show (∑' w : Site d, ENNReal.ofReal (green d z w ^ 2))
          = ENNReal.ofReal (∑' w : Site d, green d z w ^ 2) from
        (ENNReal.ofReal_tsum_of_nonneg (fun w => sq_nonneg (green d z w))
          (summable_green_sq_of hL2 z)).symm,
      tsum_green_sq_eq z]
  rw [tsum_congr hz, ENNReal.tsum_mul_right,
    show (∑' i : Site d, ENNReal.ofReal (green d x i) * ENNReal.ofReal (green d y i))
        = ENNReal.ofReal (∑' z : Site d, green d x z * green d y z) from by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg (green_nonneg x z) (green_nonneg y z))
        hsum]
      exact tsum_congr fun z => (ENNReal.ofReal_mul (green_nonneg x z)).symm]
  ring

/-- **The crossed-orderings sum.**  The "crossed orderings" pattern sums to the
`ofReal` of the crossed-ordering sum of `Sandpile.External.GreenBoundsHigh`. -/
theorem tsum_green_crossed_eq (x y : Site d)
    (hsum : Summable fun p : Site d × Site d =>
      green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) :
    (∑' p : Site d × Site d,
        ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d y p.2)
          * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
      = ENNReal.ofReal (∑' p : Site d × Site d,
          green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) := by
  have hT2eq : ∀ p : Site d × Site d,
      ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d y p.2)
          * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2))
        = ENNReal.ofReal (green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) := by
    intro p
    rw [show green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2
        = green d x p.1 * (green d p.1 p.2 * green d p.1 p.2) * green d y p.2 from by ring,
      ENNReal.ofReal_mul (mul_nonneg (green_nonneg x p.1)
        (mul_nonneg (green_nonneg p.1 p.2) (green_nonneg p.1 p.2))),
      ENNReal.ofReal_mul (green_nonneg x p.1), ENNReal.ofReal_mul (green_nonneg p.1 p.2)]
    ring
  rw [tsum_congr hT2eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun p : Site d × Site d =>
      mul_nonneg (mul_nonneg (green_nonneg x p.1) (sq_nonneg (green d p.1 p.2)))
        (green_nonneg y p.2))
    hsum).symm

/-! ### The combinatorics of the four relative orderings -/

/-- **The four-ordering bound, in the vocabulary of `green` alone.**  Splits the
product of the two single-walk bounds of `lintegral_localTime_mul_le` into the
four relative orderings, identifies the two "matching" orderings (up to the
`z ↔ w` swap) with the finite quantity `M := ∑_w G(0,w)^2` of Lawler's
Proposition 3.2.1 times the first intersection moment, and the two "crossed"
orderings (again up to the swap) with the crossed-ordering sum bounded
directly by `Sandpile.External.GreenBoundsHigh`.  This isolates the Green-sum
combinatorics from the walk/measure-theoretic vocabulary of the surrounding proof, keeping
each step's elaboration context small. -/
theorem green_bound_combine (hd1 : 1 ≤ d)
    (hL2 : Summable fun w : Site d => green d 0 w ^ 2)
    (C1 C2 : ℝ) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hfirst : ∀ x y : Site d, Summable (fun z : Site d => green d x z * green d y z) ∧
      (∑' z : Site d, green d x z * green d y z) ≤
        C1 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
    (hcross : ∀ x y : Site d,
      Summable (fun p : Site d × Site d => green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) ∧
      (∑' p : Site d × Site d, green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) ≤
        C2 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
    (x y : Site d) :
    (∑' p : Site d × Site d,
        (ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d p.1 p.2)
              + ENNReal.ofReal (green d x p.2) * ENNReal.ofReal (green d p.1 p.2))
          * (ENNReal.ofReal (green d y p.1) * ENNReal.ofReal (green d p.1 p.2)
              + ENNReal.ofReal (green d y p.2) * ENNReal.ofReal (green d p.1 p.2)))
      ≤ ENNReal.ofReal ((2 * (∑' w : Site d, green d 0 w ^ 2) * C1 + 2 * C2)
          * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
  classical
  have hMnonneg : 0 ≤ ∑' w : Site d, green d 0 w ^ 2 := tsum_nonneg fun w => sq_nonneg _
  have hsplit : ∀ p : Site d × Site d,
      (ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d p.1 p.2)
            + ENNReal.ofReal (green d x p.2) * ENNReal.ofReal (green d p.1 p.2))
        * (ENNReal.ofReal (green d y p.1) * ENNReal.ofReal (green d p.1 p.2)
            + ENNReal.ofReal (green d y p.2) * ENNReal.ofReal (green d p.1 p.2))
        = (ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d y p.1)
              * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
          + (ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d y p.2)
              * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
          + (ENNReal.ofReal (green d x p.2) * ENNReal.ofReal (green d y p.1)
              * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2)))
          + (ENNReal.ofReal (green d x p.2) * ENNReal.ofReal (green d y p.2)
              * (ENNReal.ofReal (green d p.1 p.2) * ENNReal.ofReal (green d p.1 p.2))) := by
    intro p; ring
  rw [tsum_congr hsplit]
  simp only [ENNReal.tsum_add]
  rw [tsum_green_swap_match hd1 x y, tsum_green_swap_cross hd1 x y,
    tsum_green_matching_eq hd1 hL2 x y (hfirst x y).1, tsum_green_crossed_eq x y (hcross x y).1]
  have hle1 : ENNReal.ofReal (∑' z : Site d, green d x z * green d y z)
      ≤ ENNReal.ofReal (C1 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
    ENNReal.ofReal_le_ofReal (hfirst x y).2
  have hle2 : ENNReal.ofReal (∑' p : Site d × Site d,
        green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2)
      ≤ ENNReal.ofReal (C2 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
    ENNReal.ofReal_le_ofReal (hcross x y).2
  have hgoal : ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2)
          * ENNReal.ofReal (∑' z : Site d, green d x z * green d y z)
        + ENNReal.ofReal
            (∑' p : Site d × Site d, green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2)
        + ENNReal.ofReal
            (∑' p : Site d × Site d, green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2)
        + ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2)
          * ENNReal.ofReal (∑' z : Site d, green d x z * green d y z)
      ≤ ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2)
          * ENNReal.ofReal (C1 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
        + ENNReal.ofReal (C2 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
        + ENNReal.ofReal (C2 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
        + ENNReal.ofReal (∑' w : Site d, green d 0 w ^ 2)
          * ENNReal.ofReal (C1 * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
    gcongr
  refine hgoal.trans (le_of_eq ?_)
  have hpow_nonneg : (0:ℝ) ≤ (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
    have hE : (0:ℝ) ≤ 1 + Sandpile.External.latticeNorm (x - y) := by
      have := LatticeProb.euclidNorm_nonneg (x - y)
      rw [Sandpile.External.latticeNorm_eq_euclidNorm]
      linarith
    positivity
  rw [← ENNReal.ofReal_mul hMnonneg,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-! ### The final assembly -/

/-- **The second intersection moment.**  Bounding each pointwise summand of
`lintegral_interCount_sq_eq` by `lintegral_localTime_mul_le` on both walks and
combining via `green_bound_combine`. -/
theorem lintegral_interCount_sq_le [NeZero d] (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site d,
      (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y) ∂(walkLaw d x)) ≤
        ENNReal.ofReal (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
  classical
  obtain ⟨-, hL2, -, ⟨C1, hC1, hfirst⟩, ⟨C2, hC2, hcross⟩⟩ := Sandpile.External.greenBoundsHigh d hd
  have hMnonneg : 0 ≤ ∑' w : Site d, green d 0 w ^ 2 := tsum_nonneg fun w => sq_nonneg _
  have hd1 : 1 ≤ d := by omega
  have hd3 : 3 ≤ d := by omega
  refine ⟨2 * (∑' w : Site d, green d 0 w ^ 2) * C1 + 2 * C2, by nlinarith, fun x y => ?_⟩
  rw [lintegral_interCount_sq_eq x y]
  have hstep1 : ∀ p : Site d × Site d,
      (∫⁻ X, pairLT p X ∂(walkLaw d x)) * (∫⁻ Y, pairLT p Y ∂(walkLaw d y))
        ≤ (ENNReal.ofReal (green d x p.1) * ENNReal.ofReal (green d p.1 p.2)
              + ENNReal.ofReal (green d x p.2) * ENNReal.ofReal (green d p.1 p.2))
          * (ENNReal.ofReal (green d y p.1) * ENNReal.ofReal (green d p.1 p.2)
              + ENNReal.ofReal (green d y p.2) * ENNReal.ofReal (green d p.1 p.2)) :=
    fun p => mul_le_mul' (lintegral_localTime_mul_le hd3 x p.1 p.2)
      (lintegral_localTime_mul_le hd3 y p.1 p.2)
  exact le_trans (ENNReal.tsum_le_tsum hstep1)
    (green_bound_combine hd1 hL2 C1 C2 hC1 hC2 hfirst hcross x y)

end Sandpile

-- FROZEN-STATEMENT-BEGIN
/-- **The second intersection estimate holds**; it is no longer an assumption. -/
theorem Sandpile.External.intersectionSecondMoment : Sandpile.External.IntersectionSecondMoment := by
  intro d hd
  haveI : NeZero d := ⟨by omega⟩
  exact Sandpile.lintegral_interCount_sq_le hd
-- FROZEN-STATEMENT-END
