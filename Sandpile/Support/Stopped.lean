/-
The optimal-stopping identity behind `lem:difference-representation` and
`lem:localization-killing`: for a stopping time `τ ≤ t`,

  `E_x[∑_{j<τ} ζ(X_j) + V_{t-τ}(X_τ)] = V_t(x)`.

Write `M_n := ∑_{j<n} ζ(X_j) + V_{t-n}(X_n)`.  The membrane recursion
`V_{m+1} = ζ + P V_m` gives `M_{n+1} - M_n = V_{t-n-1}(X_{n+1}) - P V_{t-n-1}(X_n)`,
whose integral against an event determined by the first `n` positions vanishes by
the one-step Markov property of `Sandpile/Support/StrongMarkov.lean`.  Since `τ`
is bounded by `t`, `M_τ - M_0` is a finite sum of such increments.  No shift, and
so no strong Markov property, is needed.

`walk_one_step` asks for a bounded field and the membrane field is unbounded, so
each increment is taken against the truncation of the field to a box large enough
to contain everything the walk can reach by time `n + 1`, together with its
neighbours.  `boxDist_walkPath_le` is what makes that replacement invisible.
-/
import Sandpile.Support.StrongMarkov
import Sandpile.Support.Walk

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- A field vanishing off a finite set is bounded. -/
theorem exists_bound_of_eqOn_zero (s : Finset (Site d)) (f : Site d → ℝ)
    (hf : ∀ y ∉ s, f y = 0) : ∃ M : ℝ, ∀ y, |f y| ≤ M := by
  classical
  refine ⟨∑ z ∈ s, |f z|, fun y => ?_⟩
  by_cases hy : y ∈ s
  · exact Finset.single_le_sum (f := fun z => |f z|) (fun z _ => abs_nonneg _) hy
  · rw [hf y hy, abs_zero]
    exact Finset.sum_nonneg fun z _ => abs_nonneg _

/-- The truncation of a field to a finite set. -/
noncomputable def trunc (s : Finset (Site d)) (f : Site d → ℝ) (y : Site d) : ℝ :=
  if y ∈ s then f y else 0

theorem trunc_eq_of_mem {s : Finset (Site d)} {f : Site d → ℝ} {y : Site d} (h : y ∈ s) :
    trunc s f y = f y := by simp [trunc, h]

theorem exists_bound_trunc (s : Finset (Site d)) (f : Site d → ℝ) :
    ∃ M : ℝ, ∀ y, |trunc s f y| ≤ M :=
  exists_bound_of_eqOn_zero s _ fun y hy => by simp [trunc, hy]

/-- The neighbour average only reads the neighbours, so two fields agreeing there
have the same average. -/
theorem avg_congr {f g : Site d → ℝ} {y : Site d}
    (h : ∀ i : Fin d, f (y + unit i) = g (y + unit i) ∧ f (y - unit i) = g (y - unit i)) :
    avg f y = avg g y := by
  unfold avg LatticeProb.walkOp nbrSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [(h i).1, (h i).2]

theorem abs_avg_le (hd : 1 ≤ d) {f : Site d → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) (y : Site d) :
    |avg f y| ≤ M := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hf y)
  have hd0 : (0 : ℝ) < 2 * d := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  unfold avg LatticeProb.walkOp nbrSum
  rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
  calc |∑ i : Fin d, (f (y + unit i) + f (y - unit i))|
      ≤ ∑ i : Fin d, |f (y + unit i) + f (y - unit i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (M + M) :=
        Finset.sum_le_sum fun i _ =>
          le_trans (abs_add_le _ _) (add_le_add (hf _) (hf _))
    _ = M * (2 * d) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The extension of a prefix of increments by zero. -/
def extendPrefix (n : ℕ) (u : ↥(Finset.range n) → Site d) (j : ℕ) : Site d :=
  if h : j ∈ Finset.range n then u ⟨j, h⟩ else 0

/-- The indicator of `{n < τ}`, as a function of the first `n` increments. -/
noncomputable def stopIndicator (x : Site d) (n : ℕ) (τ : (ℕ → Site d) → ℕ)
    (u : ↥(Finset.range n) → Site d) : ℝ :=
  if n < τ (walkPath x (extendPrefix n u)) then 1 else 0

theorem abs_stopIndicator_le (x : Site d) (n : ℕ) (τ : (ℕ → Site d) → ℕ)
    (u : ↥(Finset.range n) → Site d) : |stopIndicator x n τ u| ≤ 1 := by
  unfold stopIndicator; split <;> simp

theorem stopIndicator_restrict (x : Site d) (n : ℕ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (ξ : ℕ → Site d) :
    stopIndicator x n τ ((Finset.range n).restrict ξ)
      = if n < τ (walkPath x ξ) then 1 else 0 := by
  unfold stopIndicator
  have hagree : ∀ j ≤ n,
      walkPath x (extendPrefix n ((Finset.range n).restrict ξ)) j = walkPath x ξ j := by
    intro j hj
    unfold walkPath
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmem : i ∈ Finset.range n :=
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)
    simp [extendPrefix, hmem, Finset.restrict]
  have h := hτ.le_iff n hagree
  have hiff : n < τ (walkPath x (extendPrefix n ((Finset.range n).restrict ξ)))
      ↔ n < τ (walkPath x ξ) := by
    rw [← Nat.not_le, ← Nat.not_le, h]
  exact if_congr hiff rfl rfl

/-- Each martingale increment integrates to zero against the event that the
stopping time has not yet occurred.  This is the one-step Markov property applied
to the membrane field, truncated to a box the walk cannot leave. -/
theorem integral_increment_zero (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t n : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) :
    Integrable (fun ξ => (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
          - avg (membrane ζ (t - n - 1)) (walkPath x ξ n)))
        (Measure.infinitePi fun _ : ℕ => stepLaw d) ∧
      ∫ ξ, (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
          - avg (membrane ζ (t - n - 1)) (walkPath x ξ n))
      ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) = 0 := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  set P : Measure (ℕ → Site d) := Measure.infinitePi fun _ : ℕ => stepLaw d with hP
  set V := membrane ζ (t - n - 1) with hVdef
  set s := boxFinset x (n + 2) with hsdef
  set f := trunc s V with hfdef
  obtain ⟨Mf, hMf⟩ := exists_bound_trunc s V
  have hwm : ∀ k : ℕ, Measurable fun ξ : ℕ → Site d => walkPath x ξ k := by
    intro k
    have h : Measurable ((fun g : ℕ → Site d => g k) ∘ walkPath x) :=
      (measurable_pi_apply k).comp (measurable_walkPath x)
    exact h
  have hGm : Measurable fun ξ : ℕ → Site d =>
      stopIndicator x n τ ((Finset.range n).restrict ξ) := by
    have hres : Measurable fun ξ : ℕ → Site d => (Finset.range n).restrict ξ :=
      Finset.measurable_restrict (Finset.range n)
    have h : Measurable (stopIndicator x n τ ∘
        fun ξ : ℕ → Site d => (Finset.range n).restrict ξ) :=
      (measurable_of_countable _).comp hres
    exact h
  have hfm1 : Measurable fun ξ : ℕ → Site d => f (walkPath x ξ (n + 1)) := by
    have h : Measurable (f ∘ fun ξ : ℕ → Site d => walkPath x ξ (n + 1)) :=
      (measurable_of_countable _).comp (hwm (n + 1))
    exact h
  have hfm2 : Measurable fun ξ : ℕ → Site d => avg f (walkPath x ξ n) := by
    have h : Measurable (avg f ∘ fun ξ : ℕ → Site d => walkPath x ξ n) :=
      (measurable_of_countable _).comp (hwm n)
    exact h
  have hI1 : Integrable (fun ξ =>
      stopIndicator x n τ ((Finset.range n).restrict ξ) * f (walkPath x ξ (n + 1))) P := by
    refine (integrable_const (1 * Mf)).mono' (hGm.mul hfm1).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_stopIndicator_le _ _ _ _) (hMf _) (abs_nonneg _) zero_le_one
  have hI2 : Integrable (fun ξ =>
      stopIndicator x n τ ((Finset.range n).restrict ξ) * avg f (walkPath x ξ n)) P := by
    refine (integrable_const (1 * Mf)).mono' (hGm.mul hfm2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_stopIndicator_le _ _ _ _) (abs_avg_le hd hMf _) (abs_nonneg _) zero_le_one
  have hae : (fun ξ => (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (V (walkPath x ξ (n + 1)) - avg V (walkPath x ξ n)))
      =ᵐ[P] fun ξ =>
        stopIndicator x n τ ((Finset.range n).restrict ξ) * f (walkPath x ξ (n + 1))
          - stopIndicator x n τ ((Finset.range n).restrict ξ) * avg f (walkPath x ξ n) := by
    filter_upwards [boxDist_walkPath_le hd x (n + 1), boxDist_walkPath_le hd x n] with ξ h1 h2
    have e1 : V (walkPath x ξ (n + 1)) = f (walkPath x ξ (n + 1)) :=
      (trunc_eq_of_mem (mem_boxFinset (by omega))).symm
    have e2 : avg V (walkPath x ξ n) = avg f (walkPath x ξ n) := by
      refine avg_congr fun i => ⟨?_, ?_⟩
      · refine (trunc_eq_of_mem (mem_boxFinset ?_)).symm
        exact le_trans (boxDist_add_le_of_unit x _ _ fun j => natAbs_unit_le i j) (by omega)
      · refine (trunc_eq_of_mem (mem_boxFinset ?_)).symm
        rw [sub_eq_add_neg]
        refine le_trans (boxDist_add_le_of_unit x _ _ fun j => ?_) (by omega)
        simpa using natAbs_unit_le (d := d) i j
    rw [e1, e2, ← stopIndicator_restrict x n hτ ξ]
    ring
  refine ⟨(hI1.sub hI2).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub hI1 hI2,
    walk_one_step hd x n (stopIndicator x n τ) f 1 Mf
      (abs_stopIndicator_le x n τ) hMf, sub_self]

/-- Telescoping a bounded stopping time: a value at a stopped index is the value
at zero plus the increments taken while the index has not been reached. -/
theorem telescope_stopped (a : ℕ → ℝ) {N t : ℕ} (h : N ≤ t) :
    a N = a 0 + ∑ n ∈ Finset.range t, (if n < N then a (n + 1) - a n else 0) := by
  have hfilt : (Finset.range t).filter (fun n => n < N) = Finset.range N := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilt, Finset.sum_range_sub]
  ring

/-- The optimal-stopping identity for the membrane field: for a stopping time
bounded by `t`, the stopped scenery sum plus the remaining-time membrane field
integrates to the membrane field at the start.  This is what
`lem:difference-representation` and `lem:localization-killing` turn on. -/
theorem integral_stopped_membrane (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    ∫ ξ, (sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)
        + membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ))))
      ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) = membrane ζ t x := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hpt : ∀ ξ : ℕ → Site d,
      sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)
          + membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))
        = membrane ζ t x + ∑ n ∈ Finset.range t,
          (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
            (membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
              - avg (membrane ζ (t - n - 1)) (walkPath x ξ n)) := by
    intro ξ
    set a : ℕ → ℝ := fun n => sceneryPartialSum ζ n (walkPath x ξ)
      + membrane ζ (t - n) (walkPath x ξ n) with ha
    have h0 : a 0 = membrane ζ t x := by
      simp [ha, sceneryPartialSum, walkPath_zero]
    have hstep : ∀ n ∈ Finset.range t, a (n + 1) - a n =
        membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
          - avg (membrane ζ (t - n - 1)) (walkPath x ξ n) := by
      intro n hn
      have hnt : n < t := Finset.mem_range.mp hn
      obtain ⟨m, hm⟩ : ∃ m, t - n = m + 1 := ⟨t - n - 1, by omega⟩
      have h2 : t - (n + 1) = m := by omega
      have h3 : t - n - 1 = m := by omega
      have hsp : sceneryPartialSum ζ (n + 1) (walkPath x ξ)
          = sceneryPartialSum ζ n (walkPath x ξ) + ζ (walkPath x ξ n) := by
        unfold sceneryPartialSum
        rw [Finset.sum_range_succ]
      show (sceneryPartialSum ζ (n + 1) (walkPath x ξ)
            + membrane ζ (t - (n + 1)) (walkPath x ξ (n + 1)))
          - (sceneryPartialSum ζ n (walkPath x ξ) + membrane ζ (t - n) (walkPath x ξ n)) = _
      rw [hsp, h3, h2, hm, membrane_succ]
      ring
    have := telescope_stopped a (hτt (walkPath x ξ))
    rw [show sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)
        + membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))
        = a (τ (walkPath x ξ)) from rfl, this, h0]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hstep n hn]
    split <;> simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hint : ∀ n ∈ Finset.range t, Integrable (fun ξ : ℕ → Site d =>
      (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
        (membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
          - avg (membrane ζ (t - n - 1)) (walkPath x ξ n)))
      (Measure.infinitePi fun _ : ℕ => stepLaw d) :=
    fun n _ => (integral_increment_zero hd x ζ t n hτ).1
  rw [integral_add (integrable_const _) (integrable_finsetSum _ hint),
    integral_const, integral_finsetSum _ hint]
  have hzero : ∀ n ∈ Finset.range t, (∫ ξ, (if n < τ (walkPath x ξ) then (1 : ℝ) else 0) *
      (membrane ζ (t - n - 1) (walkPath x ξ (n + 1))
        - avg (membrane ζ (t - n - 1)) (walkPath x ξ n))
      ∂(Measure.infinitePi fun _ : ℕ => stepLaw d)) = 0 :=
    fun n _ => (integral_increment_zero hd x ζ t n hτ).2
  rw [Finset.sum_congr rfl hzero]
  simp

/-- A stopping time bounded by `t` is measurable: it reads only the first `t + 1`
positions, and those range over a countable space. -/
theorem measurable_of_isWalkStopping (t : ℕ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) : Measurable τ := by
  have hrep : τ = (fun u : ↥(Finset.range (t + 1)) → Site d =>
      τ (extendPrefix (t + 1) u)) ∘ (Finset.range (t + 1)).restrict := by
    funext X
    have hagree : ∀ j ≤ t,
        X j = extendPrefix (t + 1) ((Finset.range (t + 1)).restrict X) j := by
      intro j hj
      have hmem : j ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
      simp [extendPrefix, hmem, Finset.restrict]
    exact (hτ (τ X) X _ (fun j hj => hagree j (le_trans hj (hτt X))) rfl).symm
  rw [hrep]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict _)

theorem le_sum_abs_of_mem {s : Finset (Site d)} {f : Site d → ℝ} {y : Site d} (h : y ∈ s) :
    |f y| ≤ ∑ z ∈ s, |f z| :=
  Finset.single_le_sum (f := fun z => |f z|) (fun _ _ => abs_nonneg _) h

/-- A functional of the path that reads only the first `t + 1` positions is
measurable, because those range over a countable space. -/
theorem measurable_of_dependsOn (t : ℕ) (F : (ℕ → Site d) → ℝ)
    (hF : ∀ X Y : ℕ → Site d, (∀ j ≤ t, X j = Y j) → F X = F Y) : Measurable F := by
  have hrep : F = (fun u : ↥(Finset.range (t + 1)) → Site d =>
      F (extendPrefix (t + 1) u)) ∘ (Finset.range (t + 1)).restrict := by
    funext X
    refine hF X _ fun j hj => ?_
    have hmem : j ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
    simp [extendPrefix, hmem, Finset.restrict]
  rw [hrep]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict _)

/-- A bounded stopping time reads only the first `t + 1` positions. -/
theorem isWalkStopping_dependsOn {t : ℕ} {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ)
    (hτt : ∀ X, τ X ≤ t) (X Y : ℕ → Site d) (h : ∀ j ≤ t, X j = Y j) : τ X = τ Y :=
  (hτ (τ X) X Y (fun j hj => h j (le_trans hj (hτt X))) rfl).symm

theorem measurable_stoppedScenery (t : ℕ) (ζ : Site d → ℝ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Measurable fun X : ℕ → Site d => sceneryPartialSum ζ (τ X) X := by
  refine measurable_of_dependsOn t _ fun X Y h => ?_
  have hxy : τ X = τ Y := isWalkStopping_dependsOn hτ hτt X Y h
  unfold sceneryPartialSum
  rw [hxy]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < τ Y := Finset.mem_range.mp hk
  have hkt : k ≤ t := by have := hτt Y; omega
  rw [h k hkt]

theorem measurable_stoppedMembrane (t : ℕ) (ζ : Site d → ℝ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Measurable fun X : ℕ → Site d => membrane ζ (t - τ X) (X (τ X)) := by
  refine measurable_of_dependsOn t _ fun X Y h => ?_
  have hxy : τ X = τ Y := isWalkStopping_dependsOn hτ hτt X Y h
  rw [hxy, h (τ Y) (hτt Y)]

/-- A bound for the scenery on the box the walk cannot leave by time `t`. -/
noncomputable def sceneryBound (x : Site d) (t : ℕ) (ζ : Site d → ℝ) : ℝ :=
  ∑ z ∈ boxFinset x t, |ζ z|

/-- A bound for every membrane field of order at most `t` on that box. -/
noncomputable def membraneBound (x : Site d) (t : ℕ) (ζ : Site d → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (t + 1), ∑ z ∈ boxFinset x t, |membrane ζ m z|

theorem sceneryBound_nonneg (x : Site d) (t : ℕ) (ζ : Site d → ℝ) :
    0 ≤ sceneryBound x t ζ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem ae_abs_stoppedScenery_le (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτt : ∀ X, τ X ≤ t) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d),
      |sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)| ≤ t * sceneryBound x t ζ := by
  filter_upwards [ae_boxDist_walkPath hd x] with ξ hξ
  have hτ' := hτt (walkPath x ξ)
  calc |sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)|
      ≤ ∑ k ∈ Finset.range (τ (walkPath x ξ)), |ζ (walkPath x ξ k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (τ (walkPath x ξ)), sceneryBound x t ζ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkt : k ≤ t := by have := Finset.mem_range.mp hk; omega
        exact le_sum_abs_of_mem (mem_boxFinset (le_trans (hξ k) hkt))
    _ = (τ (walkPath x ξ) : ℝ) * sceneryBound x t ζ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ t * sceneryBound x t ζ := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hτ') (sceneryBound_nonneg x t ζ)

theorem ae_abs_stoppedMembrane_le (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτt : ∀ X, τ X ≤ t) :
    ∀ᵐ ξ ∂(Measure.infinitePi fun _ : ℕ => stepLaw d),
      |membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))|
        ≤ membraneBound x t ζ := by
  filter_upwards [ae_boxDist_walkPath hd x] with ξ hξ
  have hτ' := hτt (walkPath x ξ)
  have hmem : walkPath x ξ (τ (walkPath x ξ)) ∈ boxFinset x t :=
    mem_boxFinset (le_trans (hξ _) hτ')
  have hm : t - τ (walkPath x ξ) ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
  calc |membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))|
      ≤ ∑ z ∈ boxFinset x t, |membrane ζ (t - τ (walkPath x ξ)) z| := le_sum_abs_of_mem hmem
    _ ≤ membraneBound x t ζ := by
        unfold membraneBound
        exact Finset.single_le_sum
          (f := fun m => ∑ z ∈ boxFinset x t, |membrane ζ m z|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hm

theorem integrable_stoppedScenery (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Integrable (fun ξ => sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ))
      (Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hm : Measurable ((fun X : ℕ → Site d => sceneryPartialSum ζ (τ X) X) ∘ walkPath x) :=
    (measurable_stoppedScenery t ζ hτ hτt).comp (measurable_walkPath x)
  refine (integrable_const (t * sceneryBound x t ζ)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_abs_stoppedScenery_le hd x ζ t hτt] with ξ h
  simpa [Real.norm_eq_abs] using h

theorem integrable_stoppedMembrane (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Integrable
      (fun ξ => membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ))))
      (Measure.infinitePi fun _ : ℕ => stepLaw d) := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  have hm : Measurable
      ((fun X : ℕ → Site d => membrane ζ (t - τ X) (X (τ X))) ∘ walkPath x) :=
    (measurable_stoppedMembrane t ζ hτ hτt).comp (measurable_walkPath x)
  refine (integrable_const (membraneBound x t ζ)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_abs_stoppedMembrane_le hd x ζ t hτt] with ξ h
  simpa [Real.norm_eq_abs] using h

/-- The optimal-stopping identity, in the walk's own language and with the two
terms separated. -/
theorem integral_neg_stoppedMembrane (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    ∫ X, -(membrane ζ (t - τ X) (X (τ X))) ∂(walkLaw d x)
      = (∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x)) - membrane ζ t x := by
  have hsplit : (∫ ξ, sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ)
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d))
      + ∫ ξ, membrane ζ (t - τ (walkPath x ξ)) (walkPath x ξ (τ (walkPath x ξ)))
        ∂(Measure.infinitePi fun _ : ℕ => stepLaw d) = membrane ζ t x := by
    rw [← integral_add (integrable_stoppedScenery hd x ζ t hτ hτt)
      (integrable_stoppedMembrane hd x ζ t hτ hτt)]
    exact integral_stopped_membrane hd x ζ t hτ hτt
  rw [integral_neg,
    integral_walkLaw x (measurable_stoppedMembrane t ζ hτ hτt).aestronglyMeasurable,
    integral_walkLaw x (measurable_stoppedScenery t ζ hτ hτt).aestronglyMeasurable]
  linarith

/-- Translating a set of reals translates its supremum. -/
theorem sSup_image_sub (A : Set ℝ) (hne : A.Nonempty) (hbdd : BddAbove A) (c : ℝ) :
    sSup ((fun a => a - c) '' A) = sSup A - c := by
  have hne' : ((fun a => a - c) '' A).Nonempty := hne.image _
  have hbdd' : BddAbove ((fun a => a - c) '' A) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M - c, by rintro _ ⟨a, ha, rfl⟩; exact sub_le_sub_right (hM ha) c⟩
  refine le_antisymm (csSup_le hne' ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact sub_le_sub_right (le_csSup hbdd ha) c
  · rw [sub_le_iff_le_add]
    refine csSup_le hne fun a ha => ?_
    have h : a - c ≤ sSup ((fun a => a - c) '' A) := le_csSup hbdd' ⟨a, ha, rfl⟩
    linarith

/-- The stopped scenery sums are bounded uniformly over the stopping times, so the
supremum defining the odometer is not a junk value. -/
theorem abs_integral_stoppedScenery_le (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    |∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x)| ≤ t * sceneryBound x t ζ := by
  haveI : IsProbabilityMeasure (stepLaw d) := isProbabilityMeasure_stepLaw hd
  rw [integral_walkLaw x (measurable_stoppedScenery t ζ hτ hτt).aestronglyMeasurable]
  have h := norm_integral_le_of_norm_le_const
    (μ := Measure.infinitePi fun _ : ℕ => stepLaw d)
    (f := fun ξ => sceneryPartialSum ζ (τ (walkPath x ξ)) (walkPath x ξ))
    (C := t * sceneryBound x t ζ) (by
      filter_upwards [ae_abs_stoppedScenery_le hd x ζ t hτt] with ξ hb
      simpa [Real.norm_eq_abs] using hb)
  simpa [Real.norm_eq_abs, Measure.real] using h

end Sandpile
