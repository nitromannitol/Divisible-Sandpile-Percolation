/-
The localized value of `sandpile.tex`, `eq:localized-odometer`, against the
odometer.

The walk of `Sandpile/Walk.lean` is the walk of `LatticeProb/Walk/Markov.lean`:
the increment law, the path map and the walk law are the same definitions, so
the library's Markov property applies here verbatim.  The bridge is recorded
first.

The localized value is the same supremum over bounded stopping times as the
odometer, but of the scenery summed only while the walk has stayed in `D`.  That
truncated sum is the plain scenery sum stopped at `τ ∧ τ_D`, and `τ ∧ τ_D` is
itself a bounded stopping time, so the localized value's set of values is a
subset of the odometer's and the first half of `lem:localization-killing`
follows.
-/
import Sandpile.Support.Stopped
import Sandpile.Support.Odometer
import Sandpile.External.BPSH
import Sandpile.External.BPSHProved
import LatticeProb.Walk.Markov

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-! ### The walk here is the walk in the library -/

theorem stepLaw_eq_incLaw (d : ℕ) : stepLaw d = LatticeProb.incLaw d := rfl

theorem walkPath_eq_sitePath (x : Site d) : walkPath x = LatticeProb.sitePath x := rfl

theorem walkLaw_eq_siteWalkLaw (d : ℕ) (x : Site d) :
    walkLaw d x = LatticeProb.siteWalkLaw d x := rfl

theorem isWalkStopping_iff {τ : (ℕ → Site d) → ℕ} :
    IsWalkStopping τ ↔ LatticeProb.IsWalkStopping τ := Iff.rfl

/-! ### Stopping at the exit from `D` -/

/-- The first time up to `t` at which the walk has left `D`, and `t + 1` if it
has not. -/
noncomputable def exitNat (D : Set (Site d)) (t : ℕ) (X : ℕ → Site d) : ℕ :=
  open Classical in
  if h : ∃ j, j ≤ t ∧ X j ∉ D then Nat.find h else t + 1

theorem exitNat_le_of {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d} {j : ℕ}
    (hjt : j ≤ t) (hj : X j ∉ D) : exitNat D t X ≤ j := by
  classical
  have hex : ∃ j, j ≤ t ∧ X j ∉ D := ⟨j, hjt, hj⟩
  unfold exitNat
  rw [dif_pos hex]
  exact Nat.find_le ⟨hjt, hj⟩

theorem mem_of_lt_exitNat {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d} {j : ℕ}
    (hj : j < exitNat D t X) (hjt : j ≤ t) : X j ∈ D := by
  by_contra hc
  have := exitNat_le_of hjt hc
  omega

theorem notMem_exitNat {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d}
    (h : exitNat D t X ≤ t) : X (exitNat D t X) ∉ D := by
  classical
  unfold exitNat at h ⊢
  split at h
  · rename_i hex
    rw [dif_pos hex]
    exact (Nat.find_spec hex).2
  · omega

/-- `exitNat` is settled by the positions up to the time in question. -/
theorem exitNat_congr {D : Set (Site d)} {t k : ℕ} {X Y : ℕ → Site d}
    (h : ∀ j ≤ k, X j = Y j) (hk : exitNat D t X = k) (hkt : k ≤ t) :
    exitNat D t Y = k := by
  refine le_antisymm (exitNat_le_of hkt ?_) ?_
  · rw [← h k le_rfl, ← hk]
    exact notMem_exitNat (by omega)
  · by_contra hc
    push Not at hc
    have hj : Y (exitNat D t Y) ∉ D :=
      notMem_exitNat (le_trans (le_of_lt hc) hkt)
    rw [← h _ (le_of_lt hc)] at hj
    have := exitNat_le_of (le_trans (le_of_lt hc) hkt) hj
    omega

/-! ### The localized value is at most the odometer -/

/-- The stopping time `τ ∧ τ_D`. -/
noncomputable def stopBeforeExit (D : Set (Site d)) (t : ℕ)
    (τ : (ℕ → Site d) → ℕ) (X : ℕ → Site d) : ℕ :=
  min (τ X) (exitNat D t X)

theorem stopBeforeExit_le {D : Set (Site d)} {t : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτt : ∀ X, τ X ≤ t) (X : ℕ → Site d) : stopBeforeExit D t τ X ≤ t :=
  le_trans (min_le_left _ _) (hτt X)

theorem isWalkStopping_stopBeforeExit {D : Set (Site d)} {t : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    IsWalkStopping (stopBeforeExit D t τ) := by
  intro k X Y hXY hk
  unfold stopBeforeExit at hk ⊢
  have hkt : k ≤ t := hk ▸ stopBeforeExit_le hτt X
  rcases le_or_gt (τ X) (exitNat D t X) with hcase | hcase
  · -- the stopping time comes first
    have hτX : τ X = k := by omega
    have hτY : τ Y = k := hτ k X Y hXY hτX
    have hge : k ≤ exitNat D t Y := by
      by_contra hc
      push Not at hc
      have hj : Y (exitNat D t Y) ∉ D := notMem_exitNat (by omega)
      rw [← hXY _ (by omega)] at hj
      have := exitNat_le_of (show exitNat D t Y ≤ t by omega) hj
      omega
    omega
  · -- the exit comes first
    have hexX : exitNat D t X = k := by omega
    have hexY : exitNat D t Y = k := exitNat_congr hXY hexX hkt
    have hτY : k < τ Y := by
      by_contra hc
      push Not at hc
      have := (hτ.le_iff k (fun j hj => (hXY j hj).symm)).mp hc
      omega
    omega

/-- The truncated scenery sum of `eq:localized-odometer` is the plain scenery sum
stopped at `τ ∧ τ_D`. -/
theorem localizedSum_eq (D : Set (Site d)) (t : ℕ) (ζ : Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτt : ∀ X, τ X ≤ t) (X : ℕ → Site d) :
    (∑ j ∈ Finset.range (τ X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
      = sceneryPartialSum ζ (stopBeforeExit D t τ X) X := by
  classical
  unfold sceneryPartialSum stopBeforeExit
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (τ X))
    (fun j => j < exitNat D t X)]
  have hfilt : (Finset.range (τ X)).filter (fun j => j < exitNat D t X)
      = Finset.range (min (τ X) (exitNat D t X)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have hin : ∀ j ∈ (Finset.range (τ X)).filter (fun j => j < exitNat D t X),
      Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j = ζ (X j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine Set.indicator_of_mem ?_ _
    intro i hi
    exact mem_of_lt_exitNat (D := D) (t := t) (by omega) (by have := hτt X; omega)
  have hout : ∀ j ∈ (Finset.range (τ X)).filter (fun j => ¬ j < exitNat D t X),
      Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j = 0 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hj
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact notMem_exitNat (by have := hτt X; omega)
      (hmem (exitNat D t X) hj.2)
  rw [Finset.sum_congr rfl hin, Finset.sum_congr rfl hout, Finset.sum_const_zero, add_zero,
    hfilt]

/-- The first half of `lem:localization-killing`: the localized value never
exceeds the odometer, because its values are a subset of the odometer's. -/
theorem localizedOdometer_le (hOS : External.OptimalStopping) (hd : 1 ≤ d)
    (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (x : Site d) (hx : x ∈ D) :
    localizedOdometer D ζ t x ≤ odometerOf ζ t x := by
  rw [(hOS d hd ζ t x).1]
  unfold localizedOdometer
  rw [Set.indicator_of_mem hx]
  show sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
      a = ∫ X, (∑ j ∈ Finset.range (τ X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
        ∂(walkLaw d x)} ≤ _
  refine csSup_le_csSup ?_ ?_ ?_
  · refine ⟨t * sceneryBound x t ζ, ?_⟩
    rintro a ⟨τ, hτ, hτt, rfl⟩
    exact le_trans (le_abs_self _) (abs_integral_stoppedScenery_le hd x ζ t hτ hτt)
  · exact ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le t, rfl⟩⟩
  · rintro a ⟨τ, hτ, hτt, rfl⟩
    refine ⟨stopBeforeExit D t τ, isWalkStopping_stopBeforeExit hτ hτt,
      stopBeforeExit_le hτt, ?_⟩
    exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
      localizedSum_eq D t ζ hτt X)

/-! ### Splitting a stopped sum at the exit

The paper bounds the reward collected after `τ_D` by `u_t(X_{τ_D})`, using the
strong Markov property at `τ_D` "inside" a supremum.  The library's
`markov_stopping_family` is the form that permits it: the functional of the
future may depend on the past, through the positions up to the stopping time.
What that functional is, here, is the residual scenery sum, whose length is the
residual stopping index of the path glued from the past and the future. -/

/-- The path whose first `k` positions are those of `X` and which continues along
`Y`.  For a path `X` and `Y` its own shift, this returns `X`. -/
def gluePath (k : ℕ) (X Y : ℕ → Site d) (j : ℕ) : Site d :=
  if j ≤ k then X j else Y (j - k)

theorem gluePath_of_le {k : ℕ} {X Y : ℕ → Site d} {j : ℕ} (h : j ≤ k) :
    gluePath k X Y j = X j := by simp [gluePath, h]

theorem gluePath_congr (k : ℕ) {X X' : ℕ → Site d} (h : ∀ j ≤ k, X j = X' j)
    (Y : ℕ → Site d) : gluePath k X Y = gluePath k X' Y := by
  funext j
  unfold gluePath
  split
  · rename_i hj; exact h j hj
  · rfl

/-- Gluing a path to its own shift returns the path. -/
theorem gluePath_shift (k : ℕ) (X : ℕ → Site d) :
    gluePath k X (LatticeProb.shiftPath k X) = X := by
  funext j
  unfold gluePath LatticeProb.shiftPath
  split
  · rfl
  · rename_i hj
    congr 1
    omega

/-- The residual stopping index after time `k`, as a functional of the future. -/
def residualStop (k : ℕ) (τ : (ℕ → Site d) → ℕ) (X Y : ℕ → Site d) : ℕ :=
  τ (gluePath k X Y) - k

/-- The residual index is a stopping time of the future. -/
theorem isWalkStopping_residualStop (k : ℕ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (X : ℕ → Site d) :
    IsWalkStopping (residualStop k τ X) := by
  intro m Y Y' hYY hm
  unfold residualStop at hm ⊢
  have hglue : ∀ j ≤ k + m, gluePath k X Y j = gluePath k X Y' j := by
    intro j hj
    unfold gluePath
    split
    · rfl
    · rename_i hjk
      exact hYY (j - k) (by omega)
  by_cases hk : τ (gluePath k X Y) ≤ k
  · -- the glued path stops at or before `k`, so the residual index is zero
    have hle : τ (gluePath k X Y) ≤ k + m := by omega
    have := hτ (τ (gluePath k X Y)) (gluePath k X Y) (gluePath k X Y')
      (fun j hj => hglue j (le_trans hj hle)) rfl
    omega
  · have heq : τ (gluePath k X Y) = k + m := by omega
    have := hτ (k + m) (gluePath k X Y) (gluePath k X Y') hglue heq
    omega

/-- The residual scenery sum after time `k`, of the length the glued path
prescribes, against a scenery truncated to a finite box so that it is bounded. -/
noncomputable def residualSum (s : Finset (Site d)) (ζ : Site d → ℝ) (k : ℕ)
    (τ : (ℕ → Site d) → ℕ) (X Y : ℕ → Site d) : ℝ :=
  ∑ i ∈ Finset.range (residualStop k τ X Y), trunc s ζ (Y i)

/-- The functional of the future that the strong Markov property is applied to:
the residual scenery sum, and zero on the event that the stopping time has
already occurred. -/
noncomputable def afterExit (s : Finset (Site d)) (ζ : Site d → ℝ)
    (τ : (ℕ → Site d) → ℕ) (k : ℕ) (X Y : ℕ → Site d) : ℝ :=
  if τ X = k then 0 else residualSum s ζ k τ X Y

theorem abs_afterExit_le (s : Finset (Site d)) (ζ : Site d → ℝ) {τ : (ℕ → Site d) → ℕ}
    {t : ℕ} (hτt : ∀ X, τ X ≤ t) {M : ℝ} (hM : ∀ y, |trunc s ζ y| ≤ M)
    (k : ℕ) (X Y : ℕ → Site d) : |afterExit s ζ τ k X Y| ≤ t * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  unfold afterExit
  split
  · simpa using mul_nonneg (Nat.cast_nonneg t) hM0
  · unfold residualSum
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun i _ => hM (Y i)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hM0
    have : residualStop k τ X Y ≤ t := by
      unfold residualStop
      have := hτt (gluePath k X Y)
      omega
    exact_mod_cast this

/-- The functional reads the past only through the positions up to the time. -/
theorem afterExit_past (s : Finset (Site d)) (ζ : Site d → ℝ) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (k : ℕ) (X X' Y : ℕ → Site d) (h : ∀ j ≤ k, X j = X' j) :
    afterExit s ζ τ k X Y = afterExit s ζ τ k X' Y := by
  unfold afterExit residualSum residualStop
  rw [gluePath_congr k h Y]
  by_cases hk : τ X = k
  · rw [if_pos hk, if_pos (hτ k X X' h hk)]
  · rw [if_neg hk, if_neg ?_]
    intro hk'
    exact hk (hτ k X' X (fun j hj => (h j hj).symm) hk')

/-- Gluing a path to its own shift makes the functional the residual scenery
sum along the path itself. -/
theorem afterExit_shift (s : Finset (Site d)) (ζ : Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (σ : (ℕ → Site d) → ℕ)
    (X : ℕ → Site d) :
    afterExit s ζ τ (σ X) X (LatticeProb.shiftPath (σ X) X)
      = ∑ i ∈ Finset.range (τ X - σ X), trunc s ζ (X (σ X + i)) := by
  unfold afterExit residualSum residualStop
  rw [gluePath_shift]
  by_cases hk : τ X = σ X
  · rw [if_pos hk, hk]
    simp
  · rw [if_neg hk]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem measurable_gluePath (k : ℕ) :
    Measurable fun p : (ℕ → Site d) × (ℕ → Site d) => gluePath k p.1 p.2 := by
  refine measurable_pi_lambda _ fun j => ?_
  unfold gluePath
  by_cases h : j ≤ k
  · simp only [if_pos h]
    exact (measurable_pi_apply j).comp measurable_fst
  · simp only [if_neg h]
    exact (measurable_pi_apply (j - k)).comp measurable_snd

theorem measurable_afterExit (s : Finset (Site d)) (ζ : Site d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) {t : ℕ} (hτt : ∀ X, τ X ≤ t) (k : ℕ) :
    Measurable (Function.uncurry (afterExit s ζ τ k)) := by
  classical
  have hτm : Measurable τ := measurable_of_isWalkStopping t hτ hτt
  have hres : Measurable fun p : (ℕ → Site d) × (ℕ → Site d) =>
      residualStop k τ p.1 p.2 :=
    (hτm.comp (measurable_gluePath k)).sub_const k
  have hτ1 : Measurable fun p : (ℕ → Site d) × (ℕ → Site d) => τ p.1 :=
    hτm.comp measurable_fst
  have hval : ∀ m : ℕ, Measurable fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ Finset.range m, trunc s ζ (p.2 i) := by
    intro m
    refine Finset.measurable_sum _ fun i _ => ?_
    have hi : Measurable fun p : (ℕ → Site d) × (ℕ → Site d) => p.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    have h : Measurable ((trunc s ζ) ∘ fun p : (ℕ → Site d) × (ℕ → Site d) => p.2 i) :=
      (measurable_of_countable _).comp hi
    exact h
  have hsplit : Function.uncurry (afterExit s ζ τ k)
      = fun p : (ℕ → Site d) × (ℕ → Site d) => ∑ m ∈ Finset.range (t + 1),
        (if τ p.1 ≠ k ∧ residualStop k τ p.1 p.2 = m then
          ∑ i ∈ Finset.range m, trunc s ζ (p.2 i) else 0) := by
    funext p
    obtain ⟨X, Y⟩ := p
    show afterExit s ζ τ k X Y = _
    have hle : residualStop k τ X Y ≤ t := by
      unfold residualStop
      have := hτt (gluePath k X Y)
      omega
    unfold afterExit residualSum
    by_cases hk : τ X = k
    · rw [if_pos hk]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      rw [if_neg (by tauto)]
    · rw [if_neg hk]
      symm
      refine (Finset.sum_eq_single (residualStop k τ X Y) ?_ ?_).trans ?_
      · intro m _ hm
        rw [if_neg (by tauto)]
      · intro hmem
        exact absurd (Finset.mem_range.mpr (by omega)) hmem
      · rw [if_pos ⟨hk, rfl⟩]
  rw [hsplit]
  refine Finset.measurable_sum _ fun m _ => ?_
  refine Measurable.ite ?_ (hval m) measurable_const
  exact ((hτ1 (measurableSet_singleton k)).compl).inter (hres (measurableSet_singleton m))


/-! ### Assembling the bound

The pieces above are put together as the paper's argument does.  For a bounded
stopping time `τ` write `σ = τ ∧ τ_D`.  The reward collected after `σ` is the
functional of the future built above; the Markov property at `σ` turns its
expectation into the expectation of an inner expectation started at `X_σ`, and
that inner expectation is one of the competitors in the optimal-stopping problem
at `X_σ`, so it is at most `u_t(X_σ)`.  On the event `σ = τ` there is no reward
to collect, and off it `σ` is the exit time, which is then at most `t`. -/

instance walkLaw_isProbabilityMeasure (d : ℕ) [NeZero d] (x : Site d) :
    IsProbabilityMeasure (walkLaw d x) := by
  rw [show walkLaw d x = LatticeProb.siteWalkLaw d x from rfl]
  infer_instance

/-- The confinement of the walk, read on path space rather than on increment
space. -/
theorem ae_boxDist_walk (hd : 1 ≤ d) (x : Site d) :
    ∀ᵐ X ∂(walkLaw d x), ∀ n : ℕ, boxDist x (X n) ≤ n := by
  have hmeas : MeasurableSet {X : ℕ → Site d | ∀ n : ℕ, boxDist x (X n) ≤ n} := by
    have hrw : {X : ℕ → Site d | ∀ n : ℕ, boxDist x (X n) ≤ n}
        = ⋂ n : ℕ, (fun X : ℕ → Site d => X n) ⁻¹' {y : Site d | boxDist x y ≤ n} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hrw]
    refine MeasurableSet.iInter fun n => (measurable_pi_apply n) ?_
    exact (Set.to_countable _).measurableSet
  rw [walkLaw, ae_map_iff (measurable_walkPath x).aemeasurable hmeas]
  exact ae_boxDist_walkPath hd x

/-! ### The exit time in `ℕ∞` and the exit index in `ℕ` -/

theorem exitNat_le_iff {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d} :
    exitNat D t X ≤ t ↔ ∃ j ≤ t, X j ∉ D := by
  constructor
  · intro h
    exact ⟨exitNat D t X, h, notMem_exitNat h⟩
  · rintro ⟨j, hj, hjD⟩
    exact le_trans (exitNat_le_of hj hjD) hj

theorem exitNat_eq_succ_of {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d}
    (h : ∀ j ≤ t, X j ∈ D) : exitNat D t X = t + 1 := by
  classical
  unfold exitNat
  rw [dif_neg]
  rintro ⟨j, hj, hjD⟩
  exact hjD (h j hj)

theorem exitNat_congr' {D : Set (Site d)} {t : ℕ} {X Y : ℕ → Site d}
    (h : ∀ j ≤ t, X j = Y j) : exitNat D t X = exitNat D t Y := by
  by_cases hc : exitNat D t X ≤ t
  · exact (exitNat_congr (D := D) (t := t) (k := exitNat D t X)
      (fun j hj => h j (le_trans hj hc)) rfl hc).symm
  · have hX : ∀ j ≤ t, X j ∈ D := by
      intro j hj
      by_contra hjD
      exact hc (le_trans (exitNat_le_of hj hjD) hj)
    have hY : ∀ j ≤ t, Y j ∈ D := by
      intro j hj
      rw [← h j hj]
      exact hX j hj
    rw [exitNat_eq_succ_of hX, exitNat_eq_succ_of hY]

/-- On the event that the walk has left `D` by time `t`, the exit time in `ℕ∞`
is the exit index in `ℕ`. -/
theorem exitTime_eq_exitNat {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d}
    (h : exitNat D t X ≤ t) : exitTime D X = (exitNat D t X : ℕ∞) := by
  refine le_antisymm (sInf_le ⟨exitNat D t X, rfl, notMem_exitNat h⟩) ?_
  refine le_sInf ?_
  rintro k ⟨n, rfl, hn⟩
  have hle : exitNat D t X ≤ n := by
    by_contra hc
    exact hn (mem_of_lt_exitNat (D := D) (t := t) (X := X) (j := n) (by omega) (by omega))
  exact_mod_cast hle

theorem exitTime_le_iff {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d} :
    exitTime D X ≤ (t : ℕ∞) ↔ exitNat D t X ≤ t := by
  constructor
  · intro h
    by_contra hc
    have hno : ∀ j ≤ t, X j ∈ D := by
      intro j hj
      by_contra hjD
      exact hc (le_trans (exitNat_le_of hj hjD) hj)
    have hlb : ((t + 1 : ℕ) : ℕ∞) ≤ exitTime D X := by
      refine le_sInf ?_
      rintro k ⟨n, rfl, hn⟩
      have hlt : t < n := by
        by_contra hcc
        exact hn (hno n (by omega : n ≤ t))
      exact_mod_cast hlt
    have hcontra : ((t + 1 : ℕ) : ℕ∞) ≤ ((t : ℕ) : ℕ∞) := le_trans hlb h
    have : t + 1 ≤ t := by exact_mod_cast hcontra
    omega
  · intro h
    rw [exitTime_eq_exitNat h]
    exact_mod_cast h


/-! ### The reward at the exit -/

/-- The integrand on the right of `lem:localization-killing`. -/
noncomputable def exitReward (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ)
    (X : ℕ → Site d) : ℝ :=
  Set.indicator {X : ℕ → Site d | exitTime D X ≤ (t : ℕ∞)}
    (fun X => odometerOf ζ t (X (exitTime D X).toNat)) X

theorem exitReward_of_le {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d}
    (ζ : Site d → ℝ) (h : exitNat D t X ≤ t) :
    exitReward D ζ t X = odometerOf ζ t (X (exitNat D t X)) := by
  unfold exitReward
  have hmem : X ∈ {X : ℕ → Site d | exitTime D X ≤ (t : ℕ∞)} := exitTime_le_iff.mpr h
  rw [Set.indicator_of_mem hmem, exitTime_eq_exitNat h]
  simp

theorem exitReward_of_not_le {D : Set (Site d)} {t : ℕ} {X : ℕ → Site d}
    (ζ : Site d → ℝ) (h : ¬ exitNat D t X ≤ t) : exitReward D ζ t X = 0 := by
  unfold exitReward
  have hmem : X ∉ {X : ℕ → Site d | exitTime D X ≤ (t : ℕ∞)} :=
    fun hc => h (exitTime_le_iff.mp hc)
  exact Set.indicator_of_notMem hmem _

theorem exitReward_nonneg (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (X : ℕ → Site d) :
    0 ≤ exitReward D ζ t X := by
  by_cases h : exitNat D t X ≤ t
  · rw [exitReward_of_le ζ h]; exact odometerOf_nonneg _ _ _
  · rw [exitReward_of_not_le ζ h]

theorem measurable_exitReward (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) :
    Measurable (exitReward D ζ t) := by
  refine measurable_of_dependsOn t _ fun X Y h => ?_
  have hex : exitNat D t X = exitNat D t Y := exitNat_congr' h
  by_cases hc : exitNat D t X ≤ t
  · rw [exitReward_of_le ζ hc, exitReward_of_le ζ (hex ▸ hc), ← hex, h _ hc]
  · rw [exitReward_of_not_le ζ hc, exitReward_of_not_le ζ (hex ▸ hc)]

/-- A bound for the odometer on the box the walk cannot leave by time `t`. -/
noncomputable def odometerBound (x : Site d) (t : ℕ) (ζ : Site d → ℝ) : ℝ :=
  ∑ z ∈ boxFinset x t, |odometerOf ζ t z|

theorem integrable_exitReward (hd : 1 ≤ d) (x : Site d) (D : Set (Site d))
    (ζ : Site d → ℝ) (t : ℕ) :
    Integrable (exitReward D ζ t) (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const (odometerBound x t ζ)).mono'
    (measurable_exitReward D ζ t).aestronglyMeasurable ?_
  filter_upwards [ae_boxDist_walk hd x] with X hX
  rw [Real.norm_eq_abs]
  by_cases hc : exitNat D t X ≤ t
  · rw [exitReward_of_le ζ hc]
    exact le_sum_abs_of_mem (mem_boxFinset (le_trans (hX _) hc))
  · rw [exitReward_of_not_le ζ hc, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem integrable_stoppedScenery_walk (hd : 1 ≤ d) (x : Site d) (ζ : Site d → ℝ) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Integrable (fun X => sceneryPartialSum ζ (τ X) X) (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  refine (integrable_const (t * sceneryBound x t ζ)).mono'
    (measurable_stoppedScenery t ζ hτ hτt).aestronglyMeasurable ?_
  filter_upwards [ae_boxDist_walk hd x] with X hX
  rw [Real.norm_eq_abs]
  calc |sceneryPartialSum ζ (τ X) X|
      ≤ ∑ k ∈ Finset.range (τ X), |ζ (X k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (τ X), sceneryBound x t ζ := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkt : k ≤ t := by have := Finset.mem_range.mp hk; have := hτt X; omega
        exact le_sum_abs_of_mem (mem_boxFinset (le_trans (hX k) hkt))
    _ = (τ X : ℝ) * sceneryBound x t ζ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ t * sceneryBound x t ζ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hτt X) (sceneryBound_nonneg x t ζ)

/-- Every competitor in the optimal-stopping problem is at most the odometer. -/
theorem integral_stoppedScenery_le_odometer (hOS : External.OptimalStopping) (hd : 1 ≤ d)
    (ζ : Site d → ℝ) (t : ℕ) (y : Site d) {ρ : (ℕ → Site d) → ℕ}
    (hρ : IsWalkStopping ρ) (hρt : ∀ Y, ρ Y ≤ t) :
    ∫ Y, sceneryPartialSum ζ (ρ Y) Y ∂(walkLaw d y) ≤ odometerOf ζ t y := by
  rw [(hOS d hd ζ t y).1]
  refine le_csSup ⟨t * sceneryBound y t ζ, ?_⟩ ⟨ρ, hρ, hρt, rfl⟩
  rintro a ⟨τ', hτ', hτ't, rfl⟩
  exact le_trans (le_abs_self _) (abs_integral_stoppedScenery_le hd y ζ t hτ' hτ't)


/-- The reward collected between `τ ∧ τ_D` and `τ` is at most the odometer read
at the exit.  This is the Markov property at `τ ∧ τ_D`, applied to the residual
scenery sum, whose inner expectation is a competitor in the optimal-stopping
problem started at the exit position. -/
theorem integral_stopped_sub_le (hOS : External.OptimalStopping) (hd : 1 ≤ d)
    (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (x : Site d)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x))
        - (∫ X, sceneryPartialSum ζ (stopBeforeExit D t τ X) X ∂(walkLaw d x))
      ≤ ∫ X, exitReward D ζ t X ∂(walkLaw d x) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set σ := stopBeforeExit D t τ with hσdef
  have hσ : IsWalkStopping σ := isWalkStopping_stopBeforeExit hτ hτt
  have hσt : ∀ X, σ X ≤ t := stopBeforeExit_le hτt
  have hσle : ∀ X, σ X ≤ τ X := fun X => min_le_left _ _
  have hmin : ∀ X, σ X = min (τ X) (exitNat D t X) := fun _ => rfl
  set s := boxFinset x (2 * t) with hsdef
  obtain ⟨M, hM⟩ := exists_bound_trunc s ζ
  have hmk := LatticeProb.markov_stopping_family d t x σ hσ hσt (afterExit s ζ τ)
    (fun k => measurable_afterExit s ζ hτ hτt k)
    (C := t * M) (fun k X Y => by
      rw [Real.norm_eq_abs]; exact abs_afterExit_le s ζ hτt hM k X Y)
    (fun k X X' Y h => afterExit_past s ζ hτ k X X' Y h)
  simp only [show ∀ y : Site d, LatticeProb.siteWalkLaw d y = walkLaw d y from
    fun _ => rfl] at hmk
  -- the left side is the difference of the two stopped scenery sums
  have hA : ∫ X, afterExit s ζ τ (σ X) X (LatticeProb.shiftPath (σ X) X) ∂(walkLaw d x)
      = (∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x))
        - ∫ X, sceneryPartialSum ζ (σ X) X ∂(walkLaw d x) := by
    rw [← integral_sub (integrable_stoppedScenery_walk hd x ζ t hτ hτt)
      (integrable_stoppedScenery_walk hd x ζ t hσ hσt)]
    refine integral_congr_ae ?_
    filter_upwards [ae_boxDist_walk hd x] with X hX
    rw [afterExit_shift s ζ σ X]
    have hsite : ∀ i ∈ Finset.range (τ X - σ X),
        trunc s ζ (X (σ X + i)) = ζ (X (σ X + i)) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hle : σ X + i ≤ t := by have := hτt X; omega
      exact trunc_eq_of_mem (mem_boxFinset (le_trans (hX _) (by omega)))
    rw [Finset.sum_congr rfl hsite]
    have hdec : τ X = σ X + (τ X - σ X) := by have := hσle X; omega
    show _ = sceneryPartialSum ζ (τ X) X - sceneryPartialSum ζ (σ X) X
    unfold sceneryPartialSum
    conv_rhs => rw [hdec]
    rw [Finset.sum_range_add]
    ring
  -- the right side is at most the reward at the exit
  have hdep : ∀ X X' : ℕ → Site d, (∀ j ≤ t, X j = X' j) →
      (∫ Y, afterExit s ζ τ (σ X) X Y ∂(walkLaw d (X (σ X))))
        = ∫ Y, afterExit s ζ τ (σ X') X' Y ∂(walkLaw d (X' (σ X'))) := by
    intro X X' h
    have hσ' : σ X = σ X' := isWalkStopping_dependsOn hσ hσt X X' h
    have hpt : X (σ X) = X' (σ X) := h (σ X) (hσt X)
    rw [← hσ', ← hpt]
    exact integral_congr_ae (Filter.Eventually.of_forall fun Y =>
      afterExit_past s ζ hτ (σ X) X X' Y (fun j hj => h j (le_trans hj (hσt X))))
  have hbd : ∀ X : ℕ → Site d,
      |∫ Y, afterExit s ζ τ (σ X) X Y ∂(walkLaw d (X (σ X)))| ≤ t * M := by
    intro X
    have h := norm_integral_le_of_norm_le_const (μ := walkLaw d (X (σ X)))
      (f := fun Y => afterExit s ζ τ (σ X) X Y) (C := t * M)
      (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs]; exact abs_afterExit_le s ζ hτt hM _ X Y)
    simpa [Real.norm_eq_abs, Measure.real] using h
  have hintI : Integrable
      (fun X => ∫ Y, afterExit s ζ τ (σ X) X Y ∂(walkLaw d (X (σ X)))) (walkLaw d x) := by
    refine (integrable_const (t * M)).mono'
      (measurable_of_dependsOn t _ hdep).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact hbd X
  have hB : (∫ X, (∫ Y, afterExit s ζ τ (σ X) X Y ∂(walkLaw d (X (σ X)))) ∂(walkLaw d x))
      ≤ ∫ X, exitReward D ζ t X ∂(walkLaw d x) := by
    refine integral_mono_ae hintI (integrable_exitReward hd x D ζ t) ?_
    filter_upwards [ae_boxDist_walk hd x] with X hX
    by_cases hcase : τ X = σ X
    · have hzero : ∀ Y : ℕ → Site d, afterExit s ζ τ (σ X) X Y = 0 := by
        intro Y
        unfold afterExit
        rw [if_pos hcase]
      simp only [hzero, integral_zero]
      exact exitReward_nonneg D ζ t X
    · have hex : exitNat D t X < τ X := by have := hmin X; omega
      have hexle : exitNat D t X ≤ t := by have := hτt X; omega
      have hσv : σ X = exitNat D t X := by have := hmin X; omega
      rw [exitReward_of_le ζ hexle, ← hσv]
      have hρ : IsWalkStopping (residualStop (σ X) τ X) :=
        isWalkStopping_residualStop (σ X) hτ X
      have hρt : ∀ Y, residualStop (σ X) τ X Y ≤ t := by
        intro Y
        have := hτt (gluePath (σ X) X Y)
        unfold residualStop
        omega
      have heq : (∫ Y, afterExit s ζ τ (σ X) X Y ∂(walkLaw d (X (σ X))))
          = ∫ Y, sceneryPartialSum ζ (residualStop (σ X) τ X Y) Y
              ∂(walkLaw d (X (σ X))) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_boxDist_walk hd (X (σ X))] with Y hY
        unfold afterExit
        rw [if_neg hcase]
        unfold residualSum sceneryPartialSum
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        have hit : i ≤ t := by have := hρt Y; omega
        refine trunc_eq_of_mem (mem_boxFinset ?_)
        calc boxDist x (Y i) ≤ boxDist x (X (σ X)) + boxDist (X (σ X)) (Y i) :=
              boxDist_trans _ _ _
          _ ≤ t + t := add_le_add (le_trans (hX _) (hσt X)) (le_trans (hY i) hit)
          _ ≤ 2 * t := by omega
      rw [heq]
      exact integral_stoppedScenery_le_odometer hOS hd ζ t (X (σ X)) hρ hρt
  rw [← hA, hmk]
  exact hB


/-- Every stopped-before-the-exit scenery sum is a competitor in the localized
optimal-stopping problem. -/
theorem localizedValue_le (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ)
    (x : Site d) (hx : x ∈ D) {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, sceneryPartialSum ζ (stopBeforeExit D t τ X) X ∂(walkLaw d x))
      ≤ localizedOdometer D ζ t x := by
  unfold localizedOdometer
  rw [Set.indicator_of_mem hx]
  show _ ≤ sSup {a : ℝ | ∃ τ' : (ℕ → Site d) → ℕ, IsWalkStopping τ' ∧ (∀ X, τ' X ≤ t) ∧
      a = ∫ X, (∑ j ∈ Finset.range (τ' X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
        ∂(walkLaw d x)}
  refine le_csSup ⟨t * sceneryBound x t ζ, ?_⟩ ⟨τ, hτ, hτt, ?_⟩
  · rintro a ⟨τ', hτ', hτ't, rfl⟩
    rw [integral_congr_ae (Filter.Eventually.of_forall fun X => localizedSum_eq D t ζ hτ't X)]
    exact le_trans (le_abs_self _) (abs_integral_stoppedScenery_le hd x ζ t
      (isWalkStopping_stopBeforeExit hτ' hτ't) (stopBeforeExit_le hτ't))
  · exact integral_congr_ae
      (Filter.Eventually.of_forall fun X => (localizedSum_eq D t ζ hτt X).symm)


/-! ### The localized value as a function of the scenery

The localized value is a supremum over an uncountable family of stopping times,
so it is not measurable in the scenery for any formal reason.  It is, however,
Lipschitz in the scenery on the box the walk cannot leave, uniformly in the
stopping time, so the supremum is Lipschitz too, hence continuous, hence
measurable.  That is what makes the integrals of `cor:mean-localization`
genuine rather than junk zeros. -/

/-- The set of values of the localized optimal-stopping problem, written with
the plain scenery sum stopped at `τ ∧ τ_D`. -/
def localizedSet (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (x : Site d) : Set ℝ :=
  {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
    a = ∫ X, sceneryPartialSum ζ (stopBeforeExit D t τ X) X ∂(walkLaw d x)}

theorem localizedSet_nonempty (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (x : Site d) :
    (localizedSet D ζ t x).Nonempty :=
  ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le t, rfl⟩⟩

theorem bddAbove_localizedSet (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ)
    (x : Site d) : BddAbove (localizedSet D ζ t x) := by
  refine ⟨t * sceneryBound x t ζ, ?_⟩
  rintro a ⟨τ, hτ, hτt, rfl⟩
  exact le_trans (le_abs_self _) (abs_integral_stoppedScenery_le hd x ζ t
    (isWalkStopping_stopBeforeExit hτ hτt) (stopBeforeExit_le hτt))

theorem localizedOdometer_eq_sSup (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ)
    (x : Site d) (hx : x ∈ D) :
    localizedOdometer D ζ t x = sSup (localizedSet D ζ t x) := by
  unfold localizedOdometer
  rw [Set.indicator_of_mem hx]
  have hset : {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
      a = ∫ X, (∑ j ∈ Finset.range (τ X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
        ∂(walkLaw d x)} = localizedSet D ζ t x := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτt, rfl⟩
      exact ⟨τ, hτ, hτt,
        integral_congr_ae (Filter.Eventually.of_forall fun X => localizedSum_eq D t ζ hτt X)⟩
    · rintro ⟨τ, hτ, hτt, rfl⟩
      exact ⟨τ, hτ, hτt,
        integral_congr_ae
          (Filter.Eventually.of_forall fun X => (localizedSum_eq D t ζ hτt X).symm)⟩
  show sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
      a = ∫ X, (∑ j ∈ Finset.range (τ X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
        ∂(walkLaw d x)} = _
  rw [hset]

/-- One competitor moves by at most the Lipschitz amount when the scenery does. -/
theorem abs_integral_stoppedScenery_sub_le (hd : 1 ≤ d) (x : Site d) (ζ η : Site d → ℝ)
    (t : ℕ) {ρ : (ℕ → Site d) → ℕ} (hρ : IsWalkStopping ρ) (hρt : ∀ X, ρ X ≤ t) :
    |(∫ X, sceneryPartialSum ζ (ρ X) X ∂(walkLaw d x))
        - ∫ X, sceneryPartialSum η (ρ X) X ∂(walkLaw d x)|
      ≤ t * ∑ y ∈ boxFinset x t, |ζ y - η y| := by
  haveI : NeZero d := ⟨by omega⟩
  rw [← integral_sub (integrable_stoppedScenery_walk hd x ζ t hρ hρt)
    (integrable_stoppedScenery_walk hd x η t hρ hρt)]
  have hpt : ∀ X : ℕ → Site d,
      sceneryPartialSum ζ (ρ X) X - sceneryPartialSum η (ρ X) X
        = sceneryPartialSum (fun y => ζ y - η y) (ρ X) X := by
    intro X
    unfold sceneryPartialSum
    rw [← Finset.sum_sub_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact abs_integral_stoppedScenery_le hd x (fun y => ζ y - η y) t hρ hρt

theorem sSup_le_sSup_add {A B : Set ℝ} (hA : A.Nonempty) (hBb : BddAbove B) (K : ℝ)
    (h : ∀ a ∈ A, ∃ b ∈ B, a ≤ b + K) : sSup A ≤ sSup B + K := by
  refine csSup_le hA fun a ha => ?_
  obtain ⟨b, hb, hab⟩ := h a ha
  have := le_csSup hBb hb
  linarith

/-- The localized value is Lipschitz in the scenery on the box the walk cannot
leave, with constant `t`. -/
theorem abs_localizedOdometer_sub_le (hd : 1 ≤ d) (D : Set (Site d)) (ζ η : Site d → ℝ)
    (t : ℕ) (x : Site d) :
    |localizedOdometer D ζ t x - localizedOdometer D η t x|
      ≤ t * ∑ y ∈ boxFinset x t, |ζ y - η y| := by
  have hK : 0 ≤ t * ∑ y ∈ boxFinset x t, |ζ y - η y| :=
    mul_nonneg (Nat.cast_nonneg t) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  by_cases hx : x ∈ D
  · have hstep : ∀ ζ' η' : Site d → ℝ,
        sSup (localizedSet D ζ' t x)
          ≤ sSup (localizedSet D η' t x) + t * ∑ y ∈ boxFinset x t, |ζ' y - η' y| := by
      intro ζ' η'
      refine sSup_le_sSup_add (localizedSet_nonempty D ζ' t x)
        (bddAbove_localizedSet hd D η' t x) _ ?_
      rintro a ⟨τ, hτ, hτt, rfl⟩
      refine ⟨_, ⟨τ, hτ, hτt, rfl⟩, ?_⟩
      have h := abs_integral_stoppedScenery_sub_le hd x ζ' η' t
        (ρ := stopBeforeExit D t τ)
        (isWalkStopping_stopBeforeExit hτ hτt) (stopBeforeExit_le hτt)
      have := abs_le.mp h
      linarith [this.2]
    have hsym : ∀ y : Site d, |η y - ζ y| = |ζ y - η y| := fun y => abs_sub_comm _ _
    rw [localizedOdometer_eq_sSup D ζ t x hx, localizedOdometer_eq_sSup D η t x hx]
    have h1 := hstep ζ η
    have h2 := hstep η ζ
    rw [Finset.sum_congr rfl fun y _ => hsym y] at h2
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  · rw [localizedOdometer, localizedOdometer, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx]
    simpa using hK

theorem continuous_localizedOdometer (hd : 1 ≤ d) (D : Set (Site d)) (t : ℕ) (x : Site d) :
    Continuous fun ζ : Site d → ℝ => localizedOdometer D ζ t x := by
  rw [continuous_iff_continuousAt]
  intro ζ
  have hH : Continuous fun η : Site d → ℝ => (t : ℝ) * ∑ y ∈ boxFinset x t, |η y - ζ y| := by
    refine continuous_const.mul (continuous_finsetSum _ fun y _ => ?_)
    exact ((continuous_apply y).sub continuous_const).abs
  have hH0 : ((t : ℝ) * ∑ y ∈ boxFinset x t, |ζ y - ζ y|) = 0 := by simp
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have htend : Filter.Tendsto
      (fun η : Site d → ℝ => (t : ℝ) * ∑ y ∈ boxFinset x t, |η y - ζ y|) (nhds ζ) (nhds 0) := by
    have := hH.continuousAt (x := ζ)
    rwa [ContinuousAt, hH0] at this
  filter_upwards [htend (gt_mem_nhds hε)] with η hη
  rw [Real.dist_eq]
  refine lt_of_le_of_lt ?_ hη
  have := abs_localizedOdometer_sub_le hd D η ζ t x
  simpa using this

theorem measurable_localizedOdometer (hd : 1 ≤ d) (D : Set (Site d)) (t : ℕ) (x : Site d) :
    Measurable fun ζ : Site d → ℝ => localizedOdometer D ζ t x :=
  (continuous_localizedOdometer hd D t x).measurable

theorem localizedOdometer_nonneg (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ)
    (x : Site d) : 0 ≤ localizedOdometer D ζ t x := by
  by_cases hx : x ∈ D
  · rw [localizedOdometer_eq_sSup D ζ t x hx]
    refine le_csSup (bddAbove_localizedSet hd D ζ t x) ?_
    refine ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le t, ?_⟩
    have : ∀ X : ℕ → Site d, sceneryPartialSum ζ (stopBeforeExit D t (fun _ => 0) X) X = 0 := by
      intro X
      unfold stopBeforeExit sceneryPartialSum
      simp
    simp [integral_congr_ae (Filter.Eventually.of_forall this)]
  · rw [localizedOdometer, Set.indicator_of_notMem hx]


/-- The pathwise localization bound: the odometer exceeds its localized version
by at most the expected odometer at the exit.  This is the second half of
`lem:localization-killing`. -/
theorem odometerOf_sub_localizedOdometer_le (hOS : External.OptimalStopping) (hd : 1 ≤ d)
    (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (x : Site d) (hx : x ∈ D) :
    odometerOf ζ t x - localizedOdometer D ζ t x
      ≤ ∫ X, exitReward D ζ t X ∂(walkLaw d x) := by
  rw [sub_le_iff_le_add, (hOS d hd ζ t x).1]
  show sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ t) ∧
      a = ∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x)} ≤ _
  refine csSup_le ⟨_, stoppingSup_mem t x (sceneryPartialSum ζ)⟩ ?_
  rintro a ⟨τ, hτ, hτt, rfl⟩
  have h1 := integral_stopped_sub_le hOS hd D ζ t x hτ hτt
  have h2 := localizedValue_le hd D ζ t x hx hτ hτt
  linarith


theorem localizedOdometer_zero (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (x : Site d) : localizedOdometer D ζ 0 x = 0 := by
  by_cases hx : x ∈ D
  · refine le_antisymm ?_ (localizedOdometer_nonneg hd D ζ 0 x)
    have h := localizedOdometer_le External.optimalStopping hd D ζ 0 x hx
    simpa [odometerOf] using h
  · rw [localizedOdometer, Set.indicator_of_notMem hx]

end Sandpile
