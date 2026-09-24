/-
Taking expectations in `lem:localization-killing`.

The bound of that lemma is an expectation over the walk of the odometer read at
the exit position, and the odometer there is still a function of the scenery.
Averaging over the scenery therefore asks for the two integrals to be exchanged.
Once they are, the inner scenery average of the odometer no longer depends on
the exit position, by stationarity, and what is left is the mean odometer times
the probability that the walk has left the domain.

The scenery law is an arbitrary stationary law whose positive part at the origin
is integrable, as in the paper.  Independence of the scenery is used nowhere: the
exchange of the integrals needs only that the scenery law is a probability
measure, and the exit position is then removed by translation invariance.  The
statements for the i.i.d. law are the instances at `LatticeProb.iidLaw d ν`
(`isStationary_iidLaw`).
-/
import Sandpile.Support.Localization
import Sandpile.External.BPSHProved
import Sandpile.Support.Stationary

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- A functional of the path reading only the first `t + 1` positions is
measurable, whatever its codomain: those positions range over a countable
space. -/
theorem measurable_of_dependsOn' {α : Type*} [MeasurableSpace α] (t : ℕ)
    (F : (ℕ → Site d) → α)
    (hF : ∀ X Y : ℕ → Site d, (∀ j ≤ t, X j = Y j) → F X = F Y) : Measurable F := by
  have hrep : F = (fun u : ↥(Finset.range (t + 1)) → Site d =>
      F (extendPrefix (t + 1) u)) ∘ (Finset.range (t + 1)).restrict := by
    funext X
    refine hF X _ fun j hj => ?_
    have hmem : j ∈ Finset.range (t + 1) := Finset.mem_range.mpr (by omega)
    simp [extendPrefix, hmem, Finset.restrict]
  rw [hrep]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict _)

theorem measurable_exitNat (D : Set (Site d)) (t : ℕ) : Measurable (exitNat D t) :=
  measurable_of_dependsOn' t _ fun _ _ h => exitNat_congr' h

theorem measurableSet_exited (D : Set (Site d)) (t : ℕ) :
    MeasurableSet {X : ℕ → Site d | exitNat D t X ≤ t} :=
  measurable_exitNat D t measurableSet_Iic

/-- The reward at the exit, decomposed over the finitely many times the exit can
occur. -/
theorem exitReward_eq_sum (D : Set (Site d)) (ζ : Site d → ℝ) (t : ℕ) (X : ℕ → Site d) :
    exitReward D ζ t X = ∑ m ∈ Finset.range (t + 1),
      (if exitNat D t X = m then odometerOf ζ t (X m) else 0) := by
  classical
  by_cases hc : exitNat D t X ≤ t
  · rw [exitReward_of_le ζ hc]
    symm
    rw [Finset.sum_eq_single (exitNat D t X)
      (fun m _ hm => if_neg (fun hcc => hm hcc.symm))
      (fun hmem => absurd (Finset.mem_range.mpr (by omega)) hmem)]
    exact if_pos rfl
  · rw [exitReward_of_not_le ζ hc]
    refine (Finset.sum_eq_zero fun m hm => ?_).symm
    have := Finset.mem_range.mp hm
    rw [if_neg (by omega)]

theorem measurable_uncurry_exitReward (D : Set (Site d)) (t : ℕ) :
    Measurable fun p : (Site d → ℝ) × (ℕ → Site d) => exitReward D p.1 t p.2 := by
  classical
  have hsite : ∀ m : ℕ, Measurable
      fun p : (Site d → ℝ) × (ℕ → Site d) => odometerOf p.1 t (p.2 m) := by
    intro m
    have hpair : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) => (p.1, p.2 m) :=
      measurable_fst.prodMk ((measurable_pi_apply m).comp measurable_snd)
    have hcount : Measurable fun q : (Site d → ℝ) × Site d => odometerOf q.1 t q.2 :=
      measurable_from_prod_countable_left fun z => measurable_odometerOf t z
    exact hcount.comp hpair
  have hset : ∀ m : ℕ,
      MeasurableSet {p : (Site d → ℝ) × (ℕ → Site d) | exitNat D t p.2 = m} :=
    fun m => (measurable_exitNat D t).comp measurable_snd (measurableSet_singleton m)
  have hrw : (fun p : (Site d → ℝ) × (ℕ → Site d) => exitReward D p.1 t p.2)
      = fun p => ∑ m ∈ Finset.range (t + 1),
        (if exitNat D t p.2 = m then odometerOf p.1 t (p.2 m) else 0) := by
    funext p
    exact exitReward_eq_sum D p.1 t p.2
  rw [hrw]
  exact Finset.measurable_sum _ fun m _ =>
    Measurable.ite (hset m) (hsite m) measurable_const

/-- The walk is confined to the box of radius `n` at time `n`, on the product of
the scenery law with the walk law. -/
theorem ae_prod_boxDist (hd : 1 ≤ d) (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (x : Site d) :
    ∀ᵐ p ∂(μ.prod (walkLaw d x)), ∀ n : ℕ, boxDist x (p.2 n) ≤ n := by
  haveI : NeZero d := ⟨by omega⟩
  rw [MeasureTheory.ae_iff]
  have hset : {p : (Site d → ℝ) × (ℕ → Site d) | ¬ ∀ n : ℕ, boxDist x (p.2 n) ≤ n}
      = (Set.univ : Set (Site d → ℝ)) ×ˢ
        {X : ℕ → Site d | ¬ ∀ n : ℕ, boxDist x (X n) ≤ n} := by
    ext p
    simp
  rw [hset, Measure.prod_prod, MeasureTheory.ae_iff.mp (ae_boxDist_walk hd x), mul_zero]

theorem integrable_comp_fst {μ : Measure (Site d → ℝ)} [IsProbabilityMeasure μ]
    {ν : Measure (ℕ → Site d)} [IsProbabilityMeasure ν] {H : (Site d → ℝ) → ℝ}
    (hH : Integrable H μ) : Integrable (fun p : (Site d → ℝ) × (ℕ → Site d) => H p.1) (μ.prod ν) := by
  have hmapfst : (μ.prod ν).map Prod.fst = μ := Measure.fst_prod
  have hasm : AEStronglyMeasurable H ((μ.prod ν).map Prod.fst) := by
    rw [hmapfst]; exact hH.aestronglyMeasurable
  show Integrable (H ∘ Prod.fst) _
  refine (integrable_map_measure hasm measurable_fst.aemeasurable).mp ?_
  rw [hmapfst]
  exact hH

theorem integrable_prod_exitReward (hd : 1 ≤ d) (P : Measure (Site d → ℝ))
    [IsProbabilityMeasure P] (hstat : IsStationary d P)
    (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (D : Set (Site d)) (t : ℕ) (x : Site d) :
    Integrable (fun p : (Site d → ℝ) × (ℕ → Site d) => exitReward D p.1 t p.2)
      (P.prod (walkLaw d x)) := by
  haveI : NeZero d := ⟨by omega⟩
  have hH : Integrable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset x t, odometerOf ζ t z) P :=
    integrable_finsetSum _ fun z _ => integrable_odometerOf_of_stationary hstat hpos t z
  refine Integrable.mono' (integrable_comp_fst hH)
    (measurable_uncurry_exitReward D t).aestronglyMeasurable ?_
  filter_upwards [ae_prod_boxDist hd P x] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (exitReward_nonneg D p.1 t p.2)]
  by_cases hc : exitNat D t p.2 ≤ t
  · rw [exitReward_of_le p.1 hc]
    exact Finset.single_le_sum (f := fun z => odometerOf p.1 t z)
      (fun z _ => odometerOf_nonneg _ _ _) (mem_boxFinset (le_trans (hp _) hc))
  · rw [exitReward_of_not_le p.1 hc]
    exact Finset.sum_nonneg fun z _ => odometerOf_nonneg _ _ _

/-- The scenery average of the reward at the exit: by stationarity it no longer
sees the exit position. -/
theorem integral_exitReward_scenery {P : Measure (Site d → ℝ)} (hstat : IsStationary d P)
    (D : Set (Site d)) (t : ℕ) (X : ℕ → Site d) :
    (∫ ζ, exitReward D ζ t X ∂P)
      = Set.indicator {X : ℕ → Site d | exitNat D t X ≤ t}
          (fun _ => ∫ ζ, odometerOf ζ t 0 ∂P) X := by
  by_cases hc : exitNat D t X ≤ t
  · have hmem : X ∈ {X : ℕ → Site d | exitNat D t X ≤ t} := hc
    rw [Set.indicator_of_mem hmem,
      integral_congr_ae (Filter.Eventually.of_forall fun ζ => exitReward_of_le ζ hc)]
    exact integral_odometerOf_eq_of_stationary hstat t _
  · have hmem : X ∉ {X : ℕ → Site d | exitNat D t X ≤ t} := hc
    rw [Set.indicator_of_notMem hmem,
      integral_congr_ae (Filter.Eventually.of_forall fun ζ => exitReward_of_not_le ζ hc),
      integral_zero]

/-- Averaging the localization bound over the scenery. -/
theorem integral_integral_exitReward (hd : 1 ≤ d) (P : Measure (Site d → ℝ))
    [IsProbabilityMeasure P] (hstat : IsStationary d P)
    (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (D : Set (Site d)) (t : ℕ) (x : Site d) :
    (∫ ζ, (∫ X, exitReward D ζ t X ∂(walkLaw d x)) ∂P)
      = ((walkLaw d x) {X : ℕ → Site d | exitNat D t X ≤ t}).toReal *
        ∫ ζ, odometerOf ζ t 0 ∂P := by
  haveI : NeZero d := ⟨by omega⟩
  rw [integral_integral_swap (integrable_prod_exitReward hd P hstat hpos D t x),
    integral_congr_ae (Filter.Eventually.of_forall fun X =>
      integral_exitReward_scenery hstat D t X),
    integral_indicator_const _ (measurableSet_exited D t), smul_eq_mul, Measure.real]

/-- The localized odometer is integrable in the scenery under a stationary law
whose scenery at the origin has an integrable positive part. -/
theorem integrable_localizedOdometer_of_stationary (hd : 1 ≤ d)
    {P : Measure (Site d → ℝ)} (hstat : IsStationary d P)
    (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (D : Set (Site d)) (t : ℕ) (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => localizedOdometer D ζ t x) P := by
  refine Integrable.mono' (integrable_odometerOf_of_stationary hstat hpos t x)
    (measurable_localizedOdometer hd D t x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (localizedOdometer_nonneg hd D ζ t x)]
  by_cases hx : x ∈ D
  · exact localizedOdometer_le External.optimalStopping hd D ζ t x hx
  · rw [localizedOdometer, Set.indicator_of_notMem hx]
    exact odometerOf_nonneg _ _ _

/-- The i.i.d. case of `integrable_localizedOdometer_of_stationary`. -/
theorem integrable_localizedOdometer (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (D : Set (Site d)) (t : ℕ) (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => localizedOdometer D ζ t x)
      (LatticeProb.iidLaw d ν) :=
  integrable_localizedOdometer_of_stationary hd (isStationary_iidLaw d ν)
    (integrable_coord_pos d ν hpos 0) D t x

/-- The mean localization bound, before the maximal-displacement estimate is
applied to the exit probability. -/
theorem mean_localization_bound_of_stationary (hd : 1 ≤ d) (P : Measure (Site d → ℝ))
    [IsProbabilityMeasure P] (hstat : IsStationary d P)
    (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (D : Set (Site d)) (t : ℕ) (x : Site d) (hx : x ∈ D) :
    0 ≤ (∫ ζ, odometerOf ζ t 0 ∂P) - ∫ ζ, localizedOdometer D ζ t x ∂P ∧
      (∫ ζ, odometerOf ζ t 0 ∂P) - ∫ ζ, localizedOdometer D ζ t x ∂P
        ≤ ((walkLaw d x) {X : ℕ → Site d | exitNat D t X ≤ t}).toReal *
            ∫ ζ, odometerOf ζ t 0 ∂P := by
  haveI : NeZero d := ⟨by omega⟩
  have hsite : (∫ ζ, odometerOf ζ t x ∂P) = ∫ ζ, odometerOf ζ t 0 ∂P :=
    integral_odometerOf_eq_of_stationary hstat t x
  have hLint := integrable_localizedOdometer_of_stationary hd hstat hpos D t x
  have hUint := integrable_odometerOf_of_stationary hstat hpos t x
  have hEint : Integrable
      (fun ζ : Site d → ℝ => ∫ X, exitReward D ζ t X ∂(walkLaw d x)) P :=
    (integrable_prod_exitReward hd P hstat hpos D t x).integral_prod_left
  have hle : (∫ ζ, localizedOdometer D ζ t x ∂P) ≤ ∫ ζ, odometerOf ζ t 0 ∂P := by
    rw [← hsite]
    refine integral_mono hLint hUint fun ζ => ?_
    exact localizedOdometer_le External.optimalStopping hd D ζ t x hx
  refine ⟨by linarith, ?_⟩
  have hstep : (∫ ζ, odometerOf ζ t x ∂P) - ∫ ζ, localizedOdometer D ζ t x ∂P
      ≤ ∫ ζ, (∫ X, exitReward D ζ t X ∂(walkLaw d x)) ∂P := by
    rw [← integral_sub hUint hLint]
    refine integral_mono (hUint.sub hLint) hEint fun ζ => ?_
    exact odometerOf_sub_localizedOdometer_le External.optimalStopping hd D ζ t x hx
  rw [← hsite]
  refine le_trans hstep ?_
  rw [integral_integral_exitReward hd P hstat hpos D t x, hsite]

/-- The i.i.d. case of `mean_localization_bound_of_stationary`. -/
theorem mean_localization_bound (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (D : Set (Site d)) (t : ℕ) (x : Site d)
    (hx : x ∈ D) :
    0 ≤ (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, localizedOdometer D ζ t x ∂(LatticeProb.iidLaw d ν) ∧
      (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, localizedOdometer D ζ t x ∂(LatticeProb.iidLaw d ν)
        ≤ ((walkLaw d x) {X : ℕ → Site d | exitNat D t X ≤ t}).toReal *
            ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
  mean_localization_bound_of_stationary hd _ (isStationary_iidLaw d ν)
    (integrable_coord_pos d ν hpos 0) D t x hx

end Sandpile
