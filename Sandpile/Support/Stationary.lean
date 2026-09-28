import Sandpile.Law
import Sandpile.Support.Odometer
import Sandpile.Support.Kernel
import Sandpile.Support.Translation
import LatticeProb.Prob.WeightedCLT

/-!
# Stationarity and integrability of the odometer in the scenery

A scenery law `P` is stationary (`IsStationary`) when it is invariant under every lattice
translation, and the i.i.d. law is an instance of this (`isStationary_iidLaw`). Since the
odometer `odometerOf ζ t x` commutes with a translation of the scenery
(`odometerOf_shiftField`), the mean odometer under a stationary law does not depend on the site.
A crude bound `u_t(x) ≤ t * ∑_{y ∈ Q(x,t)} ζ(y)⁺` follows from the recursion alone, since the
reflection contributes only the positive part of the scenery at the site and the neighbour
average of a field bounded by `M` is itself bounded by `M`; this makes the odometer integrable
under any stationary law whose scenery at the origin has integrable positive part. The
statements are proved first for a general stationary law and then specialized to the i.i.d. law.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ} {x : Site d}

/-! ### The odometer in the scenery, as a function of the scenery -/

/-- The map `ζ ↦ odometerOf ζ t x` is measurable, for fixed `t` and `x`. -/
theorem measurable_odometerOf (t : ℕ) (x : Site d) :
    Measurable fun ζ : Site d → ℝ => odometerOf ζ t x := by
  induction t generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
      have havg : Measurable fun ζ : Site d → ℝ => avg (odometerOf ζ n) x := by
        show Measurable fun ζ : Site d → ℝ =>
          (∑ i : Fin d, (odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)))
            / (2 * (d : ℝ))
        exact (Finset.measurable_sum _ fun i _ => (ih _).add (ih _)).div_const _
      exact measurable_const.max ((measurable_pi_apply x).add havg)

/-- The odometer commutes with translation of the scenery. -/
theorem odometerOf_shiftField (ζ : Site d → ℝ) (y : Site d) :
    ∀ (t : ℕ) (z : Site d), odometerOf (shiftField y ζ) t z = odometerOf ζ t (z + y) := by
  intro t
  induction t with
  | zero => intro z; rfl
  | succ n ih =>
      intro z
      have hnb : avg (odometerOf (shiftField y ζ) n) z = avg (odometerOf ζ n) (z + y) := by
        unfold avg LatticeProb.walkOp nbrSum
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have e1 : z + unit i + y = z + y + unit i := by abel
        have e2 : z - unit i + y = z + y - unit i := by abel
        rw [ih (z + unit i), ih (z - unit i), e1, e2]
      show max 0 (shiftField y ζ z + avg (odometerOf (shiftField y ζ) n) z) = _
      rw [hnb]
      rfl

/-- The i.i.d. scenery law `LatticeProb.iidLaw d ν` is definitionally `massLaw d ν`. -/
theorem iidLaw_eq_massLaw (d : ℕ) (ν : Measure ℝ) : LatticeProb.iidLaw d ν = massLaw d ν := rfl

/-! ### Stationary scenery laws -/

/-- A scenery law is stationary when it is invariant under every lattice
translation. -/
def IsStationary (d : ℕ) (P : Measure (Site d → ℝ)) : Prop :=
  ∀ v : Site d, P.map (fun ζ => fun x => ζ (x + v)) = P

/-- The i.i.d. scenery law is stationary. -/
theorem isStationary_iidLaw (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsStationary d (LatticeProb.iidLaw d ν) :=
  fun v => massLaw_map_shiftField d ν v

/-- Under a stationary scenery law the mean odometer does not depend on the
site. -/
theorem integral_odometerOf_eq_of_stationary {P : Measure (Site d → ℝ)}
    (hstat : IsStationary d P) (t : ℕ) (y : Site d) :
    ∫ ζ, odometerOf ζ t y ∂P = ∫ ζ, odometerOf ζ t 0 ∂P := by
  have hmap : P.map (shiftField y) = P := hstat y
  have hmeas : AEStronglyMeasurable (fun ζ : Site d → ℝ => odometerOf ζ t 0)
      (P.map (shiftField y)) := by
    rw [hmap]
    exact (measurable_odometerOf t 0).aestronglyMeasurable
  have h1 : ∫ ζ, odometerOf (shiftField y ζ) t 0 ∂P = ∫ ζ, odometerOf ζ t 0 ∂P := by
    rw [← integral_map (measurable_shiftField y).aemeasurable hmeas, hmap]
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  show odometerOf ζ t y = odometerOf (shiftField y ζ) t 0
  rw [odometerOf_shiftField ζ y t 0, zero_add]

/-! ### A crude bound on the odometer -/

/-- `y` lies in `boxFinset x r` iff `boxDist x y ≤ r`. -/
theorem mem_boxFinset_iff {x y : Site d} {r : ℕ} : y ∈ boxFinset x r ↔ boxDist x y ≤ r := by
  refine ⟨fun h => ?_, mem_boxFinset⟩
  refine Finset.sup_le fun i _ => ?_
  have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp h i)
  omega

/-- `boxFinset y s ⊆ boxFinset x u` whenever `boxDist x y + s ≤ u`, by the triangle inequality
for `boxDist`. -/
theorem boxFinset_subset {x y : Site d} {s u : ℕ} (h : boxDist x y + s ≤ u) :
    boxFinset y s ⊆ boxFinset x u := by
  intro z hz
  refine mem_boxFinset (le_trans (boxDist_trans x y z) ?_)
  have := mem_boxFinset_iff.mp hz
  omega

/-- Adding a unit vector moves the box distance from `x` by at most one:
`boxDist x (x + unit i) ≤ 1`. -/
theorem boxDist_add_unit (x : Site d) (i : Fin d) : boxDist x (x + unit i) ≤ 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  show (x j - (x j + unit i j)).natAbs ≤ 1
  rcases hu with hu | hu <;> rw [hu] <;> omega

/-- Subtracting a unit vector moves the box distance from `x` by at most one:
`boxDist x (x - unit i) ≤ 1`. -/
theorem boxDist_sub_unit (x : Site d) (i : Fin d) : boxDist x (x - unit i) ≤ 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  show (x j - (x j - unit i j)).natAbs ≤ 1
  rcases hu with hu | hu <;> rw [hu] <;> omega

/-- The neighbour average of a field bounded above at the neighbours by a
nonnegative constant is bounded by that constant. -/
theorem avg_le_of_nbr_le {f : Site d → ℝ} {M : ℝ}
    (hf : ∀ i : Fin d, f (x + unit i) ≤ M ∧ f (x - unit i) ≤ M) (hM : 0 ≤ M) :
    avg f x ≤ M := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0
    show (∑ i : Fin 0, _) / _ ≤ M
    simpa using hM
  · have hc : (0 : ℝ) < 2 * (d : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
      linarith
    show (∑ i : Fin d, (f (x + unit i) + f (x - unit i))) / (2 * (d : ℝ)) ≤ M
    rw [div_le_iff₀ hc]
    calc ∑ i : Fin d, (f (x + unit i) + f (x - unit i))
        ≤ ∑ _i : Fin d, (M + M) :=
          Finset.sum_le_sum fun i _ => add_le_add (hf i).1 (hf i).2
      _ = M * (2 * (d : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The sum of the positive parts of the scenery on the box of radius `t`. -/
noncomputable def sceneryPosBound (x : Site d) (t : ℕ) (ζ : Site d → ℝ) : ℝ :=
  ∑ y ∈ boxFinset x t, max (ζ y) 0

/-- `sceneryPosBound x t ζ` is nonnegative, being a sum of the nonnegative terms
`max (ζ y) 0`. -/
theorem sceneryPosBound_nonneg (x : Site d) (t : ℕ) (ζ : Site d → ℝ) :
    0 ≤ sceneryPosBound x t ζ :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- `sceneryPosBound` is monotone under box inclusion: `sceneryPosBound y s ζ ≤
sceneryPosBound x u ζ` whenever `boxDist x y + s ≤ u`. -/
theorem sceneryPosBound_mono {x y : Site d} {s u : ℕ} (h : boxDist x y + s ≤ u)
    (ζ : Site d → ℝ) : sceneryPosBound y s ζ ≤ sceneryPosBound x u ζ :=
  Finset.sum_le_sum_of_subset_of_nonneg (boxFinset_subset h)
    (fun _ _ _ => le_max_right _ _)

/-- The odometer is at most `t` times the sum of the positive parts of the
scenery on the box it can read. -/
theorem odometerOf_le_bound (ζ : Site d → ℝ) :
    ∀ (t : ℕ) (x : Site d), odometerOf ζ t x ≤ t * sceneryPosBound x t ζ := by
  intro t
  induction t with
  | zero => intro x; simp [odometerOf]
  | succ n ih =>
      intro x
      have hB : 0 ≤ sceneryPosBound x (n + 1) ζ := sceneryPosBound_nonneg _ _ _
      have hnB : 0 ≤ (n : ℝ) * sceneryPosBound x (n + 1) ζ :=
        mul_nonneg (Nat.cast_nonneg n) hB
      have hnbr : ∀ y : Site d, boxDist x y ≤ 1 →
          odometerOf ζ n y ≤ (n : ℝ) * sceneryPosBound x (n + 1) ζ := by
        intro y hy
        refine le_trans (ih y) (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
        exact sceneryPosBound_mono (by omega) ζ
      have havg : avg (odometerOf ζ n) x ≤ (n : ℝ) * sceneryPosBound x (n + 1) ζ :=
        avg_le_of_nbr_le (fun i => ⟨hnbr _ (boxDist_add_unit x i),
          hnbr _ (boxDist_sub_unit x i)⟩) hnB
      have h0 : 0 ≤ avg (odometerOf ζ n) x :=
        avg_nonneg (fun y => odometerOf_nonneg ζ n y) x
      have hzeta : max (ζ x) 0 ≤ sceneryPosBound x (n + 1) ζ :=
        Finset.single_le_sum (f := fun y => max (ζ y) 0)
          (fun _ _ => le_max_right _ _) (mem_boxFinset (by simp [boxDist_self]))
      show max 0 (ζ x + avg (odometerOf ζ n) x) ≤ _
      have hsplit : max 0 (ζ x + avg (odometerOf ζ n) x)
          ≤ max (ζ x) 0 + avg (odometerOf ζ n) x := by
        rcases le_or_gt (ζ x + avg (odometerOf ζ n) x) 0 with h | h
        · rw [max_eq_left h]
          have hm : 0 ≤ max (ζ x) 0 := le_max_right _ _
          linarith
        · rw [max_eq_right (le_of_lt h)]
          have hm : ζ x ≤ max (ζ x) 0 := le_max_left _ _
          linarith
      refine le_trans hsplit ?_
      have hcast : ((n + 1 : ℕ) : ℝ) * sceneryPosBound x (n + 1) ζ
          = sceneryPosBound x (n + 1) ζ + (n : ℝ) * sceneryPosBound x (n + 1) ζ := by
        push_cast; ring
      rw [hcast]
      exact add_le_add hzeta havg


/-! ### Integrability and stationarity of the mean odometer -/

/-- Under a stationary scenery law the positive part of the scenery is
integrable at every site as soon as it is at the origin. -/
theorem integrable_coord_pos_of_stationary {P : Measure (Site d → ℝ)}
    (hstat : IsStationary d P) (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (y : Site d) : Integrable (fun ζ : Site d → ℝ => max (ζ y) 0) P := by
  have hmap : P.map (shiftField y) = P := hstat y
  have hasm : AEStronglyMeasurable (fun ζ : Site d → ℝ => max (ζ 0) 0)
      (P.map (shiftField y)) := by
    rw [hmap]
    exact hpos.aestronglyMeasurable
  have h : Integrable ((fun ζ : Site d → ℝ => max (ζ 0) 0) ∘ shiftField y) P := by
    refine (integrable_map_measure hasm (measurable_shiftField y).aemeasurable).mp ?_
    rw [hmap]
    exact hpos
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show max (ζ (0 + y)) 0 = max (ζ y) 0
  rw [zero_add]

/-- Under a stationary scenery law whose positive part at the origin is integrable,
`sceneryPosBound x t` is integrable, as a finite sum of the integrable coordinates
of `integrable_coord_pos_of_stationary`. -/
theorem integrable_sceneryPosBound_of_stationary {P : Measure (Site d → ℝ)}
    (hstat : IsStationary d P) (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (x : Site d) (t : ℕ) : Integrable (fun ζ : Site d → ℝ => sceneryPosBound x t ζ) P :=
  integrable_finsetSum _ fun y _ => integrable_coord_pos_of_stationary hstat hpos y

/-- The odometer at a fixed site is integrable in the scenery under a stationary
law whose scenery at the origin has an integrable positive part. -/
theorem integrable_odometerOf_of_stationary {P : Measure (Site d → ℝ)}
    (hstat : IsStationary d P) (hpos : Integrable (fun ζ : Site d → ℝ => max (ζ 0) 0) P)
    (t : ℕ) (x : Site d) : Integrable (fun ζ : Site d → ℝ => odometerOf ζ t x) P := by
  refine Integrable.mono' ((integrable_sceneryPosBound_of_stationary hstat hpos x t).const_mul
      (t : ℝ))
    (measurable_odometerOf t x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (odometerOf_nonneg ζ t x)]
  exact odometerOf_le_bound ζ t x

/-- Under the i.i.d. law with one-site law `ν` whose positive part is integrable, the coordinate
`ζ ↦ max (ζ y) 0` at any site `y` is integrable, pushed forward along evaluation at `y`. -/
theorem integrable_coord_pos (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (y : Site d) :
    Integrable (fun ζ : Site d → ℝ => max (ζ y) 0) (LatticeProb.iidLaw d ν) := by
  have hmap : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ y) = ν := by
    unfold LatticeProb.iidLaw
    exact Measure.infinitePi_map_eval _ y
  have hasm : AEStronglyMeasurable (fun z : ℝ => max z 0)
      ((LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ y)) := by
    rw [hmap]; exact hpos.aestronglyMeasurable
  show Integrable ((fun z : ℝ => max z 0) ∘ (fun ζ : Site d → ℝ => ζ y)) _
  refine (integrable_map_measure hasm (measurable_pi_apply y).aemeasurable).mp ?_
  rw [hmap]
  exact hpos

/-- Under the i.i.d. law with integrable positive one-site part, `sceneryPosBound x t` is
integrable, as a finite sum of the integrable coordinates of `integrable_coord_pos`. -/
theorem integrable_sceneryPosBound (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (x : Site d) (t : ℕ) :
    Integrable (fun ζ : Site d → ℝ => sceneryPosBound x t ζ) (LatticeProb.iidLaw d ν) :=
  integrable_finsetSum _ fun y _ => integrable_coord_pos d ν hpos y

/-- The odometer at a fixed site is integrable in the scenery whenever the
positive part of the one-site law is. -/
theorem integrable_odometerOf (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => odometerOf ζ t x) (LatticeProb.iidLaw d ν) :=
  integrable_odometerOf_of_stationary (isStationary_iidLaw d ν)
    (integrable_coord_pos d ν hpos 0) t x

/-- The mean odometer does not depend on the site. -/
theorem integral_odometerOf_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ)
    (y : Site d) :
    ∫ ζ, odometerOf ζ t y ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
  integral_odometerOf_eq_of_stationary (isStationary_iidLaw d ν) t y

/-- The mean odometer `∫ odometerOf ζ t x ∂(LatticeProb.iidLaw d ν)` is nonnegative, since the
odometer itself is nonnegative at every scenery. -/
theorem integral_odometerOf_nonneg (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ)
    (x : Site d) : 0 ≤ ∫ ζ, odometerOf ζ t x ∂(LatticeProb.iidLaw d ν) :=
  integral_nonneg fun ζ => odometerOf_nonneg ζ t x

end Sandpile
