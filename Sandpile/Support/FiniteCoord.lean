/-
The finite-coordinate bridge.

Every functional of the scenery that `sandpile.tex` applies a concentration
inequality to reads only finitely many sites: `u_t(x)` is determined by the
scenery on the box of radius `t` about `x`, because the Green kernel `g_t(x, ·)`
is supported there.  The concentration lemma `lem:weighted-exp-conc`, on the
other hand, is stated for a finite product `Measure.pi` over `Fin N`.  This file
is the passage between the two: reading `N` distinct sites carries the i.i.d.
law of the field to the `N`-fold product of its one-site law.
-/
import Sandpile.Support.Lipschitz
import Sandpile.Support.Stationary
import LatticeProb.Prob.FiniteMarginal

open LatticeProb

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

/-- The odometer at `x` after `t` steps reads only the sites of the box of
radius `t` about `x`. -/
theorem odometerOf_congr_box (t : ℕ) (x : Site d) (ζ η : Site d → ℝ)
    (h : ∀ z : Site d, boxDist x z ≤ t → ζ z = η z) :
    odometerOf ζ t x = odometerOf η t x := by
  have hle := abs_odometerOf_sub_le ζ η t x
  have hzero : ∀ z : Site d, greenTime d t x z * |ζ z - η z| = 0 := by
    intro z
    by_cases hz : boxDist x z ≤ t
    · rw [h z hz]; simp
    · have : greenTime d t x z = 0 := by
        by_contra hne
        exact hz (greenTime_support t x hne)
      simp [this]
  rw [tsum_congr hzero, tsum_zero] at hle
  have := abs_nonneg (odometerOf ζ t x - odometerOf η t x)
  have hEq : |odometerOf ζ t x - odometerOf η t x| = 0 := le_antisymm hle this
  have := abs_eq_zero.mp hEq
  linarith

/-- An injective enumeration of a finite set of sites. -/
noncomputable def siteEnum (s : Finset (Site d)) : Fin s.card → Site d :=
  fun i => ((s.equivFin.symm i : ↥s) : Site d)

theorem siteEnum_mem (s : Finset (Site d)) (i : Fin s.card) : siteEnum s i ∈ s :=
  (s.equivFin.symm i).2

theorem siteEnum_injective (s : Finset (Site d)) : Function.Injective (siteEnum s) := by
  intro i j hij
  have : s.equivFin.symm i = s.equivFin.symm j := Subtype.ext hij
  simpa using congrArg s.equivFin this

/-- The scenery on a finite set of sites, read off a vector of its coordinates. -/
noncomputable def siteExtend (s : Finset (Site d)) (ξ : Fin s.card → ℝ) : Site d → ℝ :=
  fun z => if h : z ∈ s then ξ (s.equivFin ⟨z, h⟩) else 0

theorem siteExtend_siteEnum (s : Finset (Site d)) (ζ : Site d → ℝ) {z : Site d}
    (hz : z ∈ s) : siteExtend s (fun i => ζ (siteEnum s i)) z = ζ z := by
  simp [siteExtend, siteEnum, hz]

theorem siteExtend_update (s : Finset (Site d)) (ξ : Fin s.card → ℝ)
    (i : Fin s.card) (y : ℝ) :
    siteExtend s (Function.update ξ i y)
      = Function.update (siteExtend s ξ) (siteEnum s i) y := by
  classical
  funext z
  by_cases hz : z ∈ s
  · by_cases hzi : z = siteEnum s i
    · subst hzi
      have hidx : s.equivFin ⟨siteEnum s i, hz⟩ = i := by simp [siteEnum]
      simp [siteExtend, hz, hidx]
    · have hne : s.equivFin ⟨z, hz⟩ ≠ i := by
        intro h
        exact hzi (by simp [siteEnum, ← h])
      simp [siteExtend, hz, Function.update_of_ne hzi, Function.update_of_ne hne]
  · have hzi : z ≠ siteEnum s i := by
      intro h; exact hz (h ▸ siteEnum_mem s i)
    simp [siteExtend, hz, Function.update_of_ne hzi]

theorem measurable_siteExtend (s : Finset (Site d)) : Measurable (siteExtend s) := by
  classical
  refine measurable_pi_lambda _ fun z => ?_
  by_cases hz : z ∈ s
  · simp only [siteExtend, hz, dif_pos]
    exact measurable_pi_apply _
  · simp only [siteExtend, hz, dif_neg, not_false_eq_true]
    exact measurable_const

/-- The odometer at `x` after `t` steps, read as a function of the coordinates
of a finite set of sites containing the box it reads. -/
noncomputable def sceneryOdometer (s : Finset (Site d)) (t : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) : ℝ :=
  odometerOf (siteExtend s ξ) t x

theorem sceneryOdometer_pick {s : Finset (Site d)} {t : ℕ} {x : Site d}
    (hsub : boxFinset x t ⊆ s) (ζ : Site d → ℝ) :
    sceneryOdometer s t x (fun i => ζ (siteEnum s i)) = odometerOf ζ t x :=
  odometerOf_congr_box t x _ ζ fun _ hz =>
    siteExtend_siteEnum s ζ (hsub (mem_boxFinset hz))

theorem measurable_sceneryOdometer (s : Finset (Site d)) (t : ℕ) (x : Site d) :
    Measurable (sceneryOdometer s t x) :=
  (measurable_odometerOf t x).comp (measurable_siteExtend s)

/-- The coordinate Lipschitz bound: the constant at `i` is the Green kernel at
the `i`-th site. -/
theorem abs_sceneryOdometer_update_le (s : Finset (Site d)) (t : ℕ) (x : Site d)
    (ξ : Fin s.card → ℝ) (i : Fin s.card) (y : ℝ) :
    |sceneryOdometer s t x ξ - sceneryOdometer s t x (Function.update ξ i y)|
      ≤ greenTime d t x (siteEnum s i) * |ξ i - y| := by
  have hval : siteExtend s ξ (siteEnum s i) = ξ i := by
    simp [siteExtend, siteEnum]
  have h := abs_odometerOf_update_le (siteExtend s ξ) (siteEnum s i) y t x
  rw [sceneryOdometer, sceneryOdometer, siteExtend_update, hval] at *
  exact h

/-- A sum over a finite set of sites, read through the enumeration. -/
theorem sum_siteEnum {M : Type*} [AddCommMonoid M] (s : Finset (Site d)) (f : Site d → M) :
    ∑ i : Fin s.card, f (siteEnum s i) = ∑ z ∈ s, f z := by
  classical
  have h := Equiv.sum_comp s.equivFin.symm (fun z : ↥s => f (z : Site d))
  rw [show (∑ i : Fin s.card, f (siteEnum s i))
      = ∑ i : Fin s.card, f ((s.equivFin.symm i : ↥s) : Site d) from rfl, h,
    Finset.sum_coe_sort]

/-- The enumeration of the box of radius `t` about `x`. -/
noncomputable abbrev boxEnum (x : Site d) (t : ℕ) : Fin (boxFinset x t).card → Site d :=
  siteEnum (boxFinset x t)

theorem boxEnum_injective (x : Site d) (t : ℕ) : Function.Injective (boxEnum x t) :=
  siteEnum_injective _

/-- The odometer read as a function of the box coordinates. -/
noncomputable abbrev boxOdometer (t : ℕ) (x : Site d)
    (ξ : Fin (boxFinset x t).card → ℝ) : ℝ :=
  sceneryOdometer (boxFinset x t) t x ξ

theorem boxOdometer_pick (t : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    boxOdometer t x (fun i => ζ (boxEnum x t i)) = odometerOf ζ t x :=
  sceneryOdometer_pick (subset_refl _) ζ

theorem measurable_boxOdometer (t : ℕ) (x : Site d) : Measurable (boxOdometer t x) :=
  measurable_sceneryOdometer _ t x

theorem abs_boxOdometer_update_le (t : ℕ) (x : Site d) (ξ : Fin (boxFinset x t).card → ℝ)
    (i : Fin (boxFinset x t).card) (y : ℝ) :
    |boxOdometer t x ξ - boxOdometer t x (Function.update ξ i y)|
      ≤ greenTime d t x (boxEnum x t i) * |ξ i - y| :=
  abs_sceneryOdometer_update_le _ t x ξ i y

theorem sum_boxEnum {M : Type*} [AddCommMonoid M] (x : Site d) (t : ℕ) (f : Site d → M) :
    ∑ i : Fin (boxFinset x t).card, f (boxEnum x t i) = ∑ z ∈ boxFinset x t, f z :=
  sum_siteEnum _ f

/-- A field summed against the Green kernel is a finite sum over the box. -/
theorem tsum_greenTime_mul_eq_sum (t : ℕ) (x : Site d) (f : Site d → ℝ) :
    ∑' z : Site d, greenTime d t x z * f z = ∑ z ∈ boxFinset x t, greenTime d t x z * f z := by
  refine tsum_eq_sum fun z hz => ?_
  have hg : greenTime d t x z = 0 := by
    by_contra hne
    exact hz (mem_boxFinset (greenTime_support t x hne))
  simp [hg]

theorem tsum_greenTime_sq_eq_sum (t : ℕ) (x : Site d) :
    ∑' z : Site d, greenTime d t x z ^ 2 = ∑ z ∈ boxFinset x t, greenTime d t x z ^ 2 := by
  refine tsum_eq_sum fun z hz => ?_
  have hg : greenTime d t x z = 0 := by
    by_contra hne
    exact hz (mem_boxFinset (greenTime_support t x hne))
  simp [hg]

/-- The membrane field is the linear functional of the box coordinates with the
Green kernel as coefficients. -/
theorem membrane_eq_sum_boxEnum (t : ℕ) (x : Site d) (ζ : Site d → ℝ) :
    membrane ζ t x
      = ∑ i : Fin (boxFinset x t).card,
          greenTime d t x (boxEnum x t i) * ζ (boxEnum x t i) := by
  rw [membrane_eq_greenTime, tsum_greenTime_mul_eq_sum,
    ← sum_boxEnum x t fun z => greenTime d t x z * ζ z]

/-- The pairing of two Green coefficient vectors, read through the enumeration
of a finite set containing both boxes. -/
theorem sum_siteEnum_greenTime_mul {s : Finset (Site d)} {n m : ℕ} {x y : Site d}
    (hsub : boxFinset x n ⊆ s) :
    ∑ i : Fin s.card, greenTime d n x (siteEnum s i) * greenTime d m y (siteEnum s i)
      = ∑' z : Site d, greenTime d n x z * greenTime d m y z := by
  classical
  rw [sum_siteEnum s fun z => greenTime d n x z * greenTime d m y z]
  refine (tsum_eq_sum ?_).symm
  intro z hz
  have hg : greenTime d n x z = 0 := by
    by_contra hne
    exact hz (hsub (mem_boxFinset (greenTime_support n x hne)))
  simp [hg]

/-- Transport of an integral along the reading of `N` distinct sites. -/
theorem integral_pick (ν : Measure ℝ) [IsProbabilityMeasure ν] {N : ℕ}
    (e : Fin N → Site d) (he : Function.Injective e) (G : (Fin N → ℝ) → ℝ)
    (hG : AEStronglyMeasurable G (Measure.pi fun _ : Fin N => ν)) :
    ∫ ζ, G (fun i => ζ (e i)) ∂(LatticeProb.iidLaw d ν)
      = ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin N => ν) := by
  have h := LatticeProb.measurePreserving_pick _ ν e he
  have hmap : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => fun i => ζ (e i))
      = Measure.pi fun _ : Fin N => ν := h.map_eq
  have := integral_map (μ := LatticeProb.iidLaw d ν)
    (φ := fun ζ : Site d → ℝ => fun i => ζ (e i)) (f := G)
    h.measurable.aemeasurable (by rwa [hmap])
  rw [hmap] at this
  exact this.symm

set_option maxHeartbeats 1000000 in
/-- The variance of a linear functional of finitely many distinct sites of an
i.i.d. field. -/
theorem variance_linear_pick (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) {N : ℕ} (e : Fin N → Site d)
    (he : Function.Injective e) (ℓ : Fin N → ℝ) :
    variance (fun ζ : Site d → ℝ => ∑ i, ℓ i * ζ (e i)) (LatticeProb.iidLaw d ν)
      = (∑ i, ℓ i ^ 2) * variance (id : ℝ → ℝ) ν := by
  have hpick := LatticeProb.measurePreserving_pick _ ν e he
  have hmeasM : Measurable (fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hvar : variance (fun ζ : Site d → ℝ => ∑ i, ℓ i * ζ (e i)) (LatticeProb.iidLaw d ν)
      = variance (fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i) (Measure.pi fun _ : Fin N => ν) :=
    hpick.variance_fun_comp hmeasM.aemeasurable
  have hMemLp : ∀ i : Fin N, MemLp (fun z : ℝ => ℓ i * z) 2 ν := fun i => hsq.const_mul (ℓ i)
  have hsum : variance (fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i) (Measure.pi fun _ : Fin N => ν)
      = ∑ i, variance (fun z : ℝ => ℓ i * z) ν := by
    have h := variance_sum_pi (μ := fun _ : Fin N => ν) (X := fun i => fun z : ℝ => ℓ i * z) hMemLp
    have hfun : (∑ i, fun ω : Fin N → ℝ => ℓ i * ω i)
        = fun ξ : Fin N → ℝ => ∑ i, ℓ i * ξ i := by
      funext ξ; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hi : ∀ i : Fin N,
      variance (fun z : ℝ => ℓ i * z) ν = ℓ i ^ 2 * variance (id : ℝ → ℝ) ν := by
    intro i
    have := variance_const_mul (ℓ i) (id : ℝ → ℝ) ν
    simpa using this
  rw [hvar, hsum, Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_mul]

/-- `Var(V_t(x)) = Var(ζ(0)) ∑_z g_t(x,z)^2`, the identity of
`sandpile.tex:1178-1182`. -/
theorem variance_membrane (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (t : ℕ) (x : Site d) :
    variance (fun ζ => membrane ζ t x) (LatticeProb.iidLaw d ν)
      = variance (id : ℝ → ℝ) ν * ∑' z : Site d, greenTime d t x z ^ 2 := by
  have hrep : (fun ζ : Site d → ℝ => membrane ζ t x)
      = fun ζ : Site d → ℝ =>
        ∑ i : Fin (boxFinset x t).card,
          greenTime d t x (boxEnum x t i) * ζ (boxEnum x t i) := by
    funext ζ; exact membrane_eq_sum_boxEnum t x ζ
  rw [hrep, variance_linear_pick ν hsq (boxEnum x t) (boxEnum_injective x t)
      (fun i => greenTime d t x (boxEnum x t i)), mul_comm,
    tsum_greenTime_sq_eq_sum, ← sum_boxEnum x t fun z => greenTime d t x z ^ 2]

/-- The membrane field through the enumeration of any finite set of sites
containing the box the Green kernel is supported in. -/
theorem membrane_eq_sum_siteEnum {s : Finset (Site d)} {t : ℕ} {x : Site d}
    (hsub : boxFinset x t ⊆ s) (ζ : Site d → ℝ) :
    membrane ζ t x = ∑ i : Fin s.card,
      greenTime d t x (siteEnum s i) * ζ (siteEnum s i) := by
  classical
  rw [sum_siteEnum s fun z => greenTime d t x z * ζ z, membrane_eq_greenTime]
  refine tsum_eq_sum fun z hz => ?_
  have hg : greenTime d t x z = 0 := by
    by_contra hne
    exact hz (hsub (mem_boxFinset (greenTime_support t x hne)))
  simp [hg]

/-- A linear functional of finitely many distinct sites is square integrable. -/
theorem memLp_two_linear_pick (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) {N : ℕ} (e : Fin N → Site d)
    (he : Function.Injective e) (a : Fin N → ℝ) :
    MemLp (fun ζ : Site d → ℝ => ∑ i, a i * ζ (e i)) 2 (LatticeProb.iidLaw d ν) := by
  have hcoord : ∀ i : Fin N, MemLp (fun ξ : Fin N → ℝ => a i * ξ i) 2
      (Measure.pi fun _ : Fin N => ν) := by
    intro i
    have h := hsq.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => ν) i)
    exact h.const_mul (a i)
  have hpi : MemLp (fun ξ : Fin N → ℝ => ∑ i, a i * ξ i) 2
      (Measure.pi fun _ : Fin N => ν) := by
    have h := memLp_finsetSum (μ := Measure.pi fun _ : Fin N => ν) (p := 2)
      (Finset.univ : Finset (Fin N)) (f := fun i => fun ξ : Fin N → ℝ => a i * ξ i)
      fun i _ => hcoord i
    refine h.ae_eq ?_
    exact Filter.Eventually.of_forall fun ξ => by simp
  exact hpi.comp_measurePreserving (LatticeProb.measurePreserving_pick _ ν e he)

/-- The covariance of two linear functionals of finitely many distinct sites of
an i.i.d. field is the pairing of their coefficient vectors. -/
theorem covariance_linear_pick (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) {N : ℕ} (e : Fin N → Site d)
    (he : Function.Injective e) (a b : Fin N → ℝ) :
    covariance (fun ζ : Site d → ℝ => ∑ i, a i * ζ (e i))
        (fun ζ : Site d → ℝ => ∑ i, b i * ζ (e i)) (LatticeProb.iidLaw d ν)
      = (∑ i, a i * b i) * variance (id : ℝ → ℝ) ν := by
  have hA := memLp_two_linear_pick ν hsq e he a
  have hB := memLp_two_linear_pick ν hsq e he b
  have hsum : (fun ζ : Site d → ℝ => ∑ i, a i * ζ (e i))
      + (fun ζ : Site d → ℝ => ∑ i, b i * ζ (e i))
      = fun ζ : Site d → ℝ => ∑ i, (a i + b i) * ζ (e i) := by
    funext ζ
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hvar := variance_add (μ := LatticeProb.iidLaw d ν) hA hB
  rw [hsum, variance_linear_pick ν hsq e he (fun i => a i + b i),
    variance_linear_pick ν hsq e he a, variance_linear_pick ν hsq e he b] at hvar
  have hexp : (∑ i, (a i + b i) ^ 2) = (∑ i, a i ^ 2) + (∑ i, b i ^ 2) + 2 * ∑ i, a i * b i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp] at hvar
  linarith [hvar]

/-- `Cov(V_m(x), V_n(y)) = Var(ζ(0)) ∑_z g_m(x,z) g_n(y,z)`, the identity of
`sandpile.tex:1197-1204`. -/
theorem covariance_membrane (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (m n : ℕ) (x y : Site d) :
    covariance (fun ζ => membrane ζ m x) (fun ζ => membrane ζ n y)
        (LatticeProb.iidLaw d ν)
      = variance (id : ℝ → ℝ) ν *
        ∑' z : Site d, greenTime d m x z * greenTime d n y z := by
  classical
  have hsubx : boxFinset x m ⊆ boxFinset x m ∪ boxFinset y n := Finset.subset_union_left
  have hsuby : boxFinset y n ⊆ boxFinset x m ∪ boxFinset y n := Finset.subset_union_right
  have hrepx : (fun ζ : Site d → ℝ => membrane ζ m x)
      = fun ζ : Site d → ℝ => ∑ i : Fin (boxFinset x m ∪ boxFinset y n).card,
        greenTime d m x (siteEnum (boxFinset x m ∪ boxFinset y n) i) *
          ζ (siteEnum (boxFinset x m ∪ boxFinset y n) i) :=
    funext fun ζ => membrane_eq_sum_siteEnum hsubx ζ
  have hrepy : (fun ζ : Site d → ℝ => membrane ζ n y)
      = fun ζ : Site d → ℝ => ∑ i : Fin (boxFinset x m ∪ boxFinset y n).card,
        greenTime d n y (siteEnum (boxFinset x m ∪ boxFinset y n) i) *
          ζ (siteEnum (boxFinset x m ∪ boxFinset y n) i) :=
    funext fun ζ => membrane_eq_sum_siteEnum hsuby ζ
  rw [hrepx, hrepy, covariance_linear_pick ν hsq _ (siteEnum_injective _)
    (fun i => greenTime d m x (siteEnum (boxFinset x m ∪ boxFinset y n) i))
    (fun i => greenTime d n y (siteEnum (boxFinset x m ∪ boxFinset y n) i)),
    sum_siteEnum_greenTime_mul hsubx, mul_comm]

end Sandpile
