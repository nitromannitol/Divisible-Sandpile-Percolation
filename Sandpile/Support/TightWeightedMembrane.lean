import Sandpile.Support.FiniteCoord
import Sandpile.Support.Iterate
import Sandpile.Support.GreenHigh
import Sandpile.Support.TightNegSobolev
import Sandpile.Frozen.SobolevTightness
import Sandpile.Support.TightD4Covariance

/-!
# Tightness of the time-weighted membrane field

The time-weighted membrane field of `prop:weighted-membrane-limit` (`sandpile.tex:4692-4703`),

  `x ↦ ∑_{j<t} q(j) (P^j ζ)(x)`,

its Green representation, and the covariance decay it inherits from the intersection estimate
`eq:dgt4-intersection-first-moment`. The weighted kernel `∑_{j<t} q(j) p_j(x,z)` is bounded by
`Q g_t(x,z)` whenever `|q| ≤ Q` on the range, so the covariance of two weighted fields is at
most `Q² Var(ζ(0))` times the doubled Green kernel, which in dimension five and above is at
most `C(1+|x-y|)^{4-d}` uniformly in the time. That is exactly the tightness hypothesis at
`β = d-4`, whose normalization `R^{β/2}` is the statement's `R^{(d-4)/2}` and whose threshold
`s > β/2` is the statement's `s > (d-4)/2`. `weighted_membrane_tight` proves this tightness for
the general weighted field, and `dgt4_odometer_tight` / `dgt4_odometer_tight'` specialize it to
the odometer fluctuation of `thm:dgt4-diffusive-membrane`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

variable {d : ℕ}

/-- The kernel of the time-weighted membrane field, `∑_{j<t} q(j) p_j(x,z)`. -/
noncomputable def weightedKernel (d : ℕ) (q : ℕ → ℝ) (t : ℕ) (x z : Sandpile.Site d) : ℝ :=
  ∑ j ∈ Finset.range t, q j * Sandpile.heatKernel d j x z

/-- The time-weighted membrane field, `∑_{j<t} q(j) (P^j ζ)(x)`. -/
noncomputable def weightedField (q : ℕ → ℝ) (t : ℕ) (ζ : Sandpile.Site d → ℝ)
    (x : Sandpile.Site d) : ℝ :=
  ∑ j ∈ Finset.range t, q j * (Sandpile.avg^[j] ζ) x

/-- The weighted field in Green form. -/
theorem weightedField_eq_tsum (q : ℕ → ℝ) (t : ℕ) (ζ : Sandpile.Site d → ℝ)
    (x : Sandpile.Site d) :
    weightedField q t ζ x = ∑' z : Sandpile.Site d, weightedKernel d q t x z * ζ z := by
  have hterm : ∀ j ∈ Finset.range t, q j * (Sandpile.avg^[j] ζ) x
      = ∑' z : Sandpile.Site d, q j * (Sandpile.heatKernel d j x z * ζ z) := by
    intro j _
    rw [Sandpile.avg_iterate j ζ x,
      ← (Sandpile.summable_heatKernel_mul j x ζ).tsum_mul_left (q j)]
  rw [weightedField, Finset.sum_congr rfl hterm,
    ← Summable.tsum_finsetSum fun j (_ : j ∈ Finset.range t) =>
      (Sandpile.summable_heatKernel_mul j x ζ).mul_left (q j)]
  refine tsum_congr fun z => ?_
  rw [weightedKernel, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The weighted kernel is dominated by the Green kernel. -/
theorem abs_weightedKernel_le (q : ℕ → ℝ) (t : ℕ) (Q : ℝ)
    (hQ : ∀ j ∈ Finset.range t, |q j| ≤ Q) (x z : Sandpile.Site d) :
    |weightedKernel d q t x z| ≤ Q * Sandpile.greenTime d t x z := by
  calc |weightedKernel d q t x z|
      ≤ ∑ j ∈ Finset.range t, |q j * Sandpile.heatKernel d j x z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range t, Q * Sandpile.heatKernel d j x z := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_nonneg (Sandpile.heatKernel_nonneg j x z)]
        exact mul_le_mul_of_nonneg_right (hQ j hj) (Sandpile.heatKernel_nonneg j x z)
    _ = Q * Sandpile.greenTime d t x z := by
        rw [Sandpile.greenTime, LatticeProb.greenTime, Finset.mul_sum]

/-- The weighted kernel is supported in the box of radius `t`. -/
theorem weightedKernel_support (q : ℕ → ℝ) (t : ℕ) (x z : Sandpile.Site d)
    (hne : weightedKernel d q t x z ≠ 0) : Sandpile.boxDist x z ≤ t := by
  by_contra hk
  refine hne ?_
  refine Finset.sum_eq_zero fun j hj => ?_
  have ht : t < Sandpile.boxDist x z := by simpa using Nat.lt_of_not_le hk
  have hjt : j < t := Finset.mem_range.mp hj
  rw [Sandpile.heatKernel_eq_zero_of_lt j x z (by omega), mul_zero]

/-- The weighted field as a finite linear functional of the scenery. -/
theorem weightedField_eq_sum_siteEnum {s : Finset (Sandpile.Site d)} {q : ℕ → ℝ} {t : ℕ}
    {x : Sandpile.Site d} (hsub : Sandpile.boxFinset x t ⊆ s) (ζ : Sandpile.Site d → ℝ) :
    weightedField q t ζ x
      = ∑ i : Fin s.card, weightedKernel d q t x (siteEnum s i) * ζ (siteEnum s i) := by
  classical
  rw [sum_siteEnum s fun z => weightedKernel d q t x z * ζ z, weightedField_eq_tsum]
  refine tsum_eq_sum fun z hz => ?_
  have hg : weightedKernel d q t x z = 0 := by
    by_contra hne
    exact hz (hsub (Sandpile.mem_boxFinset (weightedKernel_support q t x z hne)))
  simp [hg]

/-- The covariance of two weighted membrane fields is the pairing of their
kernels, `Var(ζ(0)) ∑_z w_x(z) w_y(z)`. -/
theorem covariance_weightedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (q : ℕ → ℝ) (t : ℕ) (x y : Sandpile.Site d) :
    covariance (fun ζ => weightedField q t ζ x) (fun ζ => weightedField q t ζ y)
        (LatticeProb.iidLaw d ν)
      = variance (id : ℝ → ℝ) ν *
        ∑' z : Sandpile.Site d, weightedKernel d q t x z * weightedKernel d q t y z := by
  classical
  have hsubx : Sandpile.boxFinset x t ⊆ Sandpile.boxFinset x t ∪ Sandpile.boxFinset y t :=
    Finset.subset_union_left
  have hsuby : Sandpile.boxFinset y t ⊆ Sandpile.boxFinset x t ∪ Sandpile.boxFinset y t :=
    Finset.subset_union_right
  set s := Sandpile.boxFinset x t ∪ Sandpile.boxFinset y t with hs
  have hrepx : (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      = fun ζ : Sandpile.Site d → ℝ =>
        ∑ i : Fin s.card, weightedKernel d q t x (siteEnum s i) * ζ (siteEnum s i) :=
    funext fun ζ => weightedField_eq_sum_siteEnum hsubx ζ
  have hrepy : (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ y)
      = fun ζ : Sandpile.Site d → ℝ =>
        ∑ i : Fin s.card, weightedKernel d q t y (siteEnum s i) * ζ (siteEnum s i) :=
    funext fun ζ => weightedField_eq_sum_siteEnum hsuby ζ
  rw [hrepx, hrepy, covariance_linear_pick ν hsq (siteEnum s) (siteEnum_injective s)
    (fun i => weightedKernel d q t x (siteEnum s i))
    (fun i => weightedKernel d q t y (siteEnum s i))]
  have hsum : ∑ i : Fin s.card,
      weightedKernel d q t x (siteEnum s i) * weightedKernel d q t y (siteEnum s i)
      = ∑' z : Sandpile.Site d, weightedKernel d q t x z * weightedKernel d q t y z := by
    rw [sum_siteEnum s fun z => weightedKernel d q t x z * weightedKernel d q t y z]
    refine (tsum_eq_sum ?_).symm
    intro z hz
    have hg : weightedKernel d q t x z = 0 := by
      by_contra hne
      exact hz (hsubx (Sandpile.mem_boxFinset (weightedKernel_support q t x z hne)))
    simp [hg]
  rw [hsum, mul_comm]

/-- The two Euclidean site distances agree. -/
theorem latticeNorm_sub_eq (x y : Sandpile.Site d) :
    Sandpile.External.latticeNorm (x - y)
      = Sandpile.Frozen.SobolevTightness.latticeDist x y := by
  rfl

/-- The finite-time Green kernel is below the Green function at every base point. -/
theorem greenTime_le_green_shift (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (t : ℕ) (x z : Sandpile.Site d) :
    Sandpile.greenTime d t x z ≤ Sandpile.green d x z := by
  have h1 : Sandpile.greenTime d t x z = Sandpile.greenTime d t 0 (z - x) := by
    have h := Sandpile.greenTime_add_right t 0 (z - x) x
    simpa using h
  have h2 : Sandpile.green d x z = Sandpile.green d 0 (z - x) := by
    unfold Sandpile.green
    refine tsum_congr fun k => ?_
    have h := Sandpile.heatKernel_add_right k 0 (z - x) x
    simpa using h
  rw [h1, h2]
  exact Sandpile.greenTime_le_green hGH hd t (z - x)

/-- The covariance of the time-weighted membrane field decays like
`(1+|x-y|)^{-(d-4)}`, uniformly in the time and in the weight, once the weight is
bounded by `Q`.  This is the hypothesis of `lem:sobolev-tightness` at
`β = d - 4`. -/
theorem exists_weighted_membrane_covariance_decay (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (Q : ℝ) (hQ0 : 0 ≤ Q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ → ℝ) (t : ℕ), (∀ j ∈ Finset.range t, |q j| ≤ Q) →
      ∀ x y : Sandpile.Site d,
        |covariance (fun ζ => weightedField q t ζ x) (fun ζ => weightedField q t ζ y)
            (LatticeProb.iidLaw d ν)|
          ≤ K * (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-((d : ℝ) - 4)) := by
  obtain ⟨C, hC, hint⟩ := (hGH d hd).2.2.2.1
  have hV : (0:ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  refine ⟨variance (id : ℝ → ℝ) ν * Q ^ 2 * C, by positivity, ?_⟩
  intro q t hq x y
  have hbound : ∀ z : Sandpile.Site d,
      |weightedKernel d q t x z * weightedKernel d q t y z|
        ≤ Q ^ 2 * (Sandpile.greenTime d t x z * Sandpile.greenTime d t y z) := by
    intro z
    rw [abs_mul]
    have hx := abs_weightedKernel_le q t Q hq x z
    have hy := abs_weightedKernel_le q t Q hq y z
    have hgx : (0:ℝ) ≤ Sandpile.greenTime d t x z := Sandpile.greenTime_nonneg t x z
    have hgy : (0:ℝ) ≤ Sandpile.greenTime d t y z := Sandpile.greenTime_nonneg t y z
    calc |weightedKernel d q t x z| * |weightedKernel d q t y z|
        ≤ (Q * Sandpile.greenTime d t x z) * (Q * Sandpile.greenTime d t y z) :=
          mul_le_mul hx hy (abs_nonneg _) (by positivity)
      _ = Q ^ 2 * (Sandpile.greenTime d t x z * Sandpile.greenTime d t y z) := by ring
  have hsumG : Summable (fun z : Sandpile.Site d =>
      Sandpile.greenTime d t x z * Sandpile.greenTime d t y z) :=
    Sandpile.summable_greenTime_mul t x _
  have hnormW : Summable (fun z : Sandpile.Site d =>
      ‖weightedKernel d q t x z * weightedKernel d q t y z‖) := by
    refine Summable.of_nonneg_of_le (fun z => norm_nonneg _) (fun z => ?_) (hsumG.mul_left (Q ^ 2))
    rw [Real.norm_eq_abs]
    exact hbound z
  have hsumW : Summable (fun z : Sandpile.Site d =>
      weightedKernel d q t x z * weightedKernel d q t y z) := hnormW.of_norm
  have habs : |∑' z : Sandpile.Site d, weightedKernel d q t x z * weightedKernel d q t y z|
      ≤ Q ^ 2 * ∑' z : Sandpile.Site d,
        Sandpile.greenTime d t x z * Sandpile.greenTime d t y z := by
    calc |∑' z : Sandpile.Site d, weightedKernel d q t x z * weightedKernel d q t y z|
        ≤ ∑' z : Sandpile.Site d, |weightedKernel d q t x z * weightedKernel d q t y z| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnormW
      _ ≤ ∑' z : Sandpile.Site d,
            Q ^ 2 * (Sandpile.greenTime d t x z * Sandpile.greenTime d t y z) := by
          refine Summable.tsum_le_tsum hbound ?_ (hsumG.mul_left (Q ^ 2))
          simpa [Real.norm_eq_abs] using hnormW
      _ = Q ^ 2 * ∑' z : Sandpile.Site d,
            Sandpile.greenTime d t x z * Sandpile.greenTime d t y z := hsumG.tsum_mul_left (Q ^ 2)
  have hgreen : ∑' z : Sandpile.Site d,
      Sandpile.greenTime d t x z * Sandpile.greenTime d t y z
      ≤ C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
    refine le_trans ?_ (hint x y).2
    exact hsumG.tsum_le_tsum (fun z => mul_le_mul (greenTime_le_green_shift hGH hd t x z)
      (greenTime_le_green_shift hGH hd t y z) (Sandpile.greenTime_nonneg t y z)
      (le_trans (Sandpile.greenTime_nonneg t x z)
        (greenTime_le_green_shift hGH hd t x z))) (hint x y).1
  have hexp : (4 : ℝ) - (d : ℝ) = -((d : ℝ) - 4) := by ring
  rw [covariance_weightedField ν hsq q t x y, abs_mul, abs_of_nonneg hV]
  calc variance (id : ℝ → ℝ) ν *
        |∑' z : Sandpile.Site d, weightedKernel d q t x z * weightedKernel d q t y z|
      ≤ variance (id : ℝ → ℝ) ν * (Q ^ 2 * ∑' z : Sandpile.Site d,
          Sandpile.greenTime d t x z * Sandpile.greenTime d t y z) :=
        mul_le_mul_of_nonneg_left habs hV
    _ ≤ variance (id : ℝ → ℝ) ν * (Q ^ 2 *
          (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgreen (by positivity)) hV
    _ = variance (id : ℝ → ℝ) ν * Q ^ 2 * C *
          (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-((d : ℝ) - 4)) := by
        rw [latticeNorm_sub_eq, hexp]
        ring

/-- A linear functional of finitely many distinct sites of a centred i.i.d.
field has mean zero. -/
theorem integral_linear_pick (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    {N : ℕ} (e : Fin N → Sandpile.Site d) (he : Function.Injective e) (a : Fin N → ℝ) :
    ∫ ζ, (∑ i, a i * ζ (e i)) ∂(LatticeProb.iidLaw d ν) = 0 := by
  have hpick := LatticeProb.measurePreserving_pick _ ν e he
  have hmeasM : Measurable (fun ξ : Fin N → ℝ => ∑ i, a i * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hcomp : ∫ ζ, (∑ i, a i * ζ (e i)) ∂(LatticeProb.iidLaw d ν)
      = ∫ ξ, (∑ i, a i * ξ i) ∂(Measure.pi fun _ : Fin N => ν) := by
    rw [← hpick.map_eq, integral_map hpick.measurable.aemeasurable
      hmeasM.aestronglyMeasurable]
  have hint : ∀ i : Fin N, Integrable (fun ξ : Fin N → ℝ => a i * ξ i)
      (Measure.pi fun _ : Fin N => ν) := by
    intro i
    have h := hsq.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => ν) i)
    exact ((h.const_mul (a i)).integrable (by norm_num))
  have hev : ∀ i : Fin N, ∫ ξ, ξ i ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin N => ν) i
    have hmap := integral_map (μ := Measure.pi fun _ : Fin N => ν)
      (φ := fun ξ : Fin N → ℝ => ξ i) (f := (id : ℝ → ℝ))
      (measurable_pi_apply i).aemeasurable
      (by rw [hmp.map_eq]; exact aestronglyMeasurable_id)
    rw [hmp.map_eq] at hmap
    have hz : ∫ ξ, ξ i ∂(Measure.pi fun _ : Fin N => ν) = ∫ z, z ∂ν := by simpa using hmap.symm
    rw [hz, hmean]
  have hcoord : ∀ i : Fin N, ∫ ξ, a i * ξ i ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
    intro i
    rw [integral_const_mul, hev i, mul_zero]
  rw [hcomp, integral_finsetSum _ fun i _ => hint i,
    Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_const_zero]

/-- The weighted membrane field is square integrable. -/
theorem memLp_two_weightedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (q : ℕ → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    MemLp (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x) 2
      (LatticeProb.iidLaw d ν) := by
  classical
  have hrep : (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      = fun ζ : Sandpile.Site d → ℝ =>
        ∑ i : Fin (Sandpile.boxFinset x t).card,
          weightedKernel d q t x (siteEnum (Sandpile.boxFinset x t) i) *
            ζ (siteEnum (Sandpile.boxFinset x t) i) :=
    funext fun ζ => weightedField_eq_sum_siteEnum (subset_refl _) ζ
  rw [hrep]
  exact memLp_two_linear_pick ν hsq (siteEnum (Sandpile.boxFinset x t))
    (siteEnum_injective _) _

/-- The weighted membrane field of a centred scenery has mean zero. -/
theorem integral_weightedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (q : ℕ → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    ∫ ζ, weightedField q t ζ x ∂(LatticeProb.iidLaw d ν) = 0 := by
  classical
  have hrep : (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      = fun ζ : Sandpile.Site d → ℝ =>
        ∑ i : Fin (Sandpile.boxFinset x t).card,
          weightedKernel d q t x (siteEnum (Sandpile.boxFinset x t) i) *
            ζ (siteEnum (Sandpile.boxFinset x t) i) :=
    funext fun ζ => weightedField_eq_sum_siteEnum (subset_refl _) ζ
  rw [show (∫ ζ, weightedField q t ζ x ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x) ζ
        ∂(LatticeProb.iidLaw d ν) from rfl, hrep]
  exact integral_linear_pick ν hsq hmean (siteEnum (Sandpile.boxFinset x t))
    (siteEnum_injective _) _

/-- The weighted membrane field is a measurable function of the scenery. -/
theorem measurable_weightedField (q : ℕ → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    Measurable (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x) := by
  classical
  have hrep : (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      = fun ζ : Sandpile.Site d → ℝ =>
        ∑ i : Fin (Sandpile.boxFinset x t).card,
          weightedKernel d q t x (siteEnum (Sandpile.boxFinset x t) i) *
            ζ (siteEnum (Sandpile.boxFinset x t) i) :=
    funext fun ζ => weightedField_eq_sum_siteEnum (subset_refl _) ζ
  rw [hrep]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).const_mul _

/-- The weighted membrane field of a mass field, read through its scenery, is
square integrable. -/
theorem memLp_two_weightedField_mass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hd1 : 1 ≤ d) (q : ℕ → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    MemLp (fun σ : Sandpile.Site d → ℝ => weightedField q t (Sandpile.scenery d σ) x) 2
      (Sandpile.centeredMassLaw d ν) := by
  have hmap := Sandpile.map_scenery_centeredMassLaw d ν hd1
  have h : MemLp (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x) 2
      ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact memLp_two_weightedField ν hsq q t x
  have hasm : AEStronglyMeasurable (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact (measurable_weightedField q t x).aestronglyMeasurable
  exact (memLp_map_measure_iff hasm (Sandpile.measurable_scenery d).aemeasurable).mp h

/-- The weighted membrane field of a mass field has mean zero. -/
theorem integral_weightedField_mass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0) (hd1 : 1 ≤ d)
    (q : ℕ → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    ∫ σ, weightedField q t (Sandpile.scenery d σ) x ∂(Sandpile.centeredMassLaw d ν) = 0 := by
  have hmap := Sandpile.map_scenery_centeredMassLaw d ν hd1
  have h2 := integral_map (μ := Sandpile.centeredMassLaw d ν) (φ := Sandpile.scenery d)
      (f := fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      (Sandpile.measurable_scenery d).aemeasurable
      (by rw [hmap]; exact (measurable_weightedField q t x).aestronglyMeasurable)
  rw [hmap] at h2
  rw [← h2, integral_weightedField ν hsq hmean q t x]

/-- The covariance of two weighted membrane fields of a mass field is their
covariance under the scenery law. -/
theorem covariance_weightedField_mass (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd1 : 1 ≤ d) (q : ℕ → ℝ) (t : ℕ) (x y : Sandpile.Site d) :
    covariance (fun σ => weightedField q t (Sandpile.scenery d σ) x)
        (fun σ => weightedField q t (Sandpile.scenery d σ) y) (Sandpile.centeredMassLaw d ν)
      = covariance (fun ζ => weightedField q t ζ x) (fun ζ => weightedField q t ζ y)
        (LatticeProb.iidLaw d ν) := by
  have hmap := Sandpile.map_scenery_centeredMassLaw d ν hd1
  have hax : AEStronglyMeasurable (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
      ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact (measurable_weightedField q t x).aestronglyMeasurable
  have hay : AEStronglyMeasurable (fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ y)
      ((Sandpile.centeredMassLaw d ν).map (Sandpile.scenery d)) := by
    rw [hmap]; exact (measurable_weightedField q t y).aestronglyMeasurable
  rw [covariance_comp (φ := Sandpile.scenery d)
    (f := fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ x)
    (g := fun ζ : Sandpile.Site d → ℝ => weightedField q t ζ y)
    (Sandpile.centeredMassLaw d ν) (Sandpile.measurable_scenery d) hax hay, hmap]

/-- The tightness half of `prop:weighted-membrane-limit`: the time-weighted
membrane fields, at the normalization `R^{(d-4)/2}` of the statement, are tight
in `H^{-s}_loc(ℝ^d)` for every `s > (d-4)/2`. -/
theorem weighted_membrane_tight (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0) (T : ℝ) (hT : 0 < T) (q : ℝ → ℝ) (Q : ℝ) (hQ0 : 0 ≤ Q)
    (hQ : ∀ r ∈ Set.Icc (0 : ℝ) T, |q r| ≤ Q) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd4 : (0:ℝ) < (d : ℝ) - 4 := by
    have : (5:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hdecay⟩ := exists_weighted_membrane_covariance_decay hGH hd ν hsq Q hQ0
  refine Sandpile.Frozen.sobolev_tightness d ((d : ℝ) - 4) K hd4 (by linarith) hBesov
    (Sandpile.centeredMassLaw d ν)
    (fun R σ x => weightedField (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊
      (Sandpile.scenery d σ) x) ?_ ?_ ?_ s (by linarith)
  · intro R hR x
    exact memLp_two_weightedField_mass ν hsq hd1 _ _ x
  · intro R hR x
    exact integral_weightedField_mass ν hsq hmean hd1 _ _ x
  · intro R hR x y
    have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    have hqb : ∀ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, |q ((j : ℝ) / R ^ 2)| ≤ Q := by
      intro j hj
      refine hQ _ ⟨by positivity, ?_⟩
      have hjlt : (j : ℝ) ≤ R ^ 2 * T := by
        have h1 : j < ⌊R ^ 2 * T⌋₊ := Finset.mem_range.mp hj
        have h2 : (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast le_of_lt h1
        exact h2.trans (Nat.floor_le (by positivity))
      rw [div_le_iff₀ hR2]
      nlinarith
    rw [covariance_weightedField_mass ν hd1 _ _ x y]
    exact hdecay _ _ hqb x y

/-- The covariance of the odometer in dimension five and above decays like
`(1+|x-y|)^{-(d-4)}`, uniformly in the time: the covariance bound
`eq:odometer-covariance-bound` and the intersection estimate
`eq:dgt4-intersection-first-moment`. -/
theorem exists_dgt4_odometer_covariance_decay (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (x y : Sandpile.Site d),
      |covariance (fun σ => Sandpile.odometer σ n x) (fun σ => Sandpile.odometer σ n y)
          (Sandpile.centeredMassLaw d ν)|
        ≤ K * (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-((d : ℝ) - 4)) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  obtain ⟨C, hC, hint⟩ := (hGH d hd).2.2.2.1
  have hV : (0:ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  refine ⟨2 * variance (id : ℝ → ℝ) ν * C, by positivity, ?_⟩
  intro n x y
  have hnn := Sandpile.covariance_odometerOf_nonneg ν hsq n n x y
  have hle := Sandpile.covariance_odometerOf_le (d := d) ν hsq n n x y
  have hsumG : Summable (fun z : Sandpile.Site d =>
      Sandpile.greenTime d n x z * Sandpile.greenTime d n y z) :=
    Sandpile.summable_greenTime_mul n x _
  have hgreen : ∑' z : Sandpile.Site d,
      Sandpile.greenTime d n x z * Sandpile.greenTime d n y z
      ≤ C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
    refine le_trans ?_ (hint x y).2
    exact hsumG.tsum_le_tsum (fun z => mul_le_mul (greenTime_le_green_shift hGH hd n x z)
      (greenTime_le_green_shift hGH hd n y z) (Sandpile.greenTime_nonneg n y z)
      (le_trans (Sandpile.greenTime_nonneg n x z)
        (greenTime_le_green_shift hGH hd n x z))) (hint x y).1
  have hexp : (4 : ℝ) - (d : ℝ) = -((d : ℝ) - 4) := by ring
  rw [covariance_odometer_eq ν hd1 n x y, abs_of_nonneg hnn]
  calc covariance (fun ζ => Sandpile.odometerOf ζ n x) (fun ζ => Sandpile.odometerOf ζ n y)
        (LatticeProb.iidLaw d ν)
      ≤ 2 * variance (id : ℝ → ℝ) ν *
          ∑' z : Sandpile.Site d, Sandpile.greenTime d n x z * Sandpile.greenTime d n y z := hle
    _ ≤ 2 * variance (id : ℝ → ℝ) ν *
          (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hgreen (by positivity)
    _ = 2 * variance (id : ℝ → ℝ) ν * C *
          (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-((d : ℝ) - 4)) := by
        rw [latticeNorm_sub_eq, hexp]
        ring

/-- The diffusively scaled odometer fluctuation in dimension five and above is
tight in `H^{-s}_loc(ℝ^d)` for every `s > (d-4)/2`: the tightness half of the
first conclusion of `thm:dgt4-diffusive-membrane`. -/
theorem dgt4_odometer_tight (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ) := by
  have _hHorizon := hT
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd4 : (0:ℝ) < (d : ℝ) - 4 := by
    have : (5:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hdecay⟩ := exists_dgt4_odometer_covariance_decay hGH hd ν hsq
  refine Sandpile.Frozen.sobolev_tightness d ((d : ℝ) - 4) K hd4 (by linarith) hBesov
    (Sandpile.centeredMassLaw d ν)
    (fun R σ x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) ?_ ?_ ?_ s (by linarith)
  · intro R hR x
    exact (memLp_two_odometer ν hsq hd1 _ x).sub (memLp_const _)
  · intro R hR x
    have hix : Integrable (fun σ : Sandpile.Site d → ℝ =>
        Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) (Sandpile.centeredMassLaw d ν) :=
      integrable_odometer ν hpos hd1 _ x
    rw [integral_sub hix (integrable_const _), integral_const,
      integral_odometer_eq ν hd1 _ x]
    simp
  · intro R hR x y
    have hix : Integrable (fun σ : Sandpile.Site d → ℝ =>
        Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x) (Sandpile.centeredMassLaw d ν) :=
      integrable_odometer ν hpos hd1 _ x
    have hiy : Integrable (fun σ : Sandpile.Site d → ℝ =>
        Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ y) (Sandpile.centeredMassLaw d ν) :=
      integrable_odometer ν hpos hd1 _ y
    rw [covariance_sub_const_left hix _, covariance_sub_const_right hiy _]
    exact hdecay _ x y

/-- The same tightness with the time written as `⌊T R²⌋`, the order in which
`thm:main-explosion(iii)(d)` writes it. -/
theorem dgt4_odometer_tight' (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (hpos : Integrable (fun z => max z 0) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
      (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ) := by
  refine tight_congr_ge_one d s _ _ _ ?_
    (dgt4_odometer_tight hGH hBesov hd ν hsq hpos T hT s hs)
  intro R hR σ
  have hcomm : R ^ 2 * T = T * R ^ 2 := mul_comm _ _
  funext φ
  rw [hcomm]

/-- The weighted membrane field is additive in the weight. -/
theorem weightedField_add (q q' : ℕ → ℝ) (t : ℕ) (ζ : Sandpile.Site d → ℝ)
    (x : Sandpile.Site d) :
    weightedField (fun j => q j + q' j) t ζ x
      = weightedField q t ζ x + weightedField q' t ζ x := by
  unfold weightedField
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A nonnegative weight gives a nonnegative kernel. -/
theorem weightedKernel_nonneg (q : ℕ → ℝ) (hq : ∀ j, 0 ≤ q j) (t : ℕ)
    (x z : Sandpile.Site d) : 0 ≤ weightedKernel d q t x z := by
  unfold weightedKernel
  refine Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (hq j) (Sandpile.heatKernel_nonneg j x z)

end Sandpile.Support
