import Sandpile.Support.Dgt4Deviation
import Sandpile.Support.Dgt4OriginProb
import Sandpile.Support.MeanLocalization
import Sandpile.Support.ExitGreen
import Sandpile.Support.HitProb
import Sandpile.Support.SceneryBridge
import Sandpile.Support.OriginProfile

/-!
# The probability of hitting a two-point set, and the mean of the odometer killed there

This file bounds the probability that the walk hits a two-point set `{0, z}`, and uses that
bound to lower-bound the mean of the odometer killed at the origin and at one further site `z`.
The hitting probability is `P_x(τ_{0,z} < ∞) = (G(x,0) + G(x,z))/(G(0,0) + G(0,z))`
(`pairPotential`), but only an upper bound is needed, and an upper bound needs no potential
theory: the right-hand side is nonnegative, equals one at the two points, and is harmonic
elsewhere, so the probability of hitting the set by time `k` is below it by induction on `k`
(`walkLaw_hitSetBy_le`). Averaged over the neighbours of the origin the bound is
`1 - 1/(G(0,0) + G(0,z))`, and `lem:localization-killing` turns that into the lower bound on the
mean, `mean_avg_pairOdometer_ge`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### A harmonic majorant bounds the probability of hitting a set -/

/-- The event that the walk has visited `A` by time `k`. -/
def hitSetBy (A : Set (Site d)) (k : ℕ) : Set (ℕ → Site d) := {X | ∃ j ≤ k, X j ∈ A}

/-- `hitSetBy A k` is measurable: it is a finite union, over `j ≤ k`, of preimages of `A` under
the coordinate projections `X ↦ X j`. -/
theorem measurableSet_hitSetBy (A : Set (Site d)) (k : ℕ) :
    MeasurableSet (hitSetBy A k) := by
  have h : hitSetBy A k
      = ⋃ j ∈ Finset.range (k + 1), (fun X : ℕ → Site d => X j) ⁻¹' A := by
    ext X
    simp only [hitSetBy, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Set.mem_preimage,
      exists_prop]
    exact ⟨fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩, fun ⟨j, hj, h⟩ => ⟨j, by omega, h⟩⟩
  rw [h]
  exact MeasurableSet.biUnion (Finset.range (k + 1)).countable_toSet
    fun j _ => (measurable_pi_apply j) (Set.to_countable A).measurableSet

/-- If `x` already lies in `A`, the walk from `x` has hit `A` by any positive time, so the
preimage of `hitSetBy A (k + 1)` under `sitePath x` is all of the sample space. -/
theorem preimage_hitSetBy_succ_of_mem (A : Set (Site d)) {x : Site d} (hx : x ∈ A) (k : ℕ) :
    LatticeProb.sitePath x ⁻¹' hitSetBy A (k + 1) = Set.univ := by
  ext ξ
  simp only [Set.mem_preimage, Set.mem_univ, iff_true, hitSetBy, Set.mem_setOf_eq]
  exact ⟨0, by omega, by rw [LatticeProb.sitePath_zero]; exact hx⟩

/-- If `x` does not lie in `A`, hitting `A` by time `k + 1` from `x` is the same event as
hitting `A` by time `k` from the walk's position one step later. -/
theorem preimage_hitSetBy_succ_of_notMem (A : Set (Site d)) {x : Site d} (hx : x ∉ A) (k : ℕ) :
    LatticeProb.sitePath x ⁻¹' hitSetBy A (k + 1)
      = {ξ : ℕ → Site d |
          LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ hitSetBy A k} := by
  ext ξ
  simp only [Set.mem_preimage, Set.mem_setOf_eq, hitSetBy]
  have hkey : ∀ m : ℕ, LatticeProb.sitePath x ξ (m + 1)
      = LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) m := by
    intro m
    have h := LatticeProb.sitePath_consNat x (ξ 0) (LatticeProb.tailNat ξ) m
    rw [LatticeProb.consNat_head_tail] at h
    exact h
  constructor
  · rintro ⟨j, hj, h⟩
    cases j with
    | zero => rw [LatticeProb.sitePath_zero] at h; exact absurd h hx
    | succ m => exact ⟨m, by omega, by rw [← hkey m]; exact h⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨m + 1, by omega, by rw [hkey m]; exact h⟩

/-- **A nonnegative function harmonic off `A` and at least one on `A` bounds the probability
of hitting `A`.**  Induction on the horizon: at a site of `A` the bound is the value one, and
elsewhere one step of the walk replaces the function by its neighbour average, which is the
function itself. -/
theorem walkLaw_hitSetBy_le (hd : 1 ≤ d) [NeZero d] (A : Set (Site d)) (ψ : Site d → ℝ)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψA : ∀ x ∈ A, 1 ≤ ψ x)
    (hψh : ∀ x, x ∉ A → LatticeProb.walkOp ψ x = ψ x) :
    ∀ (k : ℕ) (x : Site d), walkLaw d x (hitSetBy A k) ≤ ENNReal.ofReal (ψ x) := by
  intro k
  induction k with
  | zero =>
      intro x
      show LatticeProb.siteWalkLaw d x (hitSetBy A 0) ≤ _
      rw [LatticeProb.siteWalkLaw, Measure.map_apply (LatticeProb.measurable_sitePath x)
        (measurableSet_hitSetBy A 0)]
      by_cases hx : x ∈ A
      · refine le_trans (measure_mono (Set.subset_univ _)) ?_
        rw [measure_univ]
        exact ENNReal.one_le_ofReal.mpr (hψA x hx)
      · have hpre : LatticeProb.sitePath x ⁻¹' hitSetBy A 0 = ∅ := by
          ext ξ
          simp only [Set.mem_preimage, hitSetBy, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false, not_exists]
          rintro j ⟨hj, h⟩
          rw [Nat.le_zero] at hj
          subst hj
          rw [LatticeProb.sitePath_zero] at h
          exact hx h
        rw [hpre, measure_empty]
        exact bot_le
  | succ k ih =>
      intro x
      show LatticeProb.siteWalkLaw d x (hitSetBy A (k + 1)) ≤ _
      rw [LatticeProb.siteWalkLaw, Measure.map_apply (LatticeProb.measurable_sitePath x)
        (measurableSet_hitSetBy A (k + 1))]
      by_cases hx : x ∈ A
      · rw [preimage_hitSetBy_succ_of_mem A hx k, measure_univ]
        exact ENNReal.one_le_ofReal.mpr (hψA x hx)
      · rw [preimage_hitSetBy_succ_of_notMem A hx k]
        set B : Set (ℕ → Site d) := hitSetBy A k with hB
        have hBm : MeasurableSet B := measurableSet_hitSetBy A k
        have hshift : Measurable fun ξ : ℕ → Site d =>
            LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) :=
          LatticeProb.measurable_sitePath_uncurry.comp
            ((((measurable_of_countable fun v : Site d => x + v).comp
              (measurable_pi_apply 0))).prodMk LatticeProb.measurable_tailNat)
        have hset : MeasurableSet {ξ : ℕ → Site d |
            LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B} := hshift hBm
        have hmeas : Measurable (Set.indicator {ξ : ℕ → Site d |
            LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B}
            (1 : (ℕ → Site d) → ℝ≥0∞)) := measurable_one.indicator hset
        have e1 : (Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d)
              {ξ : ℕ → Site d | LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B}
            = ∫⁻ ξ, Set.indicator {ξ : ℕ → Site d |
                LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B}
                (1 : (ℕ → Site d) → ℝ≥0∞) ξ
              ∂(Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d) :=
          (lintegral_indicator_one hset).symm
        have e2 : ∀ u : Site d,
            (∫⁻ ω, Set.indicator {ξ : ℕ → Site d |
                LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B}
                (1 : (ℕ → Site d) → ℝ≥0∞) (LatticeProb.consNat u ω)
              ∂(Measure.infinitePi fun _ : ℕ => LatticeProb.incLaw d))
              ≤ ENNReal.ofReal (ψ (x + u)) := by
          intro u
          have hpre : ∀ ω : ℕ → Site d,
              Set.indicator {ξ : ℕ → Site d |
                  LatticeProb.sitePath (x + ξ 0) (LatticeProb.tailNat ξ) ∈ B}
                  (1 : (ℕ → Site d) → ℝ≥0∞) (LatticeProb.consNat u ω)
                = Set.indicator (LatticeProb.sitePath (x + u) ⁻¹' B)
                  (1 : (ℕ → Site d) → ℝ≥0∞) ω := fun _ => rfl
          rw [lintegral_congr hpre,
            lintegral_indicator_one (LatticeProb.measurable_sitePath (x + u) hBm),
            ← Measure.map_apply (LatticeProb.measurable_sitePath (x + u)) hBm]
          exact ih (x + u)
        rw [e1, LatticeProb.lintegral_infinitePi_nat_head_tail (μ := LatticeProb.incLaw d) _ hmeas]
        refine le_trans (lintegral_mono e2) ?_
        rw [← ofReal_integral_eq_lintegral_ofReal
              (LatticeProb.integrable_of_incLaw hd _)
              (Filter.Eventually.of_forall fun u => hψ0 (x + u)),
          LatticeProb.integral_incLaw_add, hψh x hx]

/-! ### The harmonic majorant of the two-point set -/

/-- `(G(x,0)+G(x,z))/(G(0,0)+G(0,z))`, the probability that the walk from `x` ever hits
`\{0,z\}` (`sandpile.tex:5363`). -/
noncomputable def pairPotential (d : ℕ) (z x : Site d) : ℝ :=
  (green d x 0 + green d x z) / (green d 0 0 + green d 0 z)

/-- The denominator `G(0,0) + G(0,z)` of `pairPotential` is positive, since `G(0,0) ≥ 1` and
`G(0,z) ≥ 0`. -/
theorem pair_denom_pos (hd : 3 ≤ d) (z : Site d) : 0 < green d 0 0 + green d 0 z :=
  lt_of_lt_of_le zero_lt_one
    (le_trans (one_le_green hd) (le_add_of_nonneg_right (green_nonneg _ _)))

/-- `pairPotential d z x` is nonnegative, as a ratio of nonnegative Green values. -/
theorem pairPotential_nonneg (hd : 3 ≤ d) (z x : Site d) : 0 ≤ pairPotential d z x :=
  div_nonneg (add_nonneg (green_nonneg _ _) (green_nonneg _ _)) (pair_denom_pos hd z).le

/-- `pairPotential d z` equals one at the origin. -/
theorem pairPotential_origin (hd : 3 ≤ d) (z : Site d) : pairPotential d z 0 = 1 := by
  rw [pairPotential, div_self (pair_denom_pos hd z).ne']

/-- `pairPotential d z` equals one at `z`, by the shift symmetry `G(z,z) = G(0,0)` and
`G(z,0) = G(0,z)`. -/
theorem pairPotential_site (hd : 3 ≤ d) (z : Site d) : pairPotential d z z = 1 := by
  have h1 : green d z z = green d 0 0 := by rw [green_shift, sub_self, green_shift, sub_zero]
  have h2 : green d z 0 = green d 0 z := green_symm (by omega) z 0
  rw [pairPotential, h1, h2, add_comm (green d 0 z) (green d 0 0),
    div_self (pair_denom_pos hd z).ne']

/-- `pairPotential d z` is harmonic away from `{0, z}`: its neighbour average at a site
`x ≠ 0, z` equals its own value there, since each of `G(·,0)` and `G(·,z)` is harmonic off its
own pole. -/
theorem walkOp_pairPotential (hd : 3 ≤ d) (z : Site d) {x : Site d} (hx0 : x ≠ 0) (hxz : x ≠ z) :
    LatticeProb.walkOp (pairPotential d z) x = pairPotential d z x := by
  show LatticeProb.walkOp
      (fun y => (green d y 0 + green d y z) / (green d 0 0 + green d 0 z)) x
    = (green d x 0 + green d x z) / (green d 0 0 + green d 0 z)
  rw [LatticeProb.walkOp_div_const]
  congr 1
  show Sandpile.avg (fun y => green d y 0 + green d y z) x = green d x 0 + green d x z
  rw [Sandpile.avg_add, avg_green hd x 0, avg_green hd x z, if_neg hx0, if_neg hxz]
  ring

/-- The neighbour average of `pairPotential d z` at the origin falls short of one by at least
`1/(G(0,0) + G(0,z))`, the size of the one-step Green correction in the Poisson-kernel
identity. -/
theorem one_sub_avg_pairPotential_origin (hd : 3 ≤ d) (z : Site d) :
    1 / (green d 0 0 + green d 0 z)
      ≤ 1 - LatticeProb.walkOp (pairPotential d z) 0 := by
  have hpos := pair_denom_pos hd z
  have hval : LatticeProb.walkOp (pairPotential d z) 0
      = (green d 0 0 - 1 + (green d 0 z - (if (0 : Site d) = z then 1 else 0)))
        / (green d 0 0 + green d 0 z) := by
    show LatticeProb.walkOp
        (fun y => (green d y 0 + green d y z) / (green d 0 0 + green d 0 z)) 0 = _
    rw [LatticeProb.walkOp_div_const]
    congr 1
    show Sandpile.avg (fun y => green d y 0 + green d y z) 0 = _
    rw [Sandpile.avg_add, avg_green hd 0 0, avg_green hd 0 z, if_pos rfl]
  rw [hval, le_sub_iff_add_le, ← add_div, div_le_one hpos]
  split_ifs with h <;> linarith

/-! ### The lower bound on the mean of the odometer killed at two sites -/

/-- The set the walk is killed on hitting. -/
theorem pairKilled_compl (z : Site d) :
    {x : Site d | x ≠ 0 ∧ x ≠ z} = ({x : Site d | x = 0 ∨ x = z})ᶜ := by
  ext x; simp [not_or]

/-- **`lem:localization-killing` at a two-point killing set.**  The mean of the odometer
killed at `\{0,z\}` is at least the escape probability times the mean of the free odometer. -/
theorem pairPotential_hyps (hd : 3 ≤ d) (z : Site d) :
    (∀ x : Site d, 0 ≤ pairPotential d z x)
      ∧ (∀ x ∈ {w : Site d | w = 0 ∨ w = z}, 1 ≤ pairPotential d z x)
      ∧ (∀ x : Site d, x ∉ {w : Site d | w = 0 ∨ w = z} →
          LatticeProb.walkOp (pairPotential d z) x = pairPotential d z x) := by
  refine ⟨pairPotential_nonneg hd z, ?_, ?_⟩
  · intro x hx
    rcases hx with h | h
    · rw [h]; exact le_of_eq (pairPotential_origin hd z).symm
    · rw [h]; exact le_of_eq (pairPotential_site hd z).symm
  · intro x hx
    simp only [Set.mem_setOf_eq, not_or] at hx
    exact walkOp_pairPotential hd z hx.1 hx.2

/-- **`lem:localization-killing` at a two-point killing set, pointwise.** The mean at `x` of the
odometer killed on hitting `{0, z}` is at least `(1 - pairPotential d z x)` times the mean at
the origin of the free odometer. -/
theorem mean_pairOdometer_ge (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun y : ℝ => max y 0) ν) (n : ℕ) (z x : Site d) :
    (1 - pairPotential d z x) * (∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν))
      ≤ ∫ ζ, pairOdometer z ζ n x ∂(LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hd3 : (3 : ℕ) ≤ d := by omega
  have hU : 0 ≤ ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) :=
    integral_nonneg fun ζ => odometerOf_nonneg ζ n 0
  by_cases hx : x ∈ {w : Site d | w ≠ 0 ∧ w ≠ z}
  · obtain ⟨h0, h1, h2⟩ := pairPotential_hyps hd3 z
    have hsub : {X : ℕ → Site d | exitNat {w : Site d | w ≠ 0 ∧ w ≠ z} n X ≤ n}
        ⊆ hitSetBy {w : Site d | w = 0 ∨ w = z} n := by
      intro X hX
      obtain ⟨j, hj, hjD⟩ := exitNat_le_iff.mp hX
      refine ⟨j, hj, ?_⟩
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hjD
      exact hjD
    have hq : ((walkLaw d x)
        {X : ℕ → Site d | exitNat {w : Site d | w ≠ 0 ∧ w ≠ z} n X ≤ n}).toReal
          ≤ pairPotential d z x := by
      have hmono : (walkLaw d x)
          {X : ℕ → Site d | exitNat {w : Site d | w ≠ 0 ∧ w ≠ z} n X ≤ n}
            ≤ ENNReal.ofReal (pairPotential d z x) :=
        le_trans (measure_mono hsub)
          (walkLaw_hitSetBy_le hd1 {w : Site d | w = 0 ∨ w = z} (pairPotential d z)
            h0 h1 h2 n x)
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
      rwa [ENNReal.toReal_ofReal (h0 x)] at this
    have hloc := (mean_localization_bound hd1 ν hpos {w : Site d | w ≠ 0 ∧ w ≠ z} n x hx).2
    nlinarith [hloc, hq, hU]
  · have hz : pairOdometer z (d := d) = fun ζ n => localizedOdometer
        {w : Site d | w ≠ 0 ∧ w ≠ z} ζ n := rfl
    have h0 : ∫ ζ, pairOdometer z ζ n x ∂(LatticeProb.iidLaw d ν) = 0 := by
      simp only [localizedOdometer_of_notMem _ _ n hx, integral_zero]
    have hone : pairPotential d z x = 1 := by
      simp only [Set.mem_setOf_eq, not_and_or, not_not] at hx
      rcases hx with h | h
      · rw [h]; exact pairPotential_origin hd3 z
      · rw [h]; exact pairPotential_site hd3 z
    rw [h0, hone]
    simp

/-- The mean of the neighbour average is the neighbour average of the means. -/
theorem integral_avg_pairOdometer (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun y : ℝ => max y 0) ν) (n : ℕ) (z : Site d) :
    (∫ ζ, Sandpile.avg (pairOdometer z ζ n) 0 ∂(LatticeProb.iidLaw d ν))
      = Sandpile.avg (fun x => ∫ ζ, pairOdometer z ζ n x ∂(LatticeProb.iidLaw d ν)) 0 :=
  integral_avg_field
    (fun x => integrable_localizedOdometer hd ν hpos {w : Site d | w ≠ 0 ∧ w ≠ z} n x) 0

/-- **The mean of `Pu_n^{\Z^d\setminus\{0,z\}}(0)` is at least `\E u_n(0)/(G(0,0)+G(0,z))`.** -/
theorem mean_avg_pairOdometer_ge (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun y : ℝ => max y 0) ν) (n : ℕ) (z : Site d) :
    (∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) / (green d 0 0 + green d 0 z)
      ≤ ∫ ζ, Sandpile.avg (pairOdometer z ζ n) 0 ∂(LatticeProb.iidLaw d ν) := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hd3 : (3 : ℕ) ≤ d := by omega
  have hU : 0 ≤ ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) :=
    integral_nonneg fun ζ => odometerOf_nonneg ζ n 0
  rw [integral_avg_pairOdometer hd1 ν hpos n z]
  have hstep : Sandpile.avg (fun x => (1 - pairPotential d z x) *
        ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) 0
      ≤ Sandpile.avg (fun x => ∫ ζ, pairOdometer z ζ n x ∂(LatticeProb.iidLaw d ν)) 0 :=
    avg_mono_le (fun x => mean_pairOdometer_ge hd ν hpos n z x) 0
  have hval : Sandpile.avg (fun x => (1 - pairPotential d z x) *
        ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) 0
      = (1 - LatticeProb.walkOp (pairPotential d z) 0) *
        ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    show LatticeProb.walkOp (fun x => (1 - pairPotential d z x) *
        ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) 0 = _
    rw [LatticeProb.walkOp_mul_const]
    congr 1
    show LatticeProb.walkOp (fun y => (1 : ℝ) - pairPotential d z y) 0 = _
    rw [LatticeProb.walkOp_sub, LatticeProb.walkOp_const hd1]
  refine le_trans ?_ hstep
  rw [hval]
  have h2 := mul_le_mul_of_nonneg_right (one_sub_avg_pairPotential_origin hd3 z) hU
  rwa [one_div, inv_mul_eq_div] at h2

/-- **`PairKilledMeanLower`.**  The residual of the first step of the heavy-tailed case
(`sandpile.tex:5369-5371`).  The escape probability from `\{0,z\}` averaged over the
neighbours of the origin is `1/(G(0,0)+G(0,z))`, at least `1/(2G(0,0))` since the Green
function is largest on the diagonal, while `\E Pw_n(0)` is asymptotically `\E u_n(0)/G(0,0)`;
the ratio is therefore eventually at least `1/2`, and a third is enough. -/
theorem pairKilledMeanLower (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ y : ℝ, ν {y} = 0) (hmeanν : ∫ y, y ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    PairKilledMeanLower d ν := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hd3 : (3 : ℕ) ≤ d := by omega
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hpos : Integrable (fun y : ℝ => max y 0) ν := by
    have hid : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
    refine hid.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    show |max y 0| ≤ |y|
    rcases le_or_gt 0 y with h | h
    · rw [max_eq_left h, abs_of_nonneg h]
    · rw [max_eq_right h.le, abs_zero]
      exact abs_nonneg y
  have hG : (0 : ℝ) < green d 0 0 := lt_of_lt_of_le zero_lt_one (one_le_green hd3)
  have hratio := tendsto_meanAvg_originOdometer_ratio hGH d hd ν hatom hmeanν hvar hvar'
  filter_upwards [hratio.eventually_lt_const (by norm_num : (1 : ℝ) < 3 / 2),
    hratio.eventually_const_lt (by norm_num : (1 : ℝ) / 2 < 1)] with n h1 h2
  intro z₀
  have hU0 : 0 ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n :=
    integral_nonneg fun _ => Sandpile.odometer_nonneg _ _ _
  have hUpos : 0 < Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n := by
    rcases eq_or_lt_of_le hU0 with h | h
    · exfalso
      rw [← h] at h2
      simp only [zero_div, div_zero] at h2
      linarith
    · exact h
  have hq : (0 : ℝ) < Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / green d 0 0 :=
    div_pos hUpos hG
  have hM : meanOriginAverage d ν n
      < 3 / 2 * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / green d 0 0) :=
    (div_lt_iff₀ hq).mp h1
  have hUeq : Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n
      = ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := meanOdometer_eq d ν hd1 n
  have hden : green d 0 0 + green d 0 z₀ ≤ 2 * green d 0 0 := by
    have := green_le_diagonal hd3 (0 : Site d) z₀
    linarith
  have hUnn : 0 ≤ ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) :=
    integral_nonneg fun ζ => odometerOf_nonneg ζ n 0
  refine le_trans ?_ (mean_avg_pairOdometer_ge hd ν hpos n z₀)
  have hstep : meanOriginAverage d ν n / 3
      ≤ (∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) / (2 * green d 0 0) := by
    rw [hUeq] at hM
    have hG2 : (0 : ℝ) < 2 * green d 0 0 := by linarith
    have hM' : meanOriginAverage d ν n * (2 * green d 0 0)
        < 3 * ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
      rw [show (3 : ℝ) / 2 * ((∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) / green d 0 0)
          = (3 * ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) / (2 * green d 0 0) by
        field_simp] at hM
      rw [lt_div_iff₀ hG2] at hM
      exact hM
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 3) hG2]
    linarith
  refine le_trans hstep ?_
  gcongr
  exact pair_denom_pos hd3 z₀

/-- **Case (b) of `prop:dgt4-contact-asymptotics`, with no residual.**  Everything of
`sandpile.tex:5301-5412` is now proved. -/
theorem caseThresholdField_linear
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p : ℝ} (hα : 1 < α) (hp : 0 < p) (hpα : α < 2 * p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d => greenRatioWeight d z ^ p)
    (Mb : ℝ) (hMb : ν (Set.Ioi Mb) = 0) :
    CaseThresholdField d ν (1 - 1 / α) :=
  caseThresholdField_linear_of_pairKilled hGH hd ν hatom hmeanν hvar hvar' hα hp hpα hmom hrv
    hsumc Mb hMb (pairKilledMeanLower hGH hd ν hatom hmeanν hvar hvar')

end Sandpile
