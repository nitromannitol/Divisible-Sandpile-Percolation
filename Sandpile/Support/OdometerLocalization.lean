/-
Conditional odometer localization from the Green tail outside a box.
-/
import Sandpile.Support.GreenSceneryTail
import Sandpile.Support.PinnedConcentration

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Sandpile

variable {d : ℕ}

lemma boxDist_cast_le_latticeNorm_sub [NeZero d] (y x : Site d) :
    (boxDist y x : ℝ) ≤ External.latticeNorm (y - x) := by
  have hcoord (i : Fin d) : |(((y - x) i : ℤ) : ℝ)| ≤ External.latticeNorm (y - x) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun j : Fin d => (((y - x) j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    Finset.univ_nonempty (fun i => (y i - x i).natAbs)
  unfold boxDist
  rw [hi, ← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  exact hcoord i

lemma greenTime_le_green_shift (hGH : External.GreenBoundsHigh) (hd : 5 ≤ d)
    (t : ℕ) (x y : Site d) : greenTime d t x y ≤ green d 0 (y - x) := by
  have he : greenTime d t x y = greenTime d t 0 (y - x) := by
    have h := greenTime_add_right t (0 : Site d) (y - x) x
    simpa using h
  rw [he]
  exact greenTime_le_green hGH hd t (y - x)

lemma exists_greenTime_outside_box_bounds (hGH : External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → ∀ (t : ℕ) (x : Site d),
      (∀ y : Site d, r < (boxDist y x : ℝ) →
        greenTime d t x y ≤ C * r ^ (2 - (d : ℝ))) ∧
      (∀ T : Finset (Site d),
        (∑ y ∈ T.filter (fun y => r < (boxDist y x : ℝ)), greenTime d t x y ^ 2) ≤
          C * r ^ (4 - (d : ℝ))) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, htail⟩ := (hGH d hd).1
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨C, hC, ?_⟩
  intro r hr t x
  let N : ℕ := Nat.ceil r
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr hr0
  have hrN : r ≤ (N : ℝ) := Nat.le_ceil r
  have hfar (y : Site d) (hy : r < (boxDist y x : ℝ)) :
      (N : ℝ) ≤ External.latticeNorm (y - x) := by
    have hn : N ≤ boxDist y x := Nat.ceil_le.mpr hy.le
    exact (show (N : ℝ) ≤ (boxDist y x : ℝ) by exact_mod_cast hn).trans
      (boxDist_cast_le_latticeNorm_sub y x)
  have hpow2 : (N : ℝ) ^ (2 - (d : ℝ)) ≤ r ^ (2 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr0 hrN (by linarith)
  have hpow4 : (N : ℝ) ^ (4 - (d : ℝ)) ≤ r ^ (4 - (d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hr0 hrN (by linarith)
  constructor
  · intro y hy
    exact (greenTime_le_green_shift hGH hd t x y).trans
      (((htail N hN).2.2 (y - x) (hfar y hy)).trans (mul_le_mul_of_nonneg_left hpow2 hC.le))
  · intro T
    let U := T.filter (fun y => r < (boxDist y x : ℝ))
    let V := U.image (fun y => y - x)
    have hV : ∀ z ∈ V, (N : ℝ) ≤ External.latticeNorm z := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact hfar y (Finset.mem_filter.mp hy).2
    calc
      _ ≤ ∑ y ∈ U, green d 0 (y - x) ^ 2 := Finset.sum_le_sum fun y _ =>
        pow_le_pow_left₀ (greenTime_nonneg t x y) (greenTime_le_green_shift hGH hd t x y) 2
      _ = ∑ z ∈ V, green d 0 z ^ 2 := by
        dsimp only [V]
        have hinj : ∀ a ∈ U, ∀ b ∈ U, a - x = b - x → a = b :=
          fun a _ b _ h => (Equiv.subRight x).injective h
        rw [Finset.sum_image hinj]
      _ ≤ ∑' z : {z : Site d // (N : ℝ) ≤ External.latticeNorm z}, green d 0 z ^ 2 :=
        finset_sum_le_tsum_subtype (fun z => green d 0 z ^ 2) (fun z => sq_nonneg _)
          (htail N hN).1 V hV
      _ ≤ C * (N : ℝ) ^ (4 - (d : ℝ)) := (htail N hN).2.1
      _ ≤ C * r ^ (4 - (d : ℝ)) := mul_le_mul_of_nonneg_left hpow4 hC.le

lemma odometer_condExp_tail (hGH : External.GreenBoundsHigh) (hd : 5 ≤ d)
    (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
      ∀ (S : Set (Site d)) (r a : ℝ), 1 ≤ r → 0 ≤ a → ∀ (t : ℕ) (x : Site d),
        (∀ y : Site d, (boxDist y x : ℝ) ≤ r → y ∈ S) →
        (LatticeProb.iidLaw d ν)
          {ζ | a < |odometerOf ζ t x - (MeasureTheory.condExp
            (MeasurableSpace.comap (fun ω : Site d → ℝ => fun y : S => ω y) inferInstance)
            (LatticeProb.iidLaw d ν) (fun ω => odometerOf ω t x)) ζ|} ≤
          ENNReal.ofReal (2 * Real.exp (-(c *
            min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2))))) := by
  classical
  obtain ⟨C, hC, hgreen⟩ := exists_greenTime_outside_box_bounds hGH hd
  obtain ⟨c, hc, hconc⟩ := conditional_finite_concentration (d := d) θ K hθ
  refine ⟨c / C, div_pos hc hC, ?_⟩
  intro ν hν hexp hK S r a hr ha t x hS
  haveI := hν
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hid := integrable_id_of_exp_moment ν θ hθ hexp
  have hi := integrable_odometerOf d ν hid.pos_part t x
  have htwo : (∑ z ∈ boxFinset x t, offWeight S (greenTime d t x) z ^ 2) ≤
      C * r ^ (4 - (d : ℝ)) := by
    refine le_trans ?_ ((hgreen r hr t x).2 (boxFinset x t))
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : z ∈ S
    · simp only [offWeight, hz, if_pos, zero_pow (by decide : 2 ≠ 0)]
      split_ifs <;> positivity
    · have hfar : r < (boxDist z x : ℝ) := lt_of_not_ge (fun h => hz (hS z h))
      simp [offWeight, hz, hfar]
  have hinf : ∀ z ∈ boxFinset x t, offWeight S (greenTime d t x) z ≤
      C * r ^ (2 - (d : ℝ)) := by
    intro z _
    by_cases hz : z ∈ S
    · simp only [offWeight, hz, if_pos]
      positivity
    · have hfar : r < (boxDist z x : ℝ) := lt_of_not_ge (fun h => hz (hS z h))
      simpa only [offWeight, hz, if_neg, not_false_iff] using (hgreen r hr t x).1 z hfar
  have ht := hconc ν hν hexp hK (boxFinset x t) S (fun ω => odometerOf ω t x)
    (measurable_odometerOf t x) hi
    (fun ξ η h => odometerOf_congr_box t x ξ η (fun z hz => h z (mem_boxFinset hz)))
    (greenTime d t x) (greenTime_nonneg t x)
    (fun ω z b => abs_odometerOf_update_le ω z b t x)
    (C * r ^ (4 - (d : ℝ))) (C * r ^ (2 - (d : ℝ))) htwo hinf a ha
  have hpow (q k : ℝ) : q / (C * r ^ (k - (d : ℝ))) =
      (q * r ^ ((d : ℝ) - k)) / C := by
    rw [show k - (d : ℝ) = -((d : ℝ) - k) by ring, Real.rpow_neg hr0.le]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hpow (a ^ 2) 4, hpow a 2, min_div_div_right hC.le,
    show c * (min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2)) / C) =
      c / C * min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2)) by ring] at ht
  exact ht

end Sandpile
