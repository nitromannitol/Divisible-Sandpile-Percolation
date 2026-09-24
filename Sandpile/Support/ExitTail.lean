import Mathlib
import Sandpile.Support.ExitGreen
import Sandpile.Support.IncrementBall
import LatticeProb.Invariance

set_option maxHeartbeats 1000000
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace Sandpile

theorem walkLaw_univ {d : ℕ} (hd : 1 ≤ d) (x : Site d) : (walkLaw d x) Set.univ = 1 := by
  haveI : ∀ i : ℕ, IsProbabilityMeasure (stepLaw d) := fun i => by
    have h := LatticeProb.instructionLaw_isProbability hd (0 : Site d)
    exact h
  rw [walkLaw, Measure.map_apply (measurable_walkPath x), Set.preimage_univ]
  simp
  exact MeasurableSet.univ

theorem exit_tail_arith (d : ℕ) (r A : ℕ) (gc : ℝ) (hr : 1 ≤ r) (hA : 1 ≤ A)
    (hgc : 0 ≤ gc) :
    (2*r+1:ℝ)^d * (Real.sqrt 2 ^ d * gc * ((A:ℝ)*(r:ℝ)^2)^(-(d:ℝ)/2)) ≤
      3^d * (Real.sqrt 2 ^ d * gc * (A:ℝ)^(-(d:ℝ)/2)) := by
  rcases eq_or_lt_of_le hgc with hgc0 | hgc0
  · subst hgc0
    simp only [mul_zero]
    norm_num
  · have hsplit : ((A:ℝ)*(r:ℝ)^2)^(-(d:ℝ)/2) = (A:ℝ)^(-(d:ℝ)/2) * ((r:ℝ)^2)^(-(d:ℝ)/2) :=
      Real.mul_rpow (by positivity) (by positivity)
    have hrpow : ((r:ℝ)^2)^(-(d:ℝ)/2) = (r:ℝ)^(-(d:ℝ)) := by
      rw [sq (a := (r:ℝ)), Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_add (by positivity)]
      congr 1
      ring
    rw [hsplit, hrpow]
    have hA0 : 0 < (A:ℝ)^(-(d:ℝ)/2) := by positivity
    have hs2 : 0 < Real.sqrt 2 ^ d := by positivity
    have hgc0' : 0 < gc := hgc0
    have h1 : (2*r+1:ℝ) ≤ 3*(r:ℝ) := by exact_mod_cast (by omega : (2*r+1 : ℕ) ≤ 3*r)
    have hr : (0:ℝ) < (r:ℝ) := by positivity
    have h3 : ((2*r+1:ℝ)/(r:ℝ))^d = (2*r+1:ℝ)^d * (r:ℝ)^(-(d:ℝ)) := by
      rw [div_pow, div_eq_inv_mul, ← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
      ring
    have h4 : ((2*r+1:ℝ)/(r:ℝ))^d ≤ 3^d := by
      gcongr
      rw [div_le_iff₀ hr]
      exact h1
    -- rewrite the goal into ((2r+1)/r)^d * (positive stuff) ≤ 3^d * (positive stuff)
    have hkey : (2*r+1:ℝ)^d * (r:ℝ)^(-(d:ℝ)) ≤ 3^d := by
      rw [← h3]
      have hq : (2*r+1:ℝ)/(r:ℝ) ≤ 3 := by
        rw [div_le_iff₀ hr]
        exact h1
      gcongr
    -- now the goal: (2r+1)^d * (√2^d * gc * (A^{-d/2} * r^{-d})) ≤ 3^d * (√2^d * gc * A^{-d/2})
    have hpos : 0 < (Real.sqrt 2 ^ d * gc * (A:ℝ)^(-(d:ℝ)/2)) := by
      have hs2 : 0 < Real.sqrt 2 ^ d := by positivity
      have hgc0' : 0 < gc := hgc0
      have hA0 : (0:ℝ) < (A:ℝ) := by positivity
      have hA1 : 0 < (A:ℝ)^(-(d:ℝ)/2) := Real.rpow_pos_of_pos hA0 _
      positivity
    calc (2*r+1:ℝ)^d * (Real.sqrt 2 ^ d * gc * ((A:ℝ)^(-(d:ℝ)/2) * (r:ℝ)^(-(d:ℝ))))
        = ((2*r+1:ℝ)^d * (r:ℝ)^(-(d:ℝ))) * (Real.sqrt 2 ^ d * gc * (A:ℝ)^(-(d:ℝ)/2)) := by ring
      _ ≤ 3^d * (Real.sqrt 2 ^ d * gc * (A:ℝ)^(-(d:ℝ)/2)) :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
      _ = 3^d * (√2 ^ d * gc * (A:ℝ)^(-(d:ℝ)/2)) := by ring

theorem exitTime_gt_implies_mem {d : ℕ} (D : Set (Site d)) (n : ℕ) :
    {X : ℕ → Site d | exitTime D X > ((n : ℕ) : ℕ∞)} ⊆ {X : ℕ → Site d | X n ∈ D} := by
  intro X hX
  by_contra h
  have hmem : ((n : ℕ) : ℕ∞) ∈ {k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ D} :=
    ⟨n, rfl, h⟩
  exact absurd (sInf_le hmem) (not_le.mpr hX)

theorem exists_exit_tail {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r A : ℕ), 1 ≤ r → 1 ≤ A →
      (walkLaw d 0) {X : ℕ → Site d |
        exitTime {y : Site d | ∀ i, |y i| ≤ (r : ℤ)} X > (((A * r ^ 2 : ℕ) : ℕ∞))} ≤
        ENNReal.ofReal (C / (A : ℝ) ^ ((d : ℝ) / 2)) := by
  refine ⟨(3:ℝ) ^ d * (2:ℝ) ^ ((d:ℝ)/2) * LatticeProb.greenConst d + 1, ?_, ?_⟩
  · have := LatticeProb.greenConst_nonneg d
    positivity
  · intro r A hr hA
    set D : Set (Site d) := {y : Site d | ∀ i, |y i| ≤ (r : ℤ)} with hDdef
    set n := A * r ^ 2 with hn
    have hsub : {X : ℕ → Site d | exitTime D X > ((n : ℕ) : ℕ∞)} ⊆
        {X : ℕ → Site d | X n ∈ D} := exitTime_gt_implies_mem D n
    have hmono : (walkLaw d 0) {X : ℕ → Site d | exitTime D X > ((n : ℕ) : ℕ∞)} ≤
        (walkLaw d 0) {X : ℕ → Site d | X n ∈ D} := measure_mono hsub
    have key : ∀ (a : ℤ), |a| ≤ (r:ℤ) → a.natAbs ≤ r := by
      intro a h
      rw [Int.abs_eq_natAbs a] at h
      exact_mod_cast h
    have hboxdist : ∀ y : Site d, y ∈ boxFinset 0 r → boxDist 0 y ≤ r := by
      intro y hy
      have hyi : ∀ i, y i ∈ Finset.Icc ((0 : Site d) i - r) ((0 : Site d) i + r) :=
        Fintype.mem_piFinset.mp hy
      have hx : ∀ i, |y i - (0 : Site d) i| ≤ r := by
        intro i
        have h2 := (Finset.mem_Icc.mp (hyi i))
        have h3 : |y i - (0 : Site d) i| = (y i - (0 : Site d) i).natAbs :=
          Int.abs_eq_natAbs _
        omega
      refine Finset.sup_le fun i _ => key _ (by rw [abs_sub_comm]; exact hx i)
    have hset : {X : ℕ → Site d | X n ∈ D} = {X : ℕ → Site d | X n ∈ (boxFinset 0 r)} := by
      ext X
      simp only [Set.mem_setOf_eq, hDdef]
      constructor
      · intro h
        have hx : ∀ i, |X n i - (0 : Site d) i| ≤ r := by simpa using h
        exact mem_boxFinset (by
          simp only [boxDist]
          exact Finset.sup_le fun i _ => key _ (by rw [abs_sub_comm]; exact hx i))
      · intro h
        have hbd : boxDist 0 (X n) ≤ r := hboxdist _ h
        have hx : ∀ i, |X n i - (0 : Site d) i| ≤ r := by
          intro i
          have h1 := le_trans (Finset.le_sup (f := fun i => ((0 : Site d) i - X n i).natAbs)
            (Finset.mem_univ i)) hbd
          have h3 : |X n i - (0 : Site d) i| = ((0 : Site d) i - X n i).natAbs := by
            rw [abs_sub_comm]
            exact Int.abs_eq_natAbs _
          omega
        simpa using hx
    -- reduce to a real inequality via measure_mono and the finite-sum identity
    have hmeas : MeasurableSet {X : ℕ → Site d | X n ∈ (boxFinset 0 r)} :=
      (measurable_pi_apply n) (Set.to_countable _).measurableSet
    have hle1 : (walkLaw d 0) {X : ℕ → Site d | exitTime D X > ((n : ℕ) : ℕ∞)} ≤
        (walkLaw d 0) {X : ℕ → Site d | X n ∈ (boxFinset 0 r)} := by
      refine le_trans (measure_mono hsub) ?_
      rw [hset]
    have hreal : (walkLaw d 0).real {X : ℕ → Site d | X n ∈ (boxFinset 0 r)} =
        ∑ y ∈ boxFinset 0 r, heatKernel d n 0 y :=
      measure_walk_mem_finset hd 0 n (boxFinset 0 r)
    -- bound each heat kernel value by the Gaussian sup bound
    have hsup : ∀ y ∈ boxFinset 0 r,
        heatKernel d n 0 y ≤ Real.sqrt 2 ^ d * LatticeProb.greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2) := by
      intro y _
      rw [Sandpile.External.heatKernel_eq_srwHeat d n 0 y]
      have hn1 : 1 ≤ n := by
        rw [hn]
        nlinarith
      exact LatticeProb.srwHeat_sup_bound (by omega) hn1 _
    -- sum bound
    have hsum : ∑ y ∈ boxFinset 0 r, heatKernel d n 0 y ≤
        (boxFinset (0 : Site d) r).card * (Real.sqrt 2 ^ d * LatticeProb.greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) := by
      calc ∑ y ∈ boxFinset 0 r, heatKernel d n 0 y
          ≤ ∑ y ∈ boxFinset 0 r, (Real.sqrt 2 ^ d * LatticeProb.greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) :=
            Finset.sum_le_sum fun y hy => hsup y hy
        _ = (boxFinset (0 : Site d) r).card * (Real.sqrt 2 ^ d * LatticeProb.greenConst d * (n : ℝ) ^ (-(d : ℝ) / 2)) :=
            by simp [Finset.sum_const]
    -- card bound
    have hcard : (boxFinset (0 : Site d) r).card = (2 * r + 1) ^ d := by
      rw [card_boxFinset]
    -- combine
    have hgc : 0 ≤ LatticeProb.greenConst d := LatticeProb.greenConst_nonneg d
    have hnpos : 0 < (n : ℝ) := by positivity
    -- combine: the measure equals ofReal of the sum, and the sum is bounded
    have htop : (walkLaw d 0) {X : ℕ → Site d | X n ∈ (boxFinset (0 : Site d) r)} ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
        (by rw [walkLaw_univ hd 0]; exact ENNReal.one_lt_top))
    have hmeas2 : (walkLaw d 0) {X : ℕ → Site d | X n ∈ (boxFinset (0 : Site d) r)} =
        ENNReal.ofReal ((walkLaw d 0).real {X : ℕ → Site d | X n ∈ (boxFinset (0 : Site d) r)}) := by
      rw [Measure.real, ENNReal.ofReal_toReal htop]
    have harith := exit_tail_arith d r A _ hr hA hgc
    have hbound : (((2 * r + 1 : ℕ) ^ d) : ℝ) * (Real.sqrt 2 ^ d * LatticeProb.greenConst d *
        ((n : ℝ) ^ (-(d : ℝ) / 2))) ≤
        (3:ℝ) ^ d * (Real.sqrt 2 ^ d * LatticeProb.greenConst d * (A : ℝ) ^ (-(d : ℝ) / 2)) := by
      have h2r1 : (((2 * r + 1 : ℕ) ^ d) : ℝ) = (2 * (r : ℝ) + 1) ^ ((d:ℕ)) := by
        push_cast
        ring
      rw [hn, h2r1]
      push_cast
      exact harith
    have hle2 : ENNReal.ofReal (∑ y ∈ boxFinset 0 r, heatKernel d n 0 y) ≤
        ENNReal.ofReal ((3:ℝ) ^ d * (Real.sqrt 2 ^ d * LatticeProb.greenConst d *
          (A : ℝ) ^ (-(d : ℝ) / 2))) := by
      refine ENNReal.ofReal_le_ofReal ?_
      calc ∑ y ∈ boxFinset 0 r, heatKernel d n 0 y
          ≤ (((2 * r + 1 : ℕ) ^ d) : ℝ) * (Real.sqrt 2 ^ d * LatticeProb.greenConst d *
              ((n : ℝ) ^ (-(d : ℝ) / 2))) := by
            rw [hcard, Nat.cast_pow] at hsum
            exact hsum
        _ ≤ (3:ℝ) ^ d * (Real.sqrt 2 ^ d * LatticeProb.greenConst d * (A : ℝ) ^ (-(d : ℝ) / 2)) :=
            hbound
    have hle3 : ENNReal.ofReal ((3:ℝ) ^ d * (Real.sqrt 2 ^ d * LatticeProb.greenConst d *
          (A : ℝ) ^ (-(d : ℝ) / 2))) ≤
        ENNReal.ofReal (((3:ℝ) ^ d * (2:ℝ) ^ ((d:ℝ)/2) * LatticeProb.greenConst d + 1) /
          (A : ℝ) ^ ((d : ℝ) / 2)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hsqrt : Real.sqrt 2 ^ d = (2:ℝ) ^ ((d:ℝ)/2) := by
        have h2 : ((2:ℝ)^(1/2:ℝ))^d = ((2:ℝ)^(1/2:ℝ))^(d:ℝ) := (Real.rpow_natCast _ d).symm
        rw [Real.sqrt_eq_rpow, h2]
        have h3 : (2:ℝ)^((1/2:ℝ)*(d:ℝ)) = ((2:ℝ)^(1/2:ℝ))^(d:ℝ) :=
          Real.rpow_mul (x := 2) (by norm_num) ((1:ℝ)/2) ((d:ℝ))
        rw [← h3]
        congr 1
        ring
      have hneg : (A : ℝ) ^ (-(d:ℝ)/2) = 1 / (A:ℝ) ^ ((d:ℝ)/2) := by
        have hA0 : (0:ℝ) < (A:ℝ) := by positivity
        rw [neg_div]
        have := Real.rpow_neg (x := (A:ℝ)) hA0.le ((d:ℝ)/2)
        rw [this, inv_eq_one_div]
      rw [hsqrt, hneg]
      have hgcnn : 0 ≤ LatticeProb.greenConst d := LatticeProb.greenConst_nonneg d
      have hAd : 0 < (A : ℝ) ^ ((d:ℝ)/2) := by
        have hA0 : (0:ℝ) < (A:ℝ) := by positivity
        exact Real.rpow_pos_of_pos hA0 _
      rw [add_div]
      have hL : 3 ^ d * ((2:ℝ) ^ ((d:ℝ)/2) * LatticeProb.greenConst d * (1 / (A:ℝ) ^ ((d:ℝ)/2)))
          = (3 ^ d * (2:ℝ) ^ ((d:ℝ)/2) * LatticeProb.greenConst d) / (A:ℝ) ^ ((d:ℝ)/2) := by
        field_simp
      rw [hL]
      exact le_add_of_nonneg_right (by positivity)
    calc (walkLaw d 0) {X : ℕ → Site d | exitTime D X > ((n : ℕ) : ℕ∞)}
        ≤ (walkLaw d 0) {X : ℕ → Site d | X n ∈ (boxFinset (0 : Site d) r)} := hle1
      _ = ENNReal.ofReal ((walkLaw d 0).real {X : ℕ → Site d | X n ∈ (boxFinset (0 : Site d) r)}) := hmeas2
      _ = ENNReal.ofReal (∑ y ∈ boxFinset (0 : Site d) r, heatKernel d n 0 y) := by rw [hreal]
      _ ≤ ENNReal.ofReal ((3:ℝ) ^ d * (Real.sqrt 2 ^ d * LatticeProb.greenConst d *
          (A : ℝ) ^ (-(d : ℝ) / 2))) := hle2
      _ ≤ ENNReal.ofReal (((3:ℝ) ^ d * (2:ℝ) ^ ((d:ℝ)/2) * LatticeProb.greenConst d + 1) /
          (A : ℝ) ^ ((d : ℝ) / 2)) := hle3

end Sandpile
