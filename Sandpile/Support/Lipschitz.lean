/-
How the odometer depends on the scenery.

`sandpile.tex` uses two facts about that dependence throughout, in
`prop:finite-time-concentration-scale` and wherever a concentration inequality is
applied: the odometer is a convex function of the scenery, and it is Lipschitz in
the scenery with coefficients at most the finite-time Green kernel,

  `|u_t(x; ζ) - u_t(x; η)| ≤ ∑_y g_t(x,y) |ζ(y) - η(y)|`.

Both are proved here by induction on the recursion, with no optimal-stopping
representation needed.  The Green kernel is finitely supported, so every sum is
summable whatever the sceneries.  The `ℓ²` form the paper states follows by
Cauchy-Schwarz, and the single-coordinate form is the resampling bound every
application of `lem:weighted-exp-conc` needs.
-/
import Sandpile.Support.Membrane

namespace Sandpile

variable {d : ℕ}

/-- The odometer is Lipschitz in the scenery with the Green kernel as
coefficients. -/
theorem abs_odometerOf_sub_le (ζ η : Site d → ℝ) :
    ∀ (t : ℕ) (x : Site d), |odometerOf ζ t x - odometerOf η t x|
      ≤ ∑' z : Site d, greenTime d t x z * |ζ z - η z| := by
  intro t
  induction t with
  | zero =>
      intro x
      simp [odometerOf, greenTime, LatticeProb.greenTime]
  | succ n ih =>
      intro x
      have hsum : ∀ w : Site d,
          Summable fun z : Site d => greenTime d n w z * |ζ z - η z| :=
        fun w => summable_greenTime_mul n w _
      have hstep : |odometerOf ζ (n + 1) x - odometerOf η (n + 1) x|
          ≤ |ζ x - η x| + avg (fun y => |odometerOf ζ n y - odometerOf η n y|) x := by
        have hmax : |max 0 (ζ x + avg (odometerOf ζ n) x)
              - max 0 (η x + avg (odometerOf η n) x)|
            ≤ |(ζ x + avg (odometerOf ζ n) x) - (η x + avg (odometerOf η n) x)| := by
          rw [max_comm 0 (ζ x + avg (odometerOf ζ n) x),
            max_comm 0 (η x + avg (odometerOf η n) x)]
          exact abs_max_sub_max_le_abs _ _ _
        refine le_trans hmax ?_
        have hsplit : |(ζ x + avg (odometerOf ζ n) x) - (η x + avg (odometerOf η n) x)|
            ≤ |ζ x - η x| + |avg (odometerOf ζ n) x - avg (odometerOf η n) x| := by
          have : (ζ x + avg (odometerOf ζ n) x) - (η x + avg (odometerOf η n) x)
              = (ζ x - η x) + (avg (odometerOf ζ n) x - avg (odometerOf η n) x) := by ring
          rw [this]
          exact abs_add_le _ _
        refine le_trans hsplit (add_le_add le_rfl ?_)
        unfold avg LatticeProb.walkOp nbrSum
        rw [← sub_div, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (d:ℝ))]
        refine div_le_div_of_nonneg_right ?_ ?_
        · rw [← Finset.sum_sub_distrib]
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
          have : odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)
              - (odometerOf η n (x + unit i) + odometerOf η n (x - unit i))
              = (odometerOf ζ n (x + unit i) - odometerOf η n (x + unit i))
                + (odometerOf ζ n (x - unit i) - odometerOf η n (x - unit i)) := by ring
          rw [this]
          exact abs_add_le _ _
        · positivity
      refine le_trans hstep ?_
      have hIH : avg (fun y => |odometerOf ζ n y - odometerOf η n y|) x
          ≤ avg (fun y => ∑' z : Site d, greenTime d n y z * |ζ z - η z|) x := by
        unfold avg LatticeProb.walkOp nbrSum
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ =>
          add_le_add (ih _) (ih _)) (by positivity)
      refine le_trans (add_le_add (le_refl |ζ x - η x|) hIH) ?_
      have hinner : ∀ z : Site d,
            ((∑ i : Fin d, (greenTime d n (x + unit i) z + greenTime d n (x - unit i) z))
              / (2 * (d : ℝ))) * |ζ z - η z|
            = (∑ i : Fin d, (greenTime d n (x + unit i) z * |ζ z - η z|
                + greenTime d n (x - unit i) z * |ζ z - η z|)) / (2 * (d : ℝ)) := by
        intro z
        rw [div_mul_eq_mul_div, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      have hswap : avg (fun y => ∑' z : Site d, greenTime d n y z * |ζ z - η z|) x
          = ∑' z : Site d,
            ((∑ i : Fin d, (greenTime d n (x + unit i) z + greenTime d n (x - unit i) z))
              / (2 * (d : ℝ))) * |ζ z - η z| := by
        rw [tsum_congr hinner, tsum_div_const]
        unfold avg LatticeProb.walkOp nbrSum
        congr 1
        rw [Summable.tsum_finsetSum (fun i _ => (hsum (x + unit i)).add (hsum (x - unit i)))]
        exact Finset.sum_congr rfl fun i _ =>
          (Summable.tsum_add (hsum (x + unit i)) (hsum (x - unit i))).symm
      rw [hswap]
      have hz : ∀ z : Site d, |ζ x - η x| * (if x = z then (1:ℝ) else 0)
          + ((∑ i : Fin d, (greenTime d n (x + unit i) z + greenTime d n (x - unit i) z))
              / (2 * (d : ℝ))) * |ζ z - η z|
          = greenTime d (n + 1) x z * |ζ z - η z| := by
        intro z
        rw [greenTime_succ_avg, add_mul]
        congr 1
        by_cases h : x = z
        · subst h; simp [heatKernel, LatticeProb.LocalCLT.heatKernel]
        · simp [heatKernel, LatticeProb.LocalCLT.heatKernel, h]
      have hone : |ζ x - η x|
          = ∑' z : Site d, |ζ x - η x| * (if x = z then (1:ℝ) else 0) := by
        rw [tsum_eq_single x] <;> simp +contextual [eq_comm]
      rw [hone, ← Summable.tsum_add ?_ ?_]
      · exact le_of_eq (tsum_congr hz)
      · exact (summable_heatKernel_zero_mul x fun z => |ζ z - η z|).congr
          (fun z => by by_cases h : x = z <;>
            simp [heatKernel, LatticeProb.LocalCLT.heatKernel, h, mul_comm])
      · have hs2 : Summable fun z : Site d =>
            (∑ i : Fin d, (greenTime d n (x + unit i) z * |ζ z - η z|
              + greenTime d n (x - unit i) z * |ζ z - η z|)) / (2 * (d : ℝ)) :=
          Summable.div_const (summable_finsetSum _ fun i _ =>
            (hsum (x + unit i)).add (hsum (x - unit i))) _
        exact hs2.congr fun z => (hinner z).symm

/-- The resampling bound: changing the scenery at one site changes the odometer
by at most the Green kernel there times the change.  This is the coefficient
bound every application of `lem:weighted-exp-conc` in the paper uses. -/
theorem abs_odometerOf_update_le (ζ : Site d → ℝ) (y : Site d) (v : ℝ) (t : ℕ)
    (x : Site d) :
    |odometerOf ζ t x - odometerOf (Function.update ζ y v) t x|
      ≤ greenTime d t x y * |ζ y - v| := by
  classical
  refine le_trans (abs_odometerOf_sub_le ζ (Function.update ζ y v) t x) ?_
  refine le_of_eq ?_
  rw [tsum_eq_single y]
  · rw [Function.update_self]
  · intro z hz
    rw [Function.update_of_ne hz]
    simp

/-- The odometer is a convex function of the scenery. -/
theorem odometerOf_convex (t : ℕ) :
    ∀ (x : Site d) (ζ η : Site d → ℝ) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      odometerOf (fun z => a * ζ z + b * η z) t x
        ≤ a * odometerOf ζ t x + b * odometerOf η t x := by
  induction t with
  | zero => intro x ζ η a b _ _ _; simp [odometerOf]
  | succ n ih =>
      intro x ζ η a b ha hb hab
      have havg : avg (odometerOf (fun z => a * ζ z + b * η z) n) x
          ≤ a * avg (odometerOf ζ n) x + b * avg (odometerOf η n) x := by
        unfold avg LatticeProb.walkOp nbrSum
        rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := ih (x + unit i) ζ η a b ha hb hab
        have h2 := ih (x - unit i) ζ η a b ha hb hab
        linarith
      have hmax : ∀ p q : ℝ, max 0 (a * p + b * q) ≤ a * max 0 p + b * max 0 q := by
        intro p q
        refine max_le (by positivity) ?_
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right 0 p) ha)
          (mul_le_mul_of_nonneg_left (le_max_right 0 q) hb)
      show max 0 ((fun z => a * ζ z + b * η z) x
        + avg (odometerOf (fun z => a * ζ z + b * η z) n) x) ≤ _
      refine le_trans (max_le_max (le_refl (0:ℝ)) (by
        have : (fun z => a * ζ z + b * η z) x
            + avg (odometerOf (fun z => a * ζ z + b * η z) n) x
          ≤ a * (ζ x + avg (odometerOf ζ n) x) + b * (η x + avg (odometerOf η n) x) := by
          simp only []
          nlinarith [havg]
        exact this)) ?_
      exact hmax _ _

/-- Clause one of `prop:finite-time-concentration-scale`: the odometer is a
convex function of the scenery on the whole space, in Mathlib's `ConvexOn`
form. -/
theorem odometerOf_convexOn (t : ℕ) (x : Site d) :
    ConvexOn ℝ (Set.univ : Set (Site d → ℝ)) fun ζ => odometerOf ζ t x := by
  refine ⟨convex_univ, ?_⟩
  intro ζ _ η _ a b ha hb hab
  exact odometerOf_convex t x ζ η a b ha hb hab

/-- Cauchy-Schwarz for a finitely supported nonnegative vector against a square
summable one.  This is the shape clause two of
`prop:finite-time-concentration-scale` needs, since the Green coefficients
vanish outside a finite box. -/
theorem tsum_mul_le_sqrt_mul_sqrt {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hfs : ∀ i, i ∉ s → f i = 0)
    (hg : Summable fun i => g i ^ 2) :
    ∑' i, f i * |g i| ≤ Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
  classical
  have hfin : ∀ i, i ∉ s → f i * |g i| = 0 := fun i hi => by rw [hfs i hi, zero_mul]
  have hfin2 : ∀ i, i ∉ s → f i ^ 2 = 0 := fun i hi => by rw [hfs i hi]; ring
  have h1 : ∑' i, f i * |g i| = ∑ i ∈ s, f i * |g i| := tsum_eq_sum hfin
  have h2 : ∑' i, f i ^ 2 = ∑ i ∈ s, f i ^ 2 := tsum_eq_sum hfin2
  have hCS : (∑ i ∈ s, f i * |g i|) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, |g i| ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s f fun i => |g i|
  have hgle : ∑ i ∈ s, |g i| ^ 2 ≤ ∑' i, g i ^ 2 := by
    have hEq : ∀ i ∈ s, |g i| ^ 2 = g i ^ 2 := fun i _ => sq_abs (g i)
    rw [Finset.sum_congr rfl hEq]
    exact Summable.sum_le_tsum s (fun i _ => sq_nonneg _) hg
  have hf2nn : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hg2nn : 0 ≤ ∑' i, g i ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hsnn : 0 ≤ ∑ i ∈ s, f i * |g i| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hf0 i) (abs_nonneg _)
  have hkey : (∑ i ∈ s, f i * |g i|) ^ 2
      ≤ (∑ i ∈ s, f i ^ 2) * ∑' i, g i ^ 2 := by
    refine le_trans hCS ?_
    exact mul_le_mul_of_nonneg_left hgle hf2nn
  rw [h1, h2]
  have hprod : 0 ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : (Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2)) ^ 2
      = (∑ i ∈ s, f i ^ 2) * ∑' i, g i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hf2nn, Real.sq_sqrt hg2nn]
  nlinarith [hkey, hsq, hsnn, hprod]

end Sandpile
