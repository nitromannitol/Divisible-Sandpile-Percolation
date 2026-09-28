import Sandpile.Support.Dgt4ABandLaw

/-!
# Band-mixture weight estimates

The band-mixture weights in Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5946-5947,5967-5970,6018-6030`). Exponential moments are summable
(`BandParameters.summable_weight_exp`), and the mass and first moment of later bands are
negligible compared with the current band (`BandParameters.weight_tail_ratio_tendsto`,
`BandParameters.level_weight_tail_ratio_tendsto`). Every series used in the bounds is summable.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

/-- Every band level is positive. -/
theorem BandParameters.level_pos (P : BandParameters) (k : ℕ) : 0 < P.level k :=
  pow_pos (zero_lt_one.trans P.hA) k

/-- Every component of the mixture has strictly positive weight. -/
theorem BandParameters.weight_pos (P : BandParameters) (k : ℕ) : 0 < P.weight k :=
  mul_pos P.hc0 (Real.exp_pos _)

/-- Band levels diverge. -/
theorem BandParameters.level_tendsto (P : BandParameters) :
    Tendsto P.level atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt P.hA

/-- Exponential decay at the band levels is summable at every positive rate. -/
theorem BandParameters.summable_exp_neg_level (P : BandParameters)
    (c : ℝ) (hc : 0 < c) :
    Summable (fun k => Real.exp (-(c * P.level k))) := by
  have hgeom : Summable (fun k : ℕ => Real.exp ((k : ℝ) * (-(c * (P.A - 1))))) :=
    Real.summable_exp_nat_mul_iff.mpr (by nlinarith [P.hA])
  refine hgeom.of_nonneg_of_le (fun _ => Real.exp_nonneg _) (fun k => ?_)
  apply Real.exp_le_exp.mpr
  have hb := one_add_mul_le_pow (by linarith [P.hA] : -2 ≤ P.A - 1) k
  rw [show 1 + (P.A - 1) = P.A by ring] at hb
  dsimp [BandParameters.level]
  nlinarith

/-- The weighted exponential moments of the band mixture are summable below
rate one. -/
theorem BandParameters.summable_weight_exp (P : BandParameters)
    (θ : ℝ) (hθ : θ < 1) :
    Summable (fun k => P.weight k * Real.exp (θ * P.level k)) := by
  have hs := (P.summable_exp_neg_level (1 - θ) (by linarith)).mul_left P.c0
  refine hs.congr fun k => ?_
  rw [BandParameters.weight, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The band mixture has finite total weight. -/
theorem BandParameters.summable_weight (P : BandParameters) : Summable P.weight := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using P.summable_weight_exp 0 (by norm_num)

/-- Exponential decay of the weights dominates a geometric decay in the
number of bands. -/
theorem BandParameters.weight_add_le (P : BandParameters) (k j : ℕ) :
    P.weight (k + j) ≤ P.weight k * Real.exp (-(P.A - 1)) ^ j := by
  have hA : 0 < P.A := zero_lt_one.trans P.hA
  have hb := one_add_mul_le_pow (by linarith [P.hA] : -2 ≤ P.A - 1) j
  rw [show 1 + (P.A - 1) = P.A by ring] at hb
  have hk : 1 ≤ P.A ^ k := one_le_pow₀ P.hA.le
  have hmul := mul_le_mul_of_nonneg_left hb (pow_nonneg hA.le k)
  have hj : 0 ≤ (j : ℝ) * (P.A - 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith [P.hA])
  have he : P.A ^ k + (j : ℝ) * (P.A - 1) ≤ P.A ^ (k + j) := by
    rw [pow_add P.A k j]
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hj]
  rw [BandParameters.weight, BandParameters.weight, mul_assoc, ← Real.exp_nat_mul,
    ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ P.hc0.le
  apply Real.exp_le_exp.mpr
  dsimp [BandParameters.level]
  linarith

/-- The sum of all later component weights is bounded by a fixed multiple of
the first later weight. -/
theorem BandParameters.weight_tail_le (P : BandParameters) (k : ℕ) :
    (∑' j : ℕ, P.weight (k + 1 + j)) ≤
      P.weight (k + 1) * (1 - Real.exp (-(P.A - 1)))⁻¹ := by
  have hgeom : Summable (fun j : ℕ => Real.exp (-(P.A - 1)) ^ j) :=
    summable_geometric_of_lt_one (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith [P.hA]))
  have htail : Summable (fun j : ℕ => P.weight (k + 1 + j)) :=
    P.summable_weight.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  calc
    (∑' j : ℕ, P.weight (k + 1 + j)) ≤
        ∑' j : ℕ, P.weight (k + 1) * Real.exp (-(P.A - 1)) ^ j := by
      apply Summable.tsum_le_tsum _ htail (hgeom.mul_left _)
      exact P.weight_add_le (k + 1)
    _ = P.weight (k + 1) * (1 - Real.exp (-(P.A - 1)))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_nonneg _)
        (Real.exp_lt_one_iff.mpr (by linarith [P.hA]))]

/-- The next band's weight is negligible compared with the current band's. -/
theorem BandParameters.weight_succ_ratio_tendsto (P : BandParameters) :
    Tendsto (fun k => P.weight (k + 1) / P.weight k) atTop (𝓝 0) := by
  have ht := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (P.level_tendsto.const_mul_atTop (by linarith [P.hA] : 0 < P.A - 1)))
  convert ht using 1
  funext k
  rw [BandParameters.weight, BandParameters.weight, mul_div_mul_left _ _ P.hc0.ne',
    ← Real.exp_sub]
  congr 1
  dsimp [BandParameters.level]
  rw [pow_succ]
  ring

/-- The later mixture components have mass `o(ω_k)`. -/
theorem BandParameters.weight_tail_ratio_tendsto (P : BandParameters) :
    Tendsto (fun k => (∑' j : ℕ, P.weight (k + 1 + j)) / P.weight k) atTop (𝓝 0) := by
  have ht := P.weight_succ_ratio_tendsto.mul_const (1 - Real.exp (-(P.A - 1)))⁻¹
  simp only [zero_mul] at ht
  apply squeeze_zero (fun k => div_nonneg (tsum_nonneg fun j => (P.weight_pos _).le)
    (P.weight_pos k).le) _ ht
  intro k
  have hb := div_le_div_of_nonneg_right (P.weight_tail_le k) (P.weight_pos k).le
  exact hb.trans_eq (by ring)

/-- The geometric bound for the first moments has ratio strictly less than one. -/
theorem BandParameters.level_weight_ratio_lt_one (P : BandParameters) :
    P.A * Real.exp (-(P.A - 1)) < 1 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  simpa only [sub_add_cancel] using Real.add_one_lt_exp (sub_pos.mpr P.hA).ne'

/-- A geometric bound for the first moments of the mixture components. -/
theorem BandParameters.level_weight_add_le (P : BandParameters) (k j : ℕ) :
    P.level (k + j) * P.weight (k + j) ≤
      (P.level k * P.weight k) * (P.A * Real.exp (-(P.A - 1))) ^ j := by
  have h := mul_le_mul_of_nonneg_left (P.weight_add_le k j) (P.level_pos (k + j)).le
  refine h.trans_eq ?_
  simp only [BandParameters.level, pow_add, mul_pow]
  ring

/-- The first moment of the band mixture is finite. -/
theorem BandParameters.summable_level_weight (P : BandParameters) :
    Summable (fun k => P.level k * P.weight k) := by
  have hgeom := summable_geometric_of_lt_one
    (mul_nonneg (zero_lt_one.trans P.hA).le (Real.exp_nonneg (-(P.A - 1))))
    P.level_weight_ratio_lt_one
  refine (hgeom.mul_left (P.level 0 * P.weight 0)).of_nonneg_of_le
    (fun k => mul_nonneg (P.level_pos k).le (P.weight_pos k).le) (fun k => ?_)
  simpa only [zero_add] using P.level_weight_add_le 0 k

/-- The first moment in all later components is bounded by a fixed multiple of
the first later component's first moment. -/
theorem BandParameters.level_weight_tail_le (P : BandParameters) (k : ℕ) :
    (∑' j : ℕ, P.level (k + 1 + j) * P.weight (k + 1 + j)) ≤
      (P.level (k + 1) * P.weight (k + 1)) *
        (1 - P.A * Real.exp (-(P.A - 1)))⁻¹ := by
  have hnonneg := mul_nonneg (zero_lt_one.trans P.hA).le (Real.exp_nonneg (-(P.A - 1)))
  have hgeom := summable_geometric_of_lt_one hnonneg P.level_weight_ratio_lt_one
  have htail := P.summable_level_weight.comp_injective
    (show Function.Injective (fun j : ℕ => k + 1 + j) from fun _ _ h => Nat.add_left_cancel h)
  calc
    _ ≤ ∑' j : ℕ, (P.level (k + 1) * P.weight (k + 1)) *
        (P.A * Real.exp (-(P.A - 1))) ^ j :=
      Summable.tsum_le_tsum (P.level_weight_add_le (k + 1)) htail (hgeom.mul_left _)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hnonneg P.level_weight_ratio_lt_one]

/-- Later components have first moment `o(a_k ω_k)`. -/
theorem BandParameters.level_weight_tail_ratio_tendsto (P : BandParameters) :
    Tendsto (fun k =>
      (∑' j : ℕ, P.level (k + 1 + j) * P.weight (k + 1 + j)) /
        (P.level k * P.weight k)) atTop (𝓝 0) := by
  have ht := (P.weight_succ_ratio_tendsto.const_mul P.A).mul_const
    (1 - P.A * Real.exp (-(P.A - 1)))⁻¹
  simp only [mul_zero, zero_mul] at ht
  apply squeeze_zero (fun k => div_nonneg
    (tsum_nonneg fun j => mul_nonneg (P.level_pos _).le (P.weight_pos _).le)
    (mul_nonneg (P.level_pos k).le (P.weight_pos k).le)) _ ht
  intro k
  have hb := div_le_div_of_nonneg_right (P.level_weight_tail_le k)
    (mul_nonneg (P.level_pos k).le (P.weight_pos k).le)
  refine hb.trans_eq ?_
  have he : P.level (k + 1) = P.level k * P.A := pow_succ _ _
  rw [he]
  field_simp [(P.level_pos k).ne', (P.weight_pos k).ne']

end Sandpile.Support
