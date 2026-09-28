import Sandpile.External.GreenBoundsHigh
import Sandpile.External.VarianceScaleProved
import LatticeProb.Walk.GreenPointwise

/-!
# The high-dimensional Green estimates are proved

The high-dimensional Green estimates are no longer assumed.

`Sandpile/External/GreenBoundsHigh.lean` states the estimates of
`ssec:green-estimates` as a `Prop`, as a cited result must be stated while it is
only assumed.  The shared library now proves all five displays for the simple
random walk above dimension four, so the `Prop` is discharged here.  The `Prop`
and its name are left untouched, so no frozen statement changes, and every node
carrying `Sandpile.External.GreenBoundsHigh` as a hypothesis becomes
unconditional.

The only content is the identification of this file's vocabulary with the
library's: the two-point Green function is the translation-invariant one, the
Euclidean norm of the notation section is the library's, and the real exponents
`4-d`, `2-d`, `(2-d)/2` and `(4-d)/2` are the natural powers `k+1`, `k+3`,
`k+3` and `k+1` in the square root, where `d = k+5`.
-/

open LatticeProb

namespace Sandpile.External

/-! ### The vocabulary -/

/-- The paper's two-point Green function `Sandpile.green` agrees with the library's
translation-invariant `LatticeProb.srwGreenInf`, via the heat-kernel identification
`Sandpile.heatKernel_eq_srwHeat`. -/
theorem green_eq_srwGreenInf (d : ℕ) (x y : Sandpile.Site d) :
    Sandpile.green d x y = LatticeProb.srwGreenInf d (y - x) :=
  tsum_congr fun k => Sandpile.heatKernel_eq_srwHeat d k x y

/-- The notation section's `latticeNorm` is definitionally the library's `euclidNorm`. -/
theorem latticeNorm_eq_euclidNorm {d : ℕ} (z : Sandpile.Site d) :
    Sandpile.External.latticeNorm z = LatticeProb.euclidNorm z := rfl

/-- A negative natural power of a positive real, written as an `rpow`, is the inverse of the
corresponding natural power. -/
theorem rpow_cast_neg {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

/-- A negative half-integer `rpow` of a positive real is the inverse of the corresponding
natural power of the square root, converting the paper's exponents `(2-d)/2` and `(4-d)/2` into
powers of `Real.sqrt`. -/
theorem rpow_half_neg {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-(n : ℝ) / 2) = (Real.sqrt x ^ n)⁻¹ := by
  rw [neg_div, Real.rpow_neg hx.le]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 2)) n, ← Real.rpow_mul hx.le]
  ring_nf

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- **The `d ≥ 5` Green-function estimates hold**; they are no longer an
assumption. -/
theorem Sandpile.External.greenBoundsHigh : Sandpile.External.GreenBoundsHigh
-- FROZEN-STATEMENT-END
:= by
  intro d hd
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 5 := ⟨d - 5, by omega⟩
  have hGeq : ∀ x y : Sandpile.Site (k + 5),
      Sandpile.green (k + 5) x y = LatticeProb.srwGreenInf (k + 5) (y - x) :=
    green_eq_srwGreenInf (k + 5)
  have hG0 : ∀ z : Sandpile.Site (k + 5),
      Sandpile.green (k + 5) 0 z = LatticeProb.srwGreenInf (k + 5) z := by
    intro z; rw [hGeq, sub_zero]
  have hexp1 : (4 : ℝ) - ((k + 5 : ℕ) : ℝ) = -((k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hexp2 : (2 : ℝ) - ((k + 5 : ℕ) : ℝ) = -((k + 3 : ℕ) : ℝ) := by push_cast; ring
  have hexp3 : ((2 : ℝ) - ((k + 5 : ℕ) : ℝ)) / 2 = -((k + 3 : ℕ) : ℝ) / 2 := by
    rw [hexp2]
  have hexp4 : ((4 : ℝ) - ((k + 5 : ℕ) : ℝ)) / 2 = -((k + 1 : ℕ) : ℝ) / 2 := by
    rw [hexp1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the tail bounds `eq:dgt4-green-tail`
    obtain ⟨C₁, hC₁, htail⟩ := exists_tsum_srwGreenInf_sq_tail_le k
    obtain ⟨C₂, hC₂, hsup⟩ := exists_srwGreenInf_sup_tail_le k
    refine ⟨C₁ + C₂, by linarith, fun r hr => ?_⟩
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    obtain ⟨hs, hb⟩ := htail r hr
    refine ⟨?_, ?_, ?_⟩
    · exact hs.congr fun z => by rw [hG0]
    · rw [hexp1, rpow_cast_neg hrpos]
      have hc : (∑' z : {z : Sandpile.Site (k + 5) //
            (r : ℝ) ≤ Sandpile.External.latticeNorm z},
              Sandpile.green (k + 5) 0 (z : Sandpile.Site (k + 5)) ^ 2)
          = ∑' z : {z : LatticeProb.Site (k + 5) // (r : ℝ) ≤ LatticeProb.euclidNorm z},
              LatticeProb.srwGreenInf (k + 5) (z : LatticeProb.Site (k + 5)) ^ 2 :=
        tsum_congr fun z => by rw [hG0]
      rw [hc]
      have hle : (0 : ℝ) ≤ C₂ := hC₂.le
      have hpos : (0 : ℝ) < (r : ℝ) ^ (k + 1) := by positivity
      rw [inv_eq_one_div, mul_one_div]
      have : C₁ / (r : ℝ) ^ (k + 1) ≤ (C₁ + C₂) / (r : ℝ) ^ (k + 1) := by
        gcongr
        linarith
      linarith [hb]
    · intro z hz
      rw [hexp2, rpow_cast_neg hrpos, hG0]
      have := hsup r hr z hz
      have hpos : (0 : ℝ) < (r : ℝ) ^ (k + 3) := by positivity
      rw [inv_eq_one_div, mul_one_div]
      have h2 : C₂ / (r : ℝ) ^ (k + 3) ≤ (C₁ + C₂) / (r : ℝ) ^ (k + 3) := by
        gcongr
        linarith
      linarith
  · -- square summability `eq:dgt4-green-l2`
    exact (summable_srwGreenInf_sq k).congr fun z => by rw [hG0]
  · -- the time-tail kernel bounds `eq:dgt4-tail-kernel`
    obtain ⟨C₁, hC₁, htail⟩ := exists_srwTimeTail_le k
    obtain ⟨C₂, hC₂, hsq⟩ := exists_tsum_srwTimeTail_sq_le k
    have hTeq : ∀ (m : ℕ) (y : Sandpile.Site (k + 5)),
        Sandpile.External.tailKernel (k + 5) m y
          = LatticeProb.srwTimeTail (k + 5) m y := by
      intro m y
      exact tsum_congr fun j => by
        rw [Sandpile.heatKernel_eq_srwHeat (k + 5) (j : ℕ) 0 y, sub_zero]
    refine ⟨C₁ + C₂, by linarith, fun m hm => ?_⟩
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
    refine ⟨fun y => ⟨?_, ?_⟩, ?_, ?_⟩
    · exact (LatticeProb.summable_subtype_ge (m := m)
        (LatticeProb.summable_srwHeat (by omega) y)).congr fun j => by
          rw [Sandpile.heatKernel_eq_srwHeat (k + 5) (j : ℕ) 0 y, sub_zero]
    · rw [hexp3, rpow_half_neg hmpos, hTeq]
      have h := htail m hm y
      have hpos : (0 : ℝ) < Real.sqrt (m : ℝ) ^ (k + 3) := by positivity
      rw [inv_eq_one_div, mul_one_div]
      have h2 : C₁ / Real.sqrt (m : ℝ) ^ (k + 3)
          ≤ (C₁ + C₂) / Real.sqrt (m : ℝ) ^ (k + 3) := by
        gcongr
        linarith
      linarith
    · exact (hsq m hm).1.congr fun y => by rw [hTeq]
    · rw [hexp4, rpow_half_neg hmpos]
      have hc : (∑' y : Sandpile.Site (k + 5),
            Sandpile.External.tailKernel (k + 5) m y ^ 2)
          = ∑' y : LatticeProb.Site (k + 5), LatticeProb.srwTimeTail (k + 5) m y ^ 2 :=
        tsum_congr fun y => by rw [hTeq]
      rw [hc]
      have h := (hsq m hm).2
      have hpos : (0 : ℝ) < Real.sqrt (m : ℝ) ^ (k + 1) := by positivity
      rw [inv_eq_one_div, mul_one_div]
      have h2 : C₂ / Real.sqrt (m : ℝ) ^ (k + 1)
          ≤ (C₁ + C₂) / Real.sqrt (m : ℝ) ^ (k + 1) := by
        gcongr
        linarith
      linarith
  · -- the first intersection estimate `eq:dgt4-intersection-first-moment`
    obtain ⟨C, hC, hH⟩ := exists_tsum_srwGreenInf_mul_le k
    refine ⟨C, hC, fun x y => ?_⟩
    obtain ⟨hs, hb⟩ := hH (x - y)
    have hfun : ∀ a : LatticeProb.Site (k + 5),
        LatticeProb.srwGreenInf (k + 5) a
            * LatticeProb.srwGreenInf (k + 5) (a + (x - y))
          = Sandpile.green (k + 5) x (a + x) * Sandpile.green (k + 5) y (a + x) := by
      intro a
      rw [hGeq x (a + x), hGeq y (a + x),
        show a + x - x = a from by abel, show a + x - y = a + (x - y) from by abel]
    have hE : (0 : ℝ) < 1 + Sandpile.External.latticeNorm (x - y) := by
      have := LatticeProb.euclidNorm_nonneg (x - y)
      rw [latticeNorm_eq_euclidNorm]
      linarith
    have hcmp : (1 : ℝ) + Sandpile.External.latticeNorm (x - y)
        ≤ 1 + ((LatticeProb.graphNorm (x - y) : ℕ) : ℝ) := by
      rw [latticeNorm_eq_euclidNorm]
      linarith [LatticeProb.euclidNorm_le_graphNorm (x - y)]
    constructor
    · refine ((Equiv.addRight x).summable_iff
        (f := fun z : LatticeProb.Site (k + 5) =>
          Sandpile.green (k + 5) x z * Sandpile.green (k + 5) y z)).mp ?_
      exact hs.congr fun a => hfun a
    · have heq : (∑' z : Sandpile.Site (k + 5),
            Sandpile.green (k + 5) x z * Sandpile.green (k + 5) y z)
          = ∑' a : LatticeProb.Site (k + 5),
              LatticeProb.srwGreenInf (k + 5) a
                * LatticeProb.srwGreenInf (k + 5) (a + (x - y)) := by
        rw [← (Equiv.addRight x).tsum_eq (fun z : LatticeProb.Site (k + 5) =>
          Sandpile.green (k + 5) x z * Sandpile.green (k + 5) y z)]
        exact tsum_congr fun a => (hfun a).symm
      rw [heq, hexp1, rpow_cast_neg hE, inv_eq_one_div, mul_one_div]
      refine hb.trans ?_
      gcongr
  · -- the crossed-ordering estimate `eq:dgt4-intersection-second-moment`
    obtain ⟨C, hC, hX⟩ := exists_tsum_srwGreenInf_crossed_le k
    refine ⟨C * Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1), by positivity, fun x y => ?_⟩
    obtain ⟨hs, hb⟩ := hX (y - x)
    have hfun : ∀ q : LatticeProb.Site (k + 5) × LatticeProb.Site (k + 5),
        LatticeProb.srwGreenInf (k + 5) q.1
            * LatticeProb.srwGreenInf (k + 5) (q.2 - q.1) ^ 2
            * LatticeProb.srwGreenInf (k + 5) (q.2 - (y - x))
          = Sandpile.green (k + 5) x (q.1 + x)
            * Sandpile.green (k + 5) (q.1 + x) (q.2 + x) ^ 2
            * Sandpile.green (k + 5) y (q.2 + x) := by
      intro q
      rw [hGeq x (q.1 + x), hGeq (q.1 + x) (q.2 + x), hGeq y (q.2 + x),
        show q.1 + x - x = q.1 from by abel,
        show q.2 + x - (q.1 + x) = q.2 - q.1 from by abel,
        show q.2 + x - y = q.2 - (y - x) from by abel]
    have hsN : (0 : ℝ) < Real.sqrt ((k + 5 : ℕ) : ℝ) := by
      refine Real.sqrt_pos.mpr ?_
      positivity
    have hE : (0 : ℝ) < 1 + Sandpile.External.latticeNorm (x - y) := by
      have := LatticeProb.euclidNorm_nonneg (x - y)
      rw [latticeNorm_eq_euclidNorm]
      linarith
    have hcmp : (1 : ℝ) + Sandpile.External.latticeNorm (x - y)
        ≤ Real.sqrt ((k + 5 : ℕ) : ℝ)
          * (1 + ((LatticeProb.supNorm (y - x) : ℕ) : ℝ)) := by
      rw [latticeNorm_eq_euclidNorm]
      have h1 : LatticeProb.euclidNorm (x - y) = LatticeProb.euclidNorm (y - x) := by
        unfold LatticeProb.euclidNorm
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have : ((x - y : LatticeProb.Site (k + 5)) i : ℤ)
            = -((y - x : LatticeProb.Site (k + 5)) i : ℤ) := by
          simp [Pi.sub_apply]
        rw [this]
        push_cast
        ring
      rw [h1]
      have h2 := LatticeProb.euclidNorm_le_sqrt_mul_supNorm (y - x)
      have h3 : (1 : ℝ) ≤ Real.sqrt ((k + 5 : ℕ) : ℝ) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        refine Real.sqrt_le_sqrt ?_
        push_cast
        linarith
      nlinarith [LatticeProb.euclidNorm_nonneg (y - x),
        (Nat.cast_nonneg (LatticeProb.supNorm (y - x)) : (0:ℝ) ≤ _)]
    constructor
    · refine (((Equiv.addRight x).prodCongr (Equiv.addRight x)).summable_iff
        (f := fun p : LatticeProb.Site (k + 5) × LatticeProb.Site (k + 5) =>
          Sandpile.green (k + 5) x p.1 * Sandpile.green (k + 5) p.1 p.2 ^ 2
            * Sandpile.green (k + 5) y p.2)).mp ?_
      exact hs.congr fun q => hfun q
    · have heq : (∑' p : Sandpile.Site (k + 5) × Sandpile.Site (k + 5),
            Sandpile.green (k + 5) x p.1 * Sandpile.green (k + 5) p.1 p.2 ^ 2
              * Sandpile.green (k + 5) y p.2)
          = ∑' q : LatticeProb.Site (k + 5) × LatticeProb.Site (k + 5),
              LatticeProb.srwGreenInf (k + 5) q.1
                * LatticeProb.srwGreenInf (k + 5) (q.2 - q.1) ^ 2
                * LatticeProb.srwGreenInf (k + 5) (q.2 - (y - x)) := by
        rw [← ((Equiv.addRight x).prodCongr (Equiv.addRight x)).tsum_eq
          (fun p : LatticeProb.Site (k + 5) × LatticeProb.Site (k + 5) =>
            Sandpile.green (k + 5) x p.1 * Sandpile.green (k + 5) p.1 p.2 ^ 2
              * Sandpile.green (k + 5) y p.2)]
        exact tsum_congr fun q => (hfun q).symm
      rw [heq, hexp1, rpow_cast_neg hE, inv_eq_one_div, mul_one_div]
      refine hb.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpow : (1 + Sandpile.External.latticeNorm (x - y)) ^ (k + 1)
          ≤ Real.sqrt ((k + 5 : ℕ) : ℝ) ^ (k + 1)
            * (1 + ((LatticeProb.supNorm (y - x) : ℕ) : ℝ)) ^ (k + 1) := by
        have := pow_le_pow_left₀ (by linarith) hcmp (k + 1)
        rwa [mul_pow] at this
      nlinarith [hC.le, hpow,
        (by positivity : (0:ℝ) < (1 + ((LatticeProb.supNorm (y - x) : ℕ) : ℝ)) ^ (k + 1))]
