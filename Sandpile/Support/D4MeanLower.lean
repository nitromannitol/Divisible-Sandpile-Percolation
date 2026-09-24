/-
The uniform logarithmic lower bound on the mean odometer in dimension four,
from the negative membrane tail and the block increment inequality. The block
length and the number of blocks are both the integer square root of time.
-/
import Sandpile.Support.BlockIncrement
import Sandpile.Support.D4BlockTail
import Mathlib.Data.Nat.Sqrt

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

theorem log_time_le_four_log_sqrt (t : ℕ) (ht : 4 ≤ t) :
    Real.log (t : ℝ) ≤ 4 * Real.log (Nat.sqrt t : ℝ) := by
  have hk : 2 ≤ Nat.sqrt t := Nat.le_sqrt'.mpr (by norm_num; exact ht)
  have hkR : (2 : ℝ) ≤ Nat.sqrt t := by exact_mod_cast hk
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlt : (t : ℝ) < ((Nat.sqrt t : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' t
  have h1 : (Nat.sqrt t : ℝ) + 1 ≤ (Nat.sqrt t : ℝ) ^ 2 := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (Nat.sqrt t : ℝ) + 1) h1 2
  have h4 : (t : ℝ) ≤ (Nat.sqrt t : ℝ) ^ 4 := by nlinarith
  calc Real.log (t : ℝ) ≤ Real.log ((Nat.sqrt t : ℝ) ^ 4) := Real.log_le_log htR h4
    _ = 4 * Real.log (Nat.sqrt t : ℝ) := by rw [Real.log_pow]; norm_num

theorem exists_log_mean_lower_four (hVS : Sandpile.External.VarianceScale)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → (∫ z, z ∂ν = 0) →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν) ≤ K₀ →
        ∀ t : ℕ, t₀ ≤ t →
          c * Real.log t ≤ ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν) := by
  obtain ⟨α, C, δ, hα, hC, hδ, htail⟩ := exists_membrane_negative_tail_four hVS ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨cQ, CQ, hcQ, hCQ, hQs⟩ := hVS.1 4 (by norm_num)
  have hQbounds (k : ℕ) (hk : 2 ≤ k) :
      cQ * Real.log k ≤ (∑' z : Site 4, greenTime 4 k 0 z ^ 2) ∧
        (∑' z : Site 4, greenTime 4 k 0 z ^ 2) ≤ CQ * Real.log k := by
    simpa [Sandpile.External.Variance.varianceRate] using hQs k hk
  set θ := min δ (min 1 (1 / (2 * C * CQ)))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθδ : θ ≤ δ := min_le_left _ _
  have hθ1 : θ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hθC : θ ≤ 1 / (2 * C * CQ) := (min_le_right _ _).trans (min_le_right _ _)
  have hcoef : 2 * C * θ ^ 2 * CQ ≤ 1 := by
    have h1 := (le_div_iff₀ (show 0 < 2 * C * CQ by positivity)).mp hθC
    have h2 : θ ^ 2 ≤ θ := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * C * CQ by positivity)
    nlinarith
  set b := 2 * Real.log 2 / (α * θ ^ 2 * cQ)
  set K := max 2048 ⌈Real.exp b⌉₊
  have hK : 2048 ≤ K := le_max_left _ _
  refine ⟨α * θ * cQ / 24, by positivity, K ^ 2, ?_⟩
  intro ν hprob hmean hvar hexp hνK t ht
  haveI := hprob
  have hint := integrable_id_of_exp_moment ν θ₀ hθ₀ hexp
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  set k := Nat.sqrt t
  have hkK : K ≤ k := Nat.le_sqrt'.mpr ht
  have hk2048 : 2048 ≤ k := hK.trans hkK
  have hk2 : 2 ≤ k := by omega
  have hkR : (2048 : ℝ) ≤ k := by exact_mod_cast hk2048
  have hk0 : (0 : ℝ) < k := by linarith
  set Q := ∑' z : Site 4, greenTime 4 k 0 z ^ 2
  obtain ⟨hQlower, hQupper⟩ := hQbounds k hk2
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos hcQ hlogk) hQlower
  have hbase : b ≤ Real.log (k : ℝ) := by
    have hceil : Real.exp b ≤ (⌈Real.exp b⌉₊ : ℝ) := Nat.le_ceil _
    have hceilK : ⌈Real.exp b⌉₊ ≤ K := le_max_right _ _
    have hceilk : (⌈Real.exp b⌉₊ : ℝ) ≤ k := by exact_mod_cast hceilK.trans hkK
    have h := Real.log_le_log (Real.exp_pos b) (hceil.trans hceilk)
    rwa [Real.log_exp] at h
  have hlarge : 2 * Real.log 2 ≤ α * θ ^ 2 * Q := by
    have h1 := mul_le_mul_of_nonneg_left hbase (show 0 ≤ α * θ ^ 2 * cQ by positivity)
    have hid : α * θ ^ 2 * cQ * b = 2 * Real.log 2 := by dsimp [b]; field_simp
    rw [hid] at h1
    have h2 := mul_le_mul_of_nonneg_left hQlower (show 0 ≤ α * θ ^ 2 by positivity)
    nlinarith
  set h := α * θ * Q / 6
  have hh : 0 < h := by dsimp [h]; positivity
  have htail' : Real.exp (-(C * θ ^ 2 * Q)) / 16 ≤
      (LatticeProb.iidLaw 4 ν).real {ζ | 3 * h < -membrane ζ k 0} := by
    have he : 3 * h = α * θ / 2 * Q := by dsimp [h]; ring
    rw [he]
    exact htail ν hprob hmean hvar hexp hνK θ hθ hθδ k hlarge
  set E := Real.exp (C * θ ^ 2 * Q)
  have hE : 0 < E := Real.exp_pos _
  have hE2 : E ^ 2 ≤ (k : ℝ) + 2 := by
    have hQup : Q ≤ CQ * Real.log ((k : ℝ) + 2) :=
      hQupper.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hk0 (by linarith)) hCQ.le)
    have h1 := mul_le_mul_of_nonneg_left hQup (show 0 ≤ 2 * C * θ ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef
      (Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 2 by linarith))
    calc E ^ 2 = Real.exp (2 * (C * θ ^ 2 * Q)) := by
          dsimp [E]; rw [sq, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (Real.log ((k : ℝ) + 2)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (k : ℝ) + 2 := Real.exp_log (by positivity)
  have h32 : 32 * E ≤ k := by
    have hprod : 0 ≤ ((k : ℝ) - 2048) * (k : ℝ) := mul_nonneg (by linarith) hk0.le
    have hkpoly : 1024 * ((k : ℝ) + 2) ≤ (k : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hcount : 2 ≤ (k : ℝ) * (LatticeProb.iidLaw 4 ν).real {ζ | 3 * h < -membrane ζ k 0} := by
    have h1 : 2 ≤ (k : ℝ) * (Real.exp (-(C * θ ^ 2 * Q)) / 16) := by
      rw [Real.exp_neg]
      change 2 ≤ (k : ℝ) * (E⁻¹ / 16)
      rw [show (k : ℝ) * (E⁻¹ / 16) = (k : ℝ) / (16 * E) by ring,
        le_div_iff₀ (show 0 < 16 * E by positivity)]
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left htail' hk0.le)
  have hblock := mean_ge_of_block_probability (by norm_num) ν hint hmean hpos k k (by omega) hh hcount
  have hkt : k * k ≤ t := Nat.sqrt_le t
  have hmeanmono := meanOdometerOf_mono (d := 4) ν hpos hkt
  have ht4 : 4 ≤ t := by nlinarith
  have hlogt := log_time_le_four_log_sqrt t ht4
  have h1 := mul_le_mul_of_nonneg_left hlogt (show 0 ≤ α * θ * cQ / 24 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hQlower (show 0 ≤ α * θ / 6 by positivity)
  dsimp [h] at hblock
  nlinarith

end Sandpile
