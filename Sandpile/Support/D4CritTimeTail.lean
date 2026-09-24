/-
Step 2 of the dimension-four critical-level percolation proof
(`sandpile.tex:4028-4046`): the infinite-time ball Green field is replaced by
its finite-time version.  The coefficient vector of the difference is the
finite-time tail `q_{r,A}` of `eq:d4ball-time-tail`, whose maximum is `C r^{-2}`
and whose square sum is `C`, so the weighted exponential concentration of
`lem:weighted-exp-conc` gives a `C exp(-c min(s², s r²))` deviation bound,
uniformly in the site and in the horizon.
-/
import Sandpile.Support.TwoScaleTail
import Sandpile.Support.NearKernel
import Sandpile.Frozen.D4FiniteRangeLowerBound

open MeasureTheory

noncomputable section
namespace Sandpile

lemma notMem_box_of_notMem_boxFinset (r : ℕ) {u : Site 4} (hu : u ∉ boxFinset 0 r) :
    u ∉ External.BallGreen.box r := by
  intro hb
  apply hu
  apply mem_boxFinset
  apply Finset.sup_le
  intro i _
  simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using hb i

lemma frCube_eq_ballCube (x : Site 4) (L : ℝ) : frCube x L = ballCube x L := rfl

lemma floor_natCast_mul_sq (Aex r : ℕ) : ⌊(Aex : ℝ) * (r : ℝ) ^ 2⌋₊ = Aex * r ^ 2 := by
  rw [show (Aex : ℝ) * (r : ℝ) ^ 2 = ((Aex * r ^ 2 : ℕ) : ℝ) by push_cast; ring,
    Nat.floor_natCast]

lemma timeTail_eq_zero_of_notMem_boxFinset (r : ℕ) (A : ℝ) {u : Site 4}
    (hu : u ∉ boxFinset 0 r) : External.BallGreen.timeTail r A u = 0 := by
  unfold External.BallGreen.timeTail
  rw [killedGreen_box_eq_zero_of_notMem_boxFinset r hu,
    killedGreenTime_eq_zero_of_target_notMem _ (notMem_box_of_notMem_boxFinset r hu), sub_zero]

/-- The difference between the ball Green field and its finite-time version is
the field of the finite-time tail `q_{r,A}`. -/
lemma ballGreenField_sub_frGreenFieldTime (Aex r : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) :
    ballGreenField r ζ z - frGreenFieldTime r (Aex * r ^ 2) ζ z
      = finiteKernelField (External.BallGreen.timeTail r (Aex : ℝ)) ζ z := by
  have h1 : ballGreenField r ζ z
      = ∑ u ∈ boxFinset 0 r, killedGreen (External.BallGreen.box r) 0 u * ζ (z + u) := by
    rw [ballGreenField, ballCube_zero_eq_box]
    exact tsum_eq_sum fun u hu => by
      rw [killedGreen_box_eq_zero_of_notMem_boxFinset r hu, zero_mul]
  have h2 : frGreenFieldTime r (Aex * r ^ 2) ζ z
      = ∑ u ∈ boxFinset 0 r,
          killedGreenTime (External.BallGreen.box r) (Aex * r ^ 2) 0 u * ζ (z + u) := by
    rw [frGreenFieldTime, frCube_eq_ballCube, ballCube_zero_eq_box]
    exact tsum_eq_sum fun u hu => by
      rw [killedGreenTime_eq_zero_of_target_notMem _ (notMem_box_of_notMem_boxFinset r hu),
        zero_mul]
  rw [h1, h2, finiteKernelField_eq_sum (boxFinset 0 r)
    (fun u hu => timeTail_eq_zero_of_notMem_boxFinset r (Aex : ℝ) hu) ζ z,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold External.BallGreen.timeTail
  rw [floor_natCast_mul_sq]
  ring

/-- Step 2 of the dimension-four proof: the infinite-time ball Green field and
its finite-time version at horizon `A_ex r²` differ by more than `s` with
probability at most `C exp(-c min(s², s r²))`, uniformly in the site and in the
horizon. -/
theorem exists_ball_time_tail (hBG : Sandpile.External.BallGreenBounds) (θ₀ K₀ : ℝ)
    (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ Aex : ℕ, 1 ≤ Aex → ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        Integrable (fun x : ℝ => Real.exp (θ₀ * |x|)) ν →
        (∫ x, Real.exp (θ₀ * |x|) ∂ν) ≤ K₀ → (∫ x, x ∂ν) = 0 →
        ∀ r : ℕ, 2 ≤ r → ∀ s : ℝ, 0 ≤ s → ∀ z : Site 4,
          LatticeProb.iidLaw 4 ν
              {ζ | s < |ballGreenField r ζ z - frGreenFieldTime r (Aex * r ^ 2) ζ z|}
            ≤ ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) (s * (r : ℝ) ^ 2)))) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_finite_kernel_field_two_scale_tail θ₀ K₀ hθ₀
  obtain ⟨G, g, hG, hg, hb⟩ := hBG
  refine ⟨c / G, C, by positivity, hC, ?_⟩
  intro Aex hAex ν hν hint hK hmean r hr s hs z
  haveI := hν
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have hA1 : (1 : ℝ) ≤ (Aex : ℝ) := by exact_mod_cast hAex
  have hlast := (hb r hr).2.2.2.2.2 (Aex : ℝ) hA1
  have hexp1 : Real.exp (-g * (Aex : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp0 : 0 ≤ Real.exp (-g * (Aex : ℝ)) := Real.exp_nonneg _
  have hmax : ∀ u : Site 4, |External.BallGreen.timeTail r (Aex : ℝ) u| ≤ G / (r : ℝ) ^ 2 := by
    intro u
    refine (hlast.1 u).trans ?_
    have hGr : (0 : ℝ) ≤ G / (r : ℝ) ^ 2 := by positivity
    nlinarith
  have hsq : (∑' u : Site 4, External.BallGreen.timeTail r (Aex : ℝ) u ^ 2) ≤ G := by
    refine hlast.2.trans ?_
    nlinarith
  have hAA : (0 : ℝ) < G / (r : ℝ) ^ 2 := by positivity
  have hzero : ∀ u ∉ boxFinset (0 : Site 4) r,
      External.BallGreen.timeTail r (Aex : ℝ) u = 0 :=
    fun u hu => timeTail_eq_zero_of_notMem_boxFinset r _ hu
  have hh := htail 4 ν hν hint hK hmean (External.BallGreen.timeTail r (Aex : ℝ))
    (boxFinset 0 r) hzero G (G / (r : ℝ) ^ 2) hG hAA hsq hmax z s hs
  have hset : {ζ : Site 4 → ℝ |
      s < |ballGreenField r ζ z - frGreenFieldTime r (Aex * r ^ 2) ζ z|}
      = {ζ : Site 4 → ℝ |
      s < |finiteKernelField (External.BallGreen.timeTail r (Aex : ℝ)) ζ z|} := by
    ext ζ
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ballGreenField_sub_frGreenFieldTime]
  rw [hset]
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hdiv : s / (G / (r : ℝ) ^ 2) = s * (r : ℝ) ^ 2 / G := by
    rw [div_div_eq_mul_div]
  have hmin : min (s ^ 2 / G) (s / (G / (r : ℝ) ^ 2))
      = min (s ^ 2) (s * (r : ℝ) ^ 2) / G := by
    rw [hdiv, min_div_div_right hG.le]
  rw [hmin]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le
  have : c * (min (s ^ 2) (s * (r : ℝ) ^ 2) / G) = c / G * min (s ^ 2) (s * (r : ℝ) ^ 2) := by
    ring
  rw [this]

end Sandpile
