/-
Uniform probability recurrence and initial scale for annular crossings.
-/
import Sandpile.Support.CascadeGeometry
import Sandpile.Support.PointwiseConc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

noncomputable def separatedPairs (x : Site d) (R : ℕ) : Finset (Site d × Site d) := by
  classical
  exact ((coarseCenters x R).product (coarseCenters x R)).filter fun p =>
    ∀ z₁ : Site d, boxDist z₁ p.1 ≤ 2 * R →
      ∀ z₂ : Site d, boxDist z₂ p.2 ≤ 2 * R → 4 * R ≤ boxDist z₁ z₂

lemma card_separatedPairs_le (x : Site d) (R : ℕ) :
    (separatedPairs x R).card ≤ (259 ^ d) ^ 2 := by
  classical
  calc
    _ ≤ ((coarseCenters x R).product (coarseCenters x R)).card := Finset.card_filter_le _ _
    _ = (coarseCenters x R).card * (coarseCenters x R).card := Finset.card_product _ _
    _ ≤ 259 ^ d * 259 ^ d := Nat.mul_le_mul (card_coarseCenters_le x R) (card_coarseCenters_le x R)
    _ = (259 ^ d) ^ 2 := (pow_two _).symm

lemma lowCrossing_subset_pair_union [NeZero d] (t : ℕ) (m : ℝ) (x : Site d) (R : ℕ)
    (hR : 1 ≤ R) (s : ℝ) :
    Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x ((64 * R : ℕ) : ℝ) s ⊆
      ⋃ p ∈ separatedPairs x R,
        (Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.1 (R : ℝ) s ∩
          Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.2 (R : ℝ) s) := by
  classical
  intro ω hω
  have hh := (hasStarAnnularCrossing_iff_lowCrossing ω t m x (64 * R) s).mpr hω
  obtain ⟨x₁, hx₁, x₂, hx₂, h₁, h₂, hsep⟩ := exists_separated_subcrossings _ x R hR hh
  have hp : (x₁, x₂) ∈ separatedPairs x R :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx₁, hx₂⟩, hsep⟩
  apply Set.mem_iUnion.mpr
  refine ⟨(x₁, x₂), Set.mem_iUnion.mpr ⟨hp, ?_⟩⟩
  exact ⟨(hasStarAnnularCrossing_iff_lowCrossing ω t m x₁ R s).mp h₁,
    (hasStarAnnularCrossing_iff_lowCrossing ω t m x₂ R s).mp h₂⟩

noncomputable def annularProbability (ν : Measure ℝ) (t : ℕ) (m : ℝ) (R : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ⨆ x : Site d, (LatticeProb.iidLaw d ν)
    (Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x (R : ℝ) s)

lemma annularProbability_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℕ) (m : ℝ) (R : ℕ) (s : ℝ) : annularProbability (d := d) ν t m R s ≤ 1 :=
  iSup_le fun _ => prob_le_one

lemma exists_annular_probability_step (_hGH : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
      ∀ (t R : ℕ), 1 ≤ R → ∀ (s a : ℝ), 0 < a → 2 * a < s →
        annularProbability (d := d) ν t (Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t)
          (64 * R) s ≤
          ENNReal.ofReal C * (annularProbability (d := d) ν t
            (Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t) R (s - 2 * a)) ^ 2 +
          ENNReal.ofReal (C * (R : ℝ) ^ d * Real.exp (-(c *
            min (a ^ 2 * (R : ℝ) ^ ((d : ℝ) - 4)) (a * (R : ℝ) ^ ((d : ℝ) - 2))))) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨c, C₀, hc, hC₀, hdec⟩ := Frozen.dgt4_level_shift_decoupling d hd θ K hθ
  let N : ℝ := ((259 ^ d) ^ 2 : ℕ)
  have hN : 0 < N := by dsimp [N]; positivity
  let C := N * (C₀ + 1)
  have hC : 0 < C := mul_pos hN (by linarith)
  have hNC : N ≤ C := by dsimp [C]; nlinarith
  have hNC₀ : N * C₀ ≤ C := by dsimp [C]; nlinarith
  refine ⟨c, C, hc, hC, ?_⟩
  intro ν hν hmean hvp hvf hexp hK t R hR s a ha hs
  haveI := hν
  let m := Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t
  let q := annularProbability (d := d) ν t m R (s - 2 * a)
  let e := Real.exp (-(c * min (a ^ 2 * (R : ℝ) ^ ((d : ℝ) - 4))
    (a * (R : ℝ) ^ ((d : ℝ) - 2))))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hpair (x : Site d) (p : Site d × Site d) (hp : p ∈ separatedPairs x R) :
      (LatticeProb.iidLaw d ν)
        (Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.1 (R : ℝ) s ∩
          Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.2 (R : ℝ) s) ≤
        q ^ 2 + ENNReal.ofReal (C₀ * (R : ℝ) ^ d * e) := by
    apply hdec ν hν hmean hvp hvf hexp hK t p.1 p.2 (R : ℝ) (R : ℝ)
      (by exact_mod_cast hR) (by exact_mod_cast hR) _ s a ha hs
    intro z₁ hz₁ z₂ hz₂
    have hsep := (Finset.mem_filter.mp hp).2
    change (boxDist z₁ p.1 : ℝ) ≤ 2 * (R : ℝ) at hz₁
    change (boxDist z₂ p.2 : ℝ) ≤ 2 * (R : ℝ) at hz₂
    have hn₁ : boxDist z₁ p.1 ≤ 2 * R := by exact_mod_cast hz₁
    have hn₂ : boxDist z₂ p.2 ≤ 2 * R := by exact_mod_cast hz₂
    exact_mod_cast hsep z₁ hn₁ z₂ hn₂
  apply iSup_le
  intro x
  let E := fun p : Site d × Site d =>
    Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.1 (R : ℝ) s ∩
      Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m p.2 (R : ℝ) s
  have hcN : ((separatedPairs x R).card : ℝ≥0∞) ≤ ENNReal.ofReal N := by
    simpa only [N, ENNReal.ofReal_natCast] using
      (show ((separatedPairs x R).card : ℝ≥0∞) ≤ (((259 ^ d) ^ 2 : ℕ) : ℝ≥0∞) by
        exact_mod_cast card_separatedPairs_le x R)
  calc
    _ ≤ (LatticeProb.iidLaw d ν) (⋃ p ∈ separatedPairs x R, E p) :=
      measure_mono (lowCrossing_subset_pair_union t m x R hR s)
    _ ≤ ∑ p ∈ separatedPairs x R, (LatticeProb.iidLaw d ν) (E p) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ separatedPairs x R, (q ^ 2 + ENNReal.ofReal (C₀ * (R : ℝ) ^ d * e)) :=
      Finset.sum_le_sum (hpair x)
    _ = ((separatedPairs x R).card : ℝ≥0∞) *
        (q ^ 2 + ENNReal.ofReal (C₀ * (R : ℝ) ^ d * e)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal N * (q ^ 2 + ENNReal.ofReal (C₀ * (R : ℝ) ^ d * e)) :=
      mul_le_mul' hcN le_rfl
    _ = ENNReal.ofReal N * q ^ 2 + ENNReal.ofReal (N * C₀ * (R : ℝ) ^ d * e) := by
      rw [mul_add, ← ENNReal.ofReal_mul hN.le]
      congr 2
      ring
    _ ≤ ENNReal.ofReal C * q ^ 2 + ENNReal.ofReal (C * (R : ℝ) ^ d * e) := by
      apply add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hNC) le_rfl)
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNC₀ (by positivity)) he

lemma exists_annular_probability_initial (hGH : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K → ∀ t : ℕ,
      1 ≤ Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t →
        annularProbability (d := d) ν t (Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t)
          1 (Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t / 4) ≤
          ENNReal.ofReal (C * Real.exp (-(c * Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t))) := by
  classical
  obtain ⟨c, C, hc, hC, hconc⟩ := exists_odometerOf_conc hGH hd θ K hθ
  refine ⟨c / 16, (5 : ℝ) ^ d * C, by positivity, by positivity, ?_⟩
  intro ν hν hexp hK t hm
  haveI := hν
  let m := Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t
  have hm' : 1 ≤ m := hm
  have hm0 : 0 ≤ m / 4 := by linarith
  let E := fun y : Site d => {ω : Site d → ℝ | m / 4 ≤ |odometerOf ω t y - m|}
  have hpoint (y : Site d) : (LatticeProb.iidLaw d ν) (E y) ≤
      ENNReal.ofReal (C * Real.exp (-(c / 16 * m))) := by
    have hh := hconc ν hν hexp hK y t (m / 4) hm0
    refine hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
    apply Real.exp_le_exp.mpr
    have hmin : m / 16 ≤ min ((m / 4) ^ 2) (m / 4) := by
      apply le_min <;> nlinarith [sq_nonneg (m - 1)]
    have hh := mul_le_mul_of_nonneg_left hmin hc.le
    nlinarith
  apply iSup_le
  intro x
  have hsub : Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x (1 : ℝ) (m / 4) ⊆
      ⋃ y ∈ boxFinset x 2, E y := by
    intro ω hω
    obtain ⟨T, hT, _hconn, ⟨y, hyT, _hy⟩, _hout⟩ := hω
    have hxy : (boxDist y x : ℝ) ≤ 2 := by
      have hh := (hT hyT).1
      change (boxDist y x : ℝ) ≤ 2 * (1 : ℝ) at hh
      simpa only [mul_one] using hh
    have hybox : y ∈ boxFinset x 2 := by
      apply mem_boxFinset
      rw [boxDist_comm x y]
      exact_mod_cast hxy
    have hv := (hT hyT).2
    have hE : ω ∈ E y := by
      change m / 4 ≤ |odometerOf ω t y - m|
      have hh := neg_le_abs (odometerOf ω t y - m)
      linarith
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hybox, hE⟩⟩
  simp only [Nat.cast_one]
  change (LatticeProb.iidLaw d ν)
    (Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x 1 (m / 4)) ≤
    ENNReal.ofReal ((5 : ℝ) ^ d * C * Real.exp (-(c / 16 * m)))
  calc
    _ ≤ (LatticeProb.iidLaw d ν) (⋃ y ∈ boxFinset x 2, E y) := measure_mono hsub
    _ ≤ ∑ y ∈ boxFinset x 2, (LatticeProb.iidLaw d ν) (E y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ boxFinset x 2, ENNReal.ofReal (C * Real.exp (-(c / 16 * m))) :=
      Finset.sum_le_sum (fun y _ => hpoint y)
    _ = ENNReal.ofReal ((5 : ℝ) ^ d * C * Real.exp (-(c / 16 * m))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        Finset.sum_const, nsmul_eq_mul, card_boxFinset]
      congr 1
      push_cast
      ring

lemma annularProbability_antitone_level {d : ℕ} (ν : Measure ℝ)
    (t : ℕ) (m : ℝ) (R : ℕ) {s u : ℝ} (hsu : s ≤ u) :
    annularProbability (d := d) ν t m R u ≤ annularProbability (d := d) ν t m R s := by
  apply iSup_mono
  intro x
  apply MeasureTheory.measure_mono
  rintro ω ⟨T, hT, hconn, hin, hout⟩
  refine ⟨T, fun y hy => ⟨(hT hy).1, ?_⟩, hconn, hin, hout⟩
  have hh := (hT hy).2
  linarith

end Sandpile
