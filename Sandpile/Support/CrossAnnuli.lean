import Sandpile.Support.CrossLocalEvents
import Sandpile.Support.CrossFixedScaleZero
import Sandpile.Support.LimSymmetry

/-!
# Four-crossing avoidance around a square annulus

Four long rectangle crossings around a square annulus, with uniform positive probability and
independence at separated scales. The four side rectangles of an annulus centred at `x` with
radius `r` each have a uniform positive zero-level crossing probability, obtained from the RSW
estimate and a symmetry transfer that centres the crossing rectangle. Annuli whose radii grow
by a factor of eight are separated by more than the dependence range of the unit ball field,
so the four-crossing events at successive scales are independent, giving a geometric bound on
the probability that none of the first `n` annuli is crossed on all four sides. The same bound
is transferred to nonpositive crossings by negating the white-noise field.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- The symmetry transfer for closed crossings preserves the level exactly. -/
theorem measure_crossing_general_same_level {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Space 2 → Ω → ℝ) (hm : ∀ x, Measurable (X x))
    (hc : ∀ᵐ ω ∂P, Continuous fun x => X x ω) (hsym : IsSymmetricField P X)
    (a b : Fin 2 → ℝ) (hab : ∀ k, a k < b k) (i : Fin 2) (l : ℝ) :
    P {ω | Crosses (centLo a b i) (centHi a b i) 0 {x | l ≤ X x ω}} ≤
      P {ω | Crosses a b i {x | l ≤ X x ω}} := by
  let Y : Space 2 → Ω → ℝ := fun x ω => X ((rectSymmetry a b i).toFun x) ω
  have hYm : ∀ x, Measurable (Y x) := fun x => hm _
  have hYc : ∀ᵐ ω ∂P, Continuous fun x => Y x ω := by
    filter_upwards [hc] with ω hω
    exact hω.comp (continuous_planeSymmetry _)
  have hlaw : fieldLaw P X = fieldLaw P Y := by
    simpa only [one_mul] using (hsym (rectSymmetry a b i) 1 (Or.inl rfl)).symm
  have hcent : ∀ k, centLo a b i k < centHi a b i k := by
    intro k
    fin_cases k
    · dsimp [centLo, centHi]
      linarith [hab i]
    · dsimp [centLo, centHi]
      linarith [hab (swapIdx i)]
  rw [measure_crossing_eq_of_fieldLaw P P X Y hm hYm hc hYc hlaw _ _ 0 hcent l]
  apply measure_mono
  intro ω hω
  exact crosses_image_of_symmetry (rectSymmetry_maps_rect a b i)
    (rectSymmetry_face_lo a b i) (rectSymmetry_face_hi a b i) hω

/-- The four side rectangles have width four and thickness one: `annulusSideLo j` is the low
corner, in units of the radius `r`, of the `j`-th side rectangle of the annulus. -/
def annulusSideLo : Fin 4 → Fin 2 → ℝ := ![![-2, 1], ![-2, -2], ![1, -2], ![-2, -2]]
/-- The high corner, in units of the radius `r`, matching `annulusSideLo`, so together they
cut out the four side rectangles of the square annulus. -/
def annulusSideHi : Fin 4 → Fin 2 → ℝ := ![![2, 2], ![2, -1], ![2, 2], ![-1, 2]]
/-- The crossing direction of the `j`-th annulus side rectangle: coordinate `0` for the
horizontal sides and coordinate `1` for the vertical sides. -/
def annulusSideDir : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The low corner of the `j`-th side rectangle of the annulus centred at `x` with radius `r`,
namely `x` shifted by the scaled offset `annulusSideLo j`. -/
def annulusLo (x : Space 2) (r : ℝ) (j : Fin 4) (k : Fin 2) : ℝ :=
  x k + r * annulusSideLo j k
/-- The high corner of the `j`-th side rectangle of the annulus centred at `x` with radius
`r`, namely `x` shifted by the scaled offset `annulusSideHi j`. -/
def annulusHi (x : Space 2) (r : ℝ) (j : Fin 4) (k : Fin 2) : ℝ :=
  x k + r * annulusSideHi j k

/-- Side `j` of the annulus has length `4 * r` in its crossing direction `annulusSideDir j`
and thickness `r` in the other coordinate. -/
theorem annulus_lengths (x : Space 2) (r : ℝ) (j : Fin 4) :
    annulusHi x r j (annulusSideDir j) - annulusLo x r j (annulusSideDir j) = 4 * r ∧
    annulusHi x r j (swapIdx (annulusSideDir j)) -
      annulusLo x r j (swapIdx (annulusSideDir j)) = r := by
  fin_cases j <;>
    norm_num [annulusHi, annulusLo, annulusSideHi, annulusSideLo, annulusSideDir, swapIdx] <;>
      constructor <;> ring

/-- Each side rectangle of the annulus is nondegenerate: its low corner is strictly below its
high corner in both coordinates, given a positive radius `r`. -/
theorem annulus_nondegenerate (x : Space 2) {r : ℝ} (hr : 0 < r) (j : Fin 4) (k : Fin 2) :
    annulusLo x r j k < annulusHi x r j k := by
  fin_cases j <;> fin_cases k <;>
    norm_num [annulusHi, annulusLo, annulusSideHi, annulusSideLo] <;> linarith

/-- A Euclidean annulus containing the four rectangles. -/
def annulusRegion (x : Space 2) (r : ℝ) : Set (Space 2) :=
  {u | r ≤ ‖u - x‖ ∧ ‖u - x‖ ≤ 3 * r}

/-- Each side rectangle of the annulus centred at `x` with radius `r` sits inside the
Euclidean annulus `annulusRegion x r`, that is, between distance `r` and `3 * r` from `x`. -/
theorem annulus_rect_subset (x : Space 2) {r : ℝ} (hr : 0 ≤ r) (j : Fin 4) :
    rectSet (annulusLo x r j) (annulusHi x r j) ⊆ annulusRegion x r := by
  intro u hu
  have hb : ∀ k, |u k - x k| ≤ 2 * r := by
    intro k
    have h := hu k
    fin_cases j <;> fin_cases k <;>
      norm_num [annulusLo, annulusHi, annulusSideLo, annulusSideHi] at h ⊢ <;>
        rw [abs_le] <;> constructor <;> linarith [h.1, h.2]
  have hl : r ≤ |u (swapIdx (annulusSideDir j)) - x (swapIdx (annulusSideDir j))| := by
    have h := hu (swapIdx (annulusSideDir j))
    have hpos := le_abs_self (u (swapIdx (annulusSideDir j)) - x (swapIdx (annulusSideDir j)))
    have hneg := neg_le_abs (u (swapIdx (annulusSideDir j)) - x (swapIdx (annulusSideDir j)))
    fin_cases j <;>
      norm_num [annulusLo, annulusHi, annulusSideLo, annulusSideHi, annulusSideDir, swapIdx]
        at h ⊢ <;>
      linarith [h.1, h.2]
  constructor
  · apply hl.trans
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (p := 2) (u - x) (swapIdx (annulusSideDir j))
  · have hn : ‖u - x‖ ^ 2 = (u 0 - x 0) ^ 2 + (u 1 - x 1) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
    have hb0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * r)).2 (hb 0)
    have hb1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * r)).2 (hb 1)
    rw [sq_abs] at hb0 hb1
    nlinarith [norm_nonneg (u - x)]

/-- The four rectangles all have a common positive zero-level crossing bound,
chosen uniformly before the field, the center and the radius. -/
theorem uniform_annulus_side_crossing (hRSW : Sandpile.External.ContinuumRSW) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Space 2 → Ω → ℝ), (∀ x, Measurable (X x)) →
        (∀ᵐ ω ∂P, Continuous fun x => X x ω) →
        IsSymmetricField P X → IsAssociatedField P X →
        ∀ (x : Space 2) (r : ℝ), 2 ≤ r → ∀ j : Fin 4,
          c ≤ P.real {ω | Crosses (annulusLo x r j) (annulusHi x r j) (annulusSideDir j)
            {u | 0 ≤ X u ω}} := by
  obtain ⟨c, hc, hbound⟩ := uniform_zero_crossing_constant hRSW 4 (by norm_num)
  refine ⟨min c (1 / 2), lt_min hc (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro Ω _ P _ X hm hcont hsym hass x r hr j
  have h := hbound Ω P X hm hcont hsym hass (r / 2) (by norm_num; linarith)
  have hcents : centLo (annulusLo x r j) (annulusHi x r j) (annulusSideDir j) =
      ![-(4 * (r / 2)), 0] ∧
      centHi (annulusLo x r j) (annulusHi x r j) (annulusSideDir j) =
        ![4 * (r / 2), 2 * (r / 2)] := by
    obtain ⟨h1, h2⟩ := annulus_lengths x r j
    constructor
    · ext k; fin_cases k <;> simp [centLo, h1]; ring
    · ext k; fin_cases k <;> simp [centHi, h1, h2]; ring
  have htrans := measure_crossing_general_same_level P X hm hcont hsym
    (annulusLo x r j) (annulusHi x r j) (annulus_nondegenerate x (by linarith) j)
    (annulusSideDir j) 0
  rw [hcents.1, hcents.2] at htrans
  exact (min_le_left _ _).trans
    ((ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).1 (h.trans htrans))


/-- Annuli with radii increasing by a factor eight are separated by more than
the dependence range of the unit ball field. -/
theorem annulusRegion_separated (x : Space 2) {r : ℝ} (hr : 2 ≤ r) :
    ∀ i j : ℕ, i ≠ j → ∀ u ∈ annulusRegion x (8 ^ i * r),
      ∀ v ∈ annulusRegion x (8 ^ j * r), 2 * (1 : ℝ) ≤ ‖u - v‖ := by
  have hrad : ∀ i : ℕ, 2 ≤ (8 : ℝ) ^ i * r := by
    intro i
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) (n := i)]
  have hordered : ∀ i j : ℕ, i < j → ∀ u ∈ annulusRegion x (8 ^ i * r),
      ∀ v ∈ annulusRegion x (8 ^ j * r), 2 * (1 : ℝ) ≤ ‖u - v‖ := by
    intro i j hij u hu v hv
    have hscale : 8 * ((8 : ℝ) ^ i * r) ≤ 8 ^ j * r := by
      have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8) (Nat.succ_le_of_lt hij)
      have hmul := mul_le_mul_of_nonneg_right hpow (by linarith : 0 ≤ r)
      rw [pow_succ] at hmul
      nlinarith
    have htriangle : ‖v - x‖ ≤ ‖u - v‖ + ‖u - x‖ := by
      simpa only [dist_eq_norm, norm_sub_rev] using dist_triangle v u x
    have hu' := hu.2
    have hv' := hv.1
    nlinarith [hrad i]
  intro i j hij u hu v hv
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h u hu v hv
  · simpa only [norm_sub_rev] using hordered j i h v hv u hu

/-- The actual four-crossing events around the annuli have a uniform geometric
avoidance bound. All marginal and independence hypotheses are discharged for
the ball field using only RSW and Pitt's cited theorem. -/
theorem uniform_annulus_avoidance (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω) →
      ∀ (x : Space 2) (r : ℝ), 2 ≤ r → ∀ n : ℕ,
        P {ω | ∀ i < n, ¬ ∀ j : Fin 4,
          Crosses (annulusLo x (8 ^ i * r) j) (annulusHi x (8 ^ i * r) j)
            (annulusSideDir j) {u | 0 ≤ ballField d W 1 u ω}} ≤
          ENNReal.ofReal ((1 - q) ^ n) := by
  obtain ⟨c, hc0, hc1, hside⟩ := uniform_annulus_side_crossing hRSW
  refine ⟨c ^ 4, pow_pos hc0 _, pow_lt_one₀ hc0.le hc1 (by norm_num), ?_⟩
  intro d hd Ω _ P _ W hW hc x r hr n
  have hm : ∀ u, Measurable (ballField d W 1 u) :=
    fun u => hW.meas _ (memLp_ballKernel hd one_pos u)
  have hass := isAssociatedField_ballField_of_whiteNoise hPitt hd hW one_pos
  have hsym := isSymmetricField_ballField Sandpile.External.gaussianLawDeterminedByCovariance
    hd hW one_pos
  have hrad : ∀ i : ℕ, 2 ≤ (8 : ℝ) ^ i * r := by
    intro i
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) (n := i)]
  exact measure_avoid_four_crossings_le P hd hW one_pos hc hass
    (fun i => annulusRegion x (8 ^ i * r)) (annulusRegion_separated x hr)
    (fun i => annulusLo x (8 ^ i * r)) (fun i => annulusHi x (8 ^ i * r))
    (fun _ => annulusSideDir) (fun _ _ => 0)
    (fun i j => annulus_rect_subset x (by linarith [hrad i]) j)
    (fun i => annulus_nondegenerate x (by linarith [hrad i])) hc0.le hc1.le
    (fun i j => hside Ω P (ballField d W 1) hm hc hsym hass x _ (hrad i) j) n


/-- Negating every white-noise coordinate preserves the white-noise law and
its jointly measurable versions. -/
theorem isWhiteNoise_neg {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P) :
    IsWhiteNoise d (fun f ω => -W f ω) P := by
  refine ⟨?_, fun f hf => (hW.meas f hf).neg, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [neg_one_smul] using hW.gaussian.smul (fun _ => (-1 : ℝ))
  · intro f hf
    rw [integral_neg, hW.mean f hf, neg_zero]
  · intro f g hf hg
    simpa only [neg_mul_neg] using hW.cov f g hf hg
  · intro f g hf hg
    filter_upwards [hW.add f g hf hg] with ω hω
    rw [hω, neg_add]
  · intro a f hf
    filter_upwards [hW.smul a f hf] with ω hω
    rw [hω, mul_neg]
  · intro U _ μ _ f hf hfm
    obtain ⟨g, hgm, heq⟩ := hW.jointMeas μ f hf hfm
    exact ⟨fun u ω => -g u ω, hgm.neg, fun u => (heq u).neg⟩

/-- The annular bound for nonpositive crossings, which block positive arms
in the exploration argument. -/
theorem uniform_nonpositive_annulus_avoidance (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun x => ballField d W 1 x ω) →
      ∀ (x : Space 2) (r : ℝ), 2 ≤ r → ∀ n : ℕ,
        P {ω | ∀ i < n, ¬ ∀ j : Fin 4,
          Crosses (annulusLo x (8 ^ i * r) j) (annulusHi x (8 ^ i * r) j)
            (annulusSideDir j) {u | ballField d W 1 u ω ≤ 0}} ≤
          ENNReal.ofReal ((1 - q) ^ n) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := uniform_annulus_avoidance hRSW hPitt
  refine ⟨q, hq0, hq1, ?_⟩
  intro d hd Ω _ P _ W hW hc x r hr n
  have hcneg : ∀ᵐ ω ∂P, Continuous fun x => ballField d (fun f η => -W f η) 1 x ω := by
    filter_upwards [hc] with ω hω
    exact hω.neg
  simpa only [ballField, neg_nonneg] using
    hbound d hd Ω P (fun f ω => -W f ω) (isWhiteNoise_neg hW) hcneg x r hr n

end Sandpile.Support
