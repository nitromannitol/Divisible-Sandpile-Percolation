/-
A fixed positive lower bound for the crossing probability of the target
fixed-aspect rectangle at a small negative level, via RSW.
-/
import Sandpile.Support.RswSquareHalfScale
import Sandpile.Support.RswHardStep
import Sandpile.Support.RectangleMonotonicity

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section
namespace Sandpile

/-- For aspect `ϑ ≥ 1` there is `q > 0` (depending only on the RSW function
and `ϑ`) such that eventually the target rectangle `⌊ϑ r⌋ x r` is crossed at
level `-(a/4) log r` with probability at least `q`. -/
lemma exists_gaussian_rectangle_crossing_lower (hRSW : External.PlanarRSW)
    (hBall : External.BallGreenBounds) (V : ℝ≥0) (hV : 0 < V) (ϑ : ℝ) (hϑ : 1 ≤ ϑ) :
    ∃ q : ℝ, 0 < q ∧ ∀ a : ℝ, 0 < a → ∃ r₀ : ℕ, ∀ r L : ℕ, r₀ ≤ r → 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        ENNReal.ofReal q ≤ LatticeProb.iidLaw 4 (gaussianReal 0 v)
          {ζ | -(a / 4 * Real.log r) ≤ crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
            finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
  obtain ⟨q0, hq0⟩ := hRSW (Nat.ceil (2 * ϑ)) (by
    have h2 : (0 : ℝ) < 2 * ϑ := by positivity
    exact Nat.ceil_pos.mpr h2)
  set half : Set.Icc (0 : ℝ) 1 := ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ with hhalfdef
  set q : ℝ := ((q0 half : Set.Icc (0 : ℝ) 1) : ℝ) with hqdef
  have hqpos : 0 < q := by
    have h1 : (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < half := by
      show ((⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) < (half : ℝ)
      show (0 : ℝ) < (1 : ℝ) / 2
      norm_num
    have h2 := q0.strictMono h1
    have h0 : ((q0 (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) : ℝ) = 0 := by
      have hb : (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) = ⊥ := rfl
      have hb2 := congrArg q0 hb
      simp only [OrderIso.map_bot] at hb2
      simp only [hb2]
      norm_num
    have h2' : ((q0 (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) : ℝ) <
        ((q0 half : Set.Icc (0 : ℝ) 1) : ℝ) :=
      Subtype.coe_lt_coe.mpr (by simpa using h2)
    rw [h0] at h2'
    exact h2'
  refine ⟨q, hqpos, ?_⟩
  intro a ha
  obtain ⟨r₁, h₁⟩ := exists_gaussian_square_crossing_ge_half_scale hBall V hV (a / 4) (by positivity)
  refine ⟨2 * r₁ ⊔ 7, ?_⟩
  intro r L hr hL φ hφ x v hv
  obtain ⟨n, h2n, hr2n⟩ : ∃ n : ℕ, 2 * n ≤ r ∧ r ≤ 2 * n + 1 := by
    refine ⟨r / 2, ?_, ?_⟩ <;> omega
  set ρ : ℕ := Nat.ceil (2 * ϑ) with hρdef
  have hr2 : 2 ≤ r := by omega
  have hn1 : 1 ≤ n := by omega
  have hr1 : r₁ ≤ r := by omega
  set μ' : Measure (Site 2 → ℝ) := (LatticeProb.iidLaw 4 (gaussianReal 0 v)).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) with hμ'
  haveI : IsProbabilityMeasure μ' := isProbabilityMeasure_planar_image (gaussianReal 0 v) r L φ x
  set lvl : ℝ := -(a / 4 * Real.log r) with hlvl
  have hρ1 : 1 ≤ ρ := Nat.ceil_pos.mpr (by positivity)
  -- square half bound at square scale 2n, field scale r
  have hcard : (planeRectangle (2 * n) (2 * n)).card ≤ r ^ 3 := by
    rw [card_planeRectangle]
    have h1 : (2 * n + 1) * (2 * n + 1) ≤ (r + 1) * (r + 1) := by
      have h2 : 2 * n + 1 ≤ r + 1 := by omega
      exact Nat.mul_le_mul h2 h2
    have h3 : (r + 1) * (r + 1) ≤ r * r * r := by
      have h4 : 7 ≤ r := by omega
      have h5 : ((r + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ ((r : ℕ) : ℝ) * ((r : ℕ) : ℝ) * ((r : ℕ) : ℝ) := by
        push_cast
        have h7 : (7 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h4
        nlinarith [h7]
      exact_mod_cast h5
    have h9 : r * r * r = r ^ 3 := by ring
    exact le_trans h1 (le_trans h3 h9.le)
  have hsqm : (1 : ℝ≥0∞) / 2 ≤ LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} :=
    h₁ r L (2 * n) hr1 hL (by omega) (by omega) hcard φ hφ x v hv
  have Hmeas : Measurable
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) :=
    measurable_pi_lambda _ (fun z =>
      measurable_finiteKernelField (boxFinset 0 r)
        (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (planeTranslate x z))
  have hmeasS : MeasurableSet {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
    show MeasurableSet ((fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) ⁻¹'
      (planarCrossingEvent (2 * n) (2 * n) lvl))
    exact Hmeas (measurableSet_planarCrossingEvent _ _ _)
  have hmeasE : MeasurableSet {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * ρ * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
    show MeasurableSet ((fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) ⁻¹'
      (planarCrossingEvent (2 * n) (2 * ρ * n) lvl))
    exact Hmeas (measurableSet_planarCrossingEvent _ _ _)
  -- square event subset easy event
  have hρn : 2 * n ≤ 2 * ρ * n := by
    have h0 : n ≤ ρ * n := Nat.le_mul_of_pos_left n hρ1
    have h1 : 2 * n ≤ 2 * (ρ * n) := Nat.mul_le_mul_left 2 h0
    simpa [Nat.mul_assoc] using h1
  have hsub : {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} ⊆
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * ρ * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
    intro ζ hζ
    simp only [Set.mem_setOf_eq] at hζ ⊢
    exact hζ.trans (crossingValue_width_height_mono (le_refl _) hρn
      (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
  have hmono : LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} ≤
    LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * ρ * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} :=
    measure_mono hsub
  have hsqm' := hsqm.trans hmono
  have hpreE : LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * ρ * n))
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} =
    μ' (planarCrossingEvent (2 * n) (2 * ρ * n) lvl) := by
    rw [hμ']
    exact (planar_image_event (gaussianReal 0 v) r L φ x (2 * n) (2 * ρ * n) lvl).symm
  have hhalfreal : (1 : ℝ) / 2 ≤
      μ'.real (planarCrossingEvent (2 * n) (2 * ρ * n) lvl) := by
    show (1 : ℝ) / 2 ≤ (μ' (planarCrossingEvent (2 * n) (2 * ρ * n) lvl)).toReal
    have hconv := ENNReal.toReal_le_toReal
      (by norm_num : ((1 : ℝ≥0∞) / 2) ≠ ⊤)
      (measure_ne_top (LatticeProb.iidLaw 4 (gaussianReal 0 v))
        {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle (2 * n) (2 * ρ * n))
          (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))})
    have h7 := hconv.mpr hsqm'
    rw [hpreE] at h7
    simpa using h7
  have hhalfIcc : half ≤ probabilityInUnitInterval μ'
      (planarCrossingEvent (2 * n) (2 * ρ * n) lvl) := by
    simp only [probabilityInUnitInterval]
    exact hhalfreal
  have hRSW' := hq0 μ' (isSymmetricPlanarLaw_cutField (gaussianReal 0 v) r L φ x)
    (isAssociatedPlanarLaw_cutField (gaussianReal 0 v) r L hφ x) n hn1 lvl
  have hqle : q ≤ ((q0 (probabilityInUnitInterval μ'
      (planarCrossingEvent (2 * n) (2 * ρ * n) lvl) : Set.Icc (0 : ℝ) 1)) : ℝ) :=
    Subtype.coe_le_coe.mpr (q0.monotone hhalfIcc)
  -- hard rectangle subset target rectangle (same level)
  have hwid : ⌊ϑ * r⌋₊ ≤ 2 * ρ * n := by
    have hϑnn : (0 : ℝ) ≤ ϑ := by linarith
    have hrnn : (0 : ℝ) ≤ (r : ℝ) := by positivity
    have hpos : (0 : ℝ) ≤ ϑ * r := mul_nonneg hϑnn hrnn
    have h1 : (⌊ϑ * r⌋₊ : ℝ) ≤ ϑ * r := Nat.floor_le hpos
    have ha : (2 : ℝ) * ϑ ≤ (ρ : ℝ) := by
      rw [hρdef]
      exact_mod_cast Nat.le_ceil (2 * ϑ)
    have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
    have hb : ϑ * r ≤ (2 : ℝ) * ϑ * ((r : ℝ) - 1) := by nlinarith [h2r, hϑnn]
    have hc : (2 : ℝ) * ϑ * ((r : ℝ) - 1) ≤ (ρ : ℝ) * ((r : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right ha (by nlinarith [h2r])
    have hd : ((r : ℝ) - 1) ≤ ((2 * n : ℕ) : ℝ) := by
      have h3 : ((r : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast hr2n
      push_cast at h3 ⊢
      linarith
    have he : (ρ : ℝ) * ((r : ℝ) - 1) ≤ (ρ : ℝ) * ((2 * n : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have hf : (ρ : ℝ) * ((2 * n : ℕ) : ℝ) = ((2 * ρ * n : ℕ) : ℝ) := by push_cast; ring
    have h13 : (⌊ϑ * r⌋₊ : ℝ) ≤ ((2 * ρ * n : ℕ) : ℝ) := by
      rw [← hf]
      calc (⌊ϑ * r⌋₊ : ℝ) ≤ ϑ * r := h1
        _ ≤ (2 : ℝ) * ϑ * ((r : ℝ) - 1) := hb
        _ ≤ (ρ : ℝ) * ((r : ℝ) - 1) := hc
        _ ≤ (ρ : ℝ) * ((2 * n : ℕ) : ℝ) := he
    exact_mod_cast h13
  have hsubHT : planarCrossingEvent (2 * ρ * n) (2 * n) lvl ⊆
      planarCrossingEvent ⌊ϑ * r⌋₊ r lvl := by
    intro F hF
    simp only [planarCrossingEvent, Set.mem_setOf_eq] at hF ⊢
    exact hF.trans (crossingValue_width_height_mono hwid h2n F)
  have hhardT : μ'.real (planarCrossingEvent (2 * ρ * n) (2 * n) lvl) ≤
      μ'.real (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl) := by
    show (μ' (planarCrossingEvent (2 * ρ * n) (2 * n) lvl)).toReal ≤
      (μ' (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl)).toReal
    have hmono2 : μ' (planarCrossingEvent (2 * ρ * n) (2 * n) lvl) ≤
        μ' (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl) := measure_mono hsubHT
    have hconv := ENNReal.toReal_le_toReal
      (measure_ne_top μ' (planarCrossingEvent (2 * ρ * n) (2 * n) lvl))
      (measure_ne_top μ' (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl))
    exact hconv.mpr hmono2
  have hchain : q ≤ μ'.real (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl) :=
    hqle.trans (hRSW'.trans hhardT)
  have hpreT : LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle ⌊ϑ * r⌋₊ r)
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} =
    μ' (planarCrossingEvent ⌊ϑ * r⌋₊ r lvl) := by
    rw [hμ']
    exact (planar_image_event (gaussianReal 0 v) r L φ x ⌊ϑ * r⌋₊ r lvl).symm
  show ENNReal.ofReal q ≤ LatticeProb.iidLaw 4 (gaussianReal 0 v)
      {ζ : Site 4 → ℝ | lvl ≤ crossingValue (planeRectangle ⌊ϑ * r⌋₊ r)
        (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))}
  rw [hpreT, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hchain

end Sandpile
end
