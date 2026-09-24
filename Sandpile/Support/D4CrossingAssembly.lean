/-
The dimension-four ball-killed Green crossing estimate, assembled from the
near-far reduction, the Gaussian comparison and the RSW lower tail.  The
planar RSW input enters as the explicit hypothesis `External.PlanarRSW`
(the paper cites the RSW theorem for symmetric positively associated planar
percolation, sandpile.tex:400, 2064, 2218, 2235).
-/
import Sandpile.Support.NearFarCrossing
import Sandpile.Support.PlaneRectangle
import Sandpile.Support.RswTail
import Sandpile.Support.SecondMomentExp
import Sandpile.Support.RpowEventual
import Sandpile.Support.BallRectangleDuality
import Sandpile.External.PlanarRSW
import Sandpile.Support.FinalBoundThreeTerms

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Sandpile

theorem d4_ball_green_crossing_of_rsw
    (hBallGreen : External.BallGreenBounds) (hRSW : External.PlanarRSW)
    (ν₀ θ₀ K₀ ϑ : ℝ) (_hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) (hϑ : 1 ≤ ϑ) :
    ∀ ε : ℝ, 0 < ε → ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧ ∃ r₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ r : ℕ, r₀ ≤ r → ∀ x : Sandpile.Site 4,
          LatticeProb.iidLaw 4 ν
              {ζ | Sandpile.HasStarTopBottomCrossing ϑ r x
                {z | Sandpile.ballGreenField r ζ z ≤ -(ε * Real.log r)}} ≤
            ENNReal.ofReal (C * (Real.log r) ^ 3 * (r : ℝ) ^ (-γ)) := by
  intro ε hε
  set η : ℝ := ε / 10 with hηdef
  have hη : 0 < η := by positivity
  have hε2 : 0 < ε / 2 := by positivity
  by_cases hK₀ : 0 < K₀
  · -- main case: K₀ > 0
    -- near-far reduction with p := 1
    obtain ⟨α, C₁, hα, hα1, hC₁, r₁, hred⟩ :=
      exists_near_far_crossing_reduction hBallGreen θ₀ K₀ η 1 ϑ hθ₀ hη (by norm_num) hϑ
    -- Gaussian comparison
    obtain ⟨C₂, hC₂, r₂, hcomp⟩ :=
      exists_gaussian_aspect_rectangle_comparison hBallGreen θ₀ K₀ α η ϑ hθ₀ hα hη hϑ
    -- the variance ceiling V := 16 K₀ / θ₀²
    obtain ⟨r₃, hr₃⟩ := exists_two_le_rpow α hα
    obtain ⟨V, hVval⟩ : ∃ V : ℝ≥0, V.val = 16 * K₀ / θ₀ ^ 2 :=
      ⟨⟨16 * K₀ / θ₀ ^ 2,
        (div_pos (show (0:ℝ) < 16 * K₀ by nlinarith) (show (0:ℝ) < θ₀ ^ 2 by positivity)).le⟩, rfl⟩
    have hVpos : 0 < V := by
      have : (0:ℝ) < V.val := by
        rw [hVval]
        exact div_pos (show (0:ℝ) < 16 * K₀ by nlinarith) (show (0:ℝ) < θ₀ ^ 2 by positivity)
      exact_mod_cast this
    obtain ⟨c, hc, htail⟩ :=
      gaussian_far_rectangle_lower_tail hRSW hBallGreen V hVpos ϑ hϑ
    obtain ⟨r₄, htail'⟩ := htail (ε / 2) hε2
    -- γ := min(1, 2α, c (ε/2)²) / 2
    refine ⟨min (min 1 (2 * α)) (c * (ε / 2) ^ 2) / 2, C₁ + C₂ + 1,
      by positivity, by positivity, ⟨max (max (max (max r₁ r₂) r₃) r₄) 3, ?_⟩⟩
    intro ν hν hmean hvar hexpint hexp r hr x
    -- r bounds
    have hr1 : r₁ ≤ r := by omega
    have hr2 : r₂ ≤ r := by omega
    have hr3 : r₃ ≤ r := by omega
    have hr3r : 3 ≤ r := by omega
    -- the second moment v and its ceiling
    have hvnn : 0 ≤ ∫ z : ℝ, z ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg z
    obtain ⟨v, hvdef⟩ : ∃ v : ℝ≥0, (v.val = ∫ z : ℝ, z ^ 2 ∂ν) := ⟨⟨∫ z : ℝ, z ^ 2 ∂ν, hvnn⟩, rfl⟩
    have hvV : v ≤ V := by
      -- integrability and bound for exp((θ₀/2)|z|)
      have hint2 : Integrable (fun z : ℝ => Real.exp ((θ₀ / 2) * |z|)) ν :=
        hexpint.mono' ((measurable_const.mul measurable_id.abs).exp.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun z => by
            have hz : (0:ℝ) ≤ |z| := abs_nonneg z
            have hhalf : θ₀ / 2 * |z| ≤ θ₀ * |z| := by nlinarith
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.mpr hhalf)
      have hexp2 : ∫ z : ℝ, Real.exp ((θ₀ / 2) * |z|) ∂ν ≤ K₀ := by
        have hnn : 0 ≤ᵐ[ν] fun z : ℝ => Real.exp ((θ₀ / 2) * |z|) :=
          Filter.Eventually.of_forall fun z => (Real.exp_pos _).le
        have hint1 : Integrable (fun z : ℝ => Real.exp (θ₀ * |z|)) ν := hexpint
        have hge : (fun z : ℝ => Real.exp ((θ₀ / 2) * |z|)) ≤ᵐ[ν]
            fun z : ℝ => Real.exp (θ₀ * |z|) :=
          Filter.Eventually.of_forall fun z => by
            have hz : (0:ℝ) ≤ |z| := abs_nonneg z
            have hhalf : θ₀ / 2 * |z| ≤ θ₀ * |z| := by nlinarith
            exact Real.exp_le_exp.mpr hhalf
        have h2 := integral_mono_of_nonneg hnn hint1 hge
        exact le_trans h2 hexp
      have hsm := second_moment_le_of_exp_moment ν (θ₀ / 2) (by positivity) K₀ hint2 hexp2
      -- v ≤ 16 K₀ / θ₀²
      have h16 : (4:ℝ) / (θ₀ / 2) ^ 2 * K₀ = 16 * K₀ / θ₀ ^ 2 := by
        field_simp
        ring
      have hval : v.val ≤ V.val := by
        rw [hvdef, hVval]
        exact h16 ▸ hsm
      exact_mod_cast hval
    -- the near-far reduction at level -ε log r
    have hred' := hred ν hν hexpint hexp hmean r hr1 x (-(ε * Real.log r))
    -- the far level is -(ε - 2η) log r = -(4ε/5) log r
    have hfarlvl : -(ε * Real.log r) + 2 * η * Real.log r = -((4 / 5) * ε) * Real.log r := by
      have : η = ε / 10 := rfl
      field_simp
      ring
    -- bridge: star crossing of the low far set implies crossingValue ≤ level
    have hbridge : {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x {z |
        finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ z ≤
          -(ε * Real.log r) + 2 * η * Real.log r}} ⊆
        {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
          finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
            (planeTranslate x (w : Site 2))) ≤ -(ε * Real.log r) + 2 * η * Real.log r} := by
      intro ζ hζ
      simp only [Set.mem_setOf_eq] at hζ ⊢
      exact crossingValue_le_of_hasStarTopBottomCrossing (le_trans (zero_le_one) hϑ) r x _ hζ
    have hmono1 := measure_mono (μ := LatticeProb.iidLaw 4 ν) hbridge
    -- the comparison at a := 4ε/5
    have hcomp' := hcomp ν hν hexpint hexp hmean v (by rw [← hvdef]; rfl) r hr2 x ((4 / 5) * ε)
    -- the Gaussian tail at a := ε/2 with L := ⌊r^α⌋₊
    have hL2 : 2 ≤ ⌊(r : ℝ) ^ α⌋₊ := Nat.le_floor (hr₃ r hr3)
    have hr4' : r₄ ≤ r := by omega
    have hG := htail' r ⌊(r : ℝ) ^ α⌋₊ hr4' hL2 farCutoff isCutoff_farCutoff x v hvV
    -- level identities
    have hlvl : -(ε * Real.log r) + 2 * η * Real.log r = -((4 / 5) * ε) * Real.log r := by
      have hηeq : η = ε / 10 := rfl
      field_simp
      ring
    have hlvlg : -((4 / 5) * ε - 3 * η) * Real.log r = -(ε / 2 * Real.log r) := by
      have hηeq : η = ε / 10 := rfl
      field_simp
      ring
    rw [hlvlg] at hcomp'
    -- the crossing-value event has finite measure
    have hcv1 : (LatticeProb.iidLaw 4 ν)
        {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
          finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
            (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r} ≤ 1 :=
      le_trans (measure_mono (subset_univ _)) (le_of_eq measure_univ)
    have hcvne : ((LatticeProb.iidLaw 4 ν)
        {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
          finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
            (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r}) ≠ ∞ := by
      intro h
      have h2 := hcv1
      rw [h] at h2
      exact absurd h2 (by simp)
    -- rewrite the crossing-value event level in hmono1
    rw [hlvl] at hmono1 hred'
    -- the Gaussian event has finite measure
    have hGne : ((LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v))
        {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
          finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
            (planeTranslate x (w : Site 2))) ≤ -(ε / 2 * Real.log r)}) ≠ ∞ :=
      by
      intro h
      have h2 : (LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v)) univ ≤ 1 := by
        rw [measure_univ]
      have h3 : (LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v))
          {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
            finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
              (planeTranslate x (w : Site 2))) ≤ -(ε / 2 * Real.log r)} ≤ 1 :=
        le_trans (measure_mono (subset_univ _)) h2
      rw [h] at h3
      exact absurd h3 (by simp)
    -- chain in ENNReal
    have hfinal : (LatticeProb.iidLaw 4 ν)
        {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x {z | ballGreenField r ζ z ≤
          -(ε * Real.log r)}} ≤
      ENNReal.ofReal ((r : ℝ) ^ (-(c * (ε / 2) ^ 2)) + C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α)
        + C₁ * (r : ℝ) ^ (-(1:ℝ))) := by
      have hcvreal : (LatticeProb.iidLaw 4 ν)
          {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
            finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
              (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r} =
        ENNReal.ofReal ((LatticeProb.iidLaw 4 ν).real
          {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
            finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
              (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r}) := by
        exact (ofReal_measureReal hcvne).symm
      have hGreal : (LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v)).real
          {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
            finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
              (planeTranslate x (w : Site 2))) ≤ -(ε / 2 * Real.log r)} ≤
        (r : ℝ) ^ (-(c * (ε / 2) ^ 2)) := by
        have h9 := (ENNReal.toReal_le_toReal hGne ENNReal.ofReal_ne_top).mpr hG
        rwa [ENNReal.toReal_ofReal (by positivity)] at h9
      calc ((LatticeProb.iidLaw 4 ν) {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x
          {z | ballGreenField r ζ z ≤ -(ε * Real.log r)}}) ≤
          (LatticeProb.iidLaw 4 ν)
            {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x {z |
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ z ≤
                -((4 / 5) * ε) * Real.log r}} +
          ENNReal.ofReal (C₁ * (r : ℝ) ^ (-(1:ℝ))) := hred'
        _ ≤ (LatticeProb.iidLaw 4 ν)
            {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r} +
          ENNReal.ofReal (C₁ * (r : ℝ) ^ (-(1:ℝ))) := add_le_add hmono1 (le_refl _)
        _ = ENNReal.ofReal ((LatticeProb.iidLaw 4 ν).real
            {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r}) +
          ENNReal.ofReal (C₁ * (r : ℝ) ^ (-(1:ℝ))) := by rw [hcvreal]
        _ = ENNReal.ofReal ((LatticeProb.iidLaw 4 ν).real
            {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                (planeTranslate x (w : Site 2))) ≤ -((4 / 5) * ε) * Real.log r} +
          C₁ * (r : ℝ) ^ (-(1:ℝ))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal ((LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v)).real
            {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                (planeTranslate x (w : Site 2))) ≤ -(ε / 2 * Real.log r)} +
          C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) + C₁ * (r : ℝ) ^ (-(1:ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          linarith [hcomp']
        _ ≤ ENNReal.ofReal ((r : ℝ) ^ (-(c * (ε / 2) ^ 2)) + C₂ * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α)
          + C₁ * (r : ℝ) ^ (-(1:ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          linarith [hGreal]
    exact le_trans hfinal (ENNReal.ofReal_le_ofReal
      (final_bound_three_terms c ε α C₁ C₂ hc hε hα hC₁ hC₂ r hr3r))
  · -- vacuous case: K₀ ≤ 0 contradicts ∫ exp ≥ 1
    refine ⟨1, 1, by norm_num, by norm_num, ⟨0, ?_⟩⟩
    intro ν hν hmean hvar hexpint hexp r hr x
    have h1 : (1:ℝ) ≤ ∫ z : ℝ, Real.exp (θ₀ * |z|) ∂ν := by
      have hnn : 0 ≤ᵐ[ν] fun _ : ℝ => (1:ℝ) :=
        Filter.Eventually.of_forall fun _ => by norm_num
      have hge : (fun _ : ℝ => (1:ℝ)) ≤ᵐ[ν] fun z : ℝ => Real.exp (θ₀ * |z|) :=
        Filter.Eventually.of_forall fun z => Real.one_le_exp (by positivity)
      have h2 := integral_mono_of_nonneg hnn hexpint hge
      simpa using h2
    have h3 : (1:ℝ) ≤ K₀ := le_trans h1 hexp
    exact absurd h3 (by linarith)
end Sandpile