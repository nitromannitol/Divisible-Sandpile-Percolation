import Sandpile.Support.MainExplInterpolationTightness
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Uniform interpolation-norm bounds for the odometer

Compact uniform bounds for the interpolated, rescaled odometer, proved in
`exists_interpolation_norm_bound`. A finite spatial net, the modulus of continuity estimate,
and the coupling convergence of the stopping values to the Brownian value control large
scales `R ≥ R₀`; finite lattice boxes control the remaining bounded scales `1 ≤ R < R₀`. The
two regimes are combined through a compactness argument that covers the given compact set `K`
by finitely many balls on which the interpolated field cannot oscillate too much.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile.Continuum

universe u
namespace Sandpile

/-- Uniform boundedness in probability on compact sets over all scales at least one. -/
theorem exists_interpolation_norm_bound
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[P] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω' → Sandpile.Continuum.Space d)
    (hB : ∀ x : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d x (B x) P')
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : Ω'), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) (K : Set (Space d)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ R : ℝ, 1 ≤ R →
      centeredMassLaw d ν {σ | ∃ z ∈ K,
        M < |multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z|}
        ≤ ENNReal.ofReal ε := by
  classical
  let F : ℝ → (Site d → ℝ) → Space d → ℝ := fun R σ z => multilinearInterp R
    (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z
  let Y : Ω → Space d → ℝ := fun ω z => brownianValue (B z) P' (fun t y => Z t y ω) T z
  have hFm : ∀ R z, Measurable (fun σ => F R σ z) := fun R z =>
    measurable_multilinearInterp_apply R _ z (measurable_rescaled_odometer_field T R)
  have hZm : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
      AEMeasurable (Z q.1 q.2) P := by
    intro q hq
    exact (measurable_const.mul (hW.meas _
      (Support.memLp_greenTimeBM hd hd3 hq.1.1 q.2))).aemeasurable.congr
      (hZmod q.1 q.2).symm
  have hYm : ∀ z, AEMeasurable (fun ω => Y ω z) P := fun z =>
    Support.aemeasurable_brownianValue_of_growth (B z) P' z (hB z)
      (fun t => (hBm z t).measurable) (hBc z) P Z T hT hZm
      (hZcont T hT) (hZgrow T hT)
  obtain ⟨δ, hδ, hmod⟩ := exists_interpolation_modulus hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT K hK (ε / 3) 1 (by positivity) one_pos
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls hδ
  let A : Ω → ℝ := fun ω => ∑ z ∈ hS.toFinset, |Y ω z|
  have hAm : AEMeasurable A P :=
    Finset.aemeasurable_fun_sum hS.toFinset fun z _ => (hYm z).abs
  obtain ⟨C, hC, hPC⟩ := exists_isCompact_closure_measure_compl_lt (P.map A)
    (ENNReal.ofReal (ε / 3)) (ENNReal.ofReal_pos.mpr (by positivity))
  obtain ⟨M, hM, hCM⟩ := hC.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hYtail : P {ω | ∃ z ∈ S, M < |Y ω z|} ≤ ENNReal.ofReal (ε / 3) := by
    refine (measure_mono (show {ω | ∃ z ∈ S, M < |Y ω z|} ⊆ A ⁻¹' Cᶜ from ?_)).trans
      ((Measure.le_map_apply hAm _).trans hPC.le)
    rintro ω ⟨z, hz, hlarge⟩ hω
    have hA : |A ω| ≤ M := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hCM (subset_closure hω)
    have hsingle : |Y ω z| ≤ A ω :=
      Finset.single_le_sum (fun y _ => abs_nonneg (Y ω y)) (hS.mem_toFinset.mpr hz)
    exact not_lt_of_ge (hsingle.trans ((le_abs_self _).trans hA)) hlarge
  obtain ⟨R₀, _, hcoup⟩ := dlt4_interpolated_coupling_of_version hLocalCLT hStab d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod Ω' P' B hB hBc hBm S hS.isCompact
    T hT (hZcont T hT) (hZgrow T hT) 1 (ε / 3) one_pos (by positivity)
  obtain ⟨M₀, C₀, G, hM₀, _, hG, hsmall⟩ := Support.exists_bounded_scale_interpolation_bound d hd3
    (centeredMassLaw d ν) T (max 1 R₀) hT (le_max_left _ _) K hK ε hε
  refine ⟨max (M + 2) M₀, lt_of_lt_of_le hM₀ (le_max_right _ _), ?_⟩
  intro R hR
  by_cases hlarge : R₀ ≤ R
  · obtain ⟨Q, hQ, hQf, hQs, hbad⟩ := hcoup R hlarge
    let E : Set (Site d → ℝ) := {σ | ∃ z ∈ S, M + 1 < |F R σ z|}
    let Em : Set (Site d → ℝ) := {σ | ∃ z ∈ K, ∃ z' ∈ K,
      dist z z' < δ ∧ 1 < |F R σ z - F R σ z'|}
    let Ec : Set ((Site d → ℝ) × Ω) := {p | ∃ z ∈ S, 1 < |F R p.1 z - Y p.2 z|}
    let Ey : Set Ω := {ω | ∃ z ∈ S, M < |Y ω z|}
    have hEm : MeasurableSet E := by
      have hEq : E = ⋃ z ∈ S, {σ | M + 1 < |F R σ z|} := by ext σ; simp [E]
      rw [hEq]
      exact hS.measurableSet_biUnion fun z _ => measurableSet_lt measurable_const (hFm R z).abs
    have hEsub : Prod.fst ⁻¹' E ⊆ Ec ∪ (Prod.snd ⁻¹' Ey) := by
      rintro p ⟨z, hz, hv⟩
      by_cases hc : p ∈ Ec
      · exact Or.inl hc
      by_cases hy : p.2 ∈ Ey
      · exact Or.inr hy
      exfalso
      have h₁ : |F R p.1 z - Y p.2 z| ≤ 1 := le_of_not_gt (fun h => hc ⟨z, hz, h⟩)
      have h₂ : |Y p.2 z| ≤ M := le_of_not_gt (fun h => hy ⟨z, hz, h⟩)
      have htri := abs_add_le (F R p.1 z - Y p.2 z) (Y p.2 z)
      rw [sub_add_cancel] at htri
      linarith
    have hE : centeredMassLaw d ν E ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
      rw [← hQf, Measure.map_apply measurable_fst hEm]
      calc Q _ ≤ Q (Ec ∪ (Prod.snd ⁻¹' Ey)) := measure_mono hEsub
        _ ≤ Q Ec + Q (Prod.snd ⁻¹' Ey) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
          apply add_le_add hbad
          have hpre : Q (Prod.snd ⁻¹' Ey) ≤ P Ey := by
            rw [← hQs]
            exact Measure.le_map_apply measurable_snd.aemeasurable Ey
          exact hpre.trans hYtail
    have hsub : {σ | ∃ z ∈ K, max (M + 2) M₀ < |F R σ z|} ⊆ Em ∪ E := by
      rintro σ ⟨z, hz, hv⟩
      by_cases hm : σ ∈ Em
      · exact Or.inl hm
      by_cases he : σ ∈ E
      · exact Or.inr he
      exfalso
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (hcover hz)
      have h₁ : |F R σ z - F R σ y| ≤ 1 :=
        le_of_not_gt (fun h => hm ⟨z, hz, y, hSK hy, hzy, h⟩)
      have h₂ : |F R σ y| ≤ M + 1 := le_of_not_gt (fun h => he ⟨y, hy, h⟩)
      have htri := abs_add_le (F R σ z - F R σ y) (F R σ y)
      rw [sub_add_cancel] at htri
      have := le_max_left (M + 2) M₀
      linarith
    calc centeredMassLaw d ν _ ≤ centeredMassLaw d ν (Em ∪ E) := measure_mono hsub
      _ ≤ centeredMassLaw d ν Em + centeredMassLaw d ν E := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) :=
        add_le_add (hmod R hR) hE
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  · refine (measure_mono ?_).trans hG
    rintro σ ⟨z, hz, hv⟩ hσ
    have hRL : R ≤ max 1 R₀ := (le_of_not_ge hlarge).trans (le_max_right _ _)
    have hb := (hsmall σ hσ R hR hRL).1 z hz
    exact not_lt_of_ge (hb.trans (le_max_right _ _)) hv

end Sandpile
