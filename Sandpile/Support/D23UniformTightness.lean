import Sandpile.Support.ContKolmogorovAssembly
import Sandpile.Support.D23UniformMoments
import Sandpile.External.HeatKernelBoundsProved

/-!
# Uniform compact tightness of the heat potential

This file proves the compact tightness estimates for the heat potential, uniform over scenery
laws satisfying a common exponential-moment bound (`sandpile.tex:1950-1955`). Both the
oscillation threshold and the modulus-of-continuity threshold in
`heat_potential_tightness_uniform_of_exp_bound` are chosen before any particular scenery law is
fixed, using the pointwise and modulus moment bounds for the linearly interpolated heat
potential together with the Kolmogorov continuity criterion `kolmogorovBoundPi_holds` and
`kolmogorovModulusPi_holds`.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

/-- Both compact tightness thresholds are chosen before the scenery law. -/
theorem heat_potential_tightness_uniform_of_exp_bound
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (T : ℝ) (hT : 0 < T)
    (K : Set (ℝ × Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (hKT : K ⊆ Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :
    (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        (∫ z, z ∂ν = 0) → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) → ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ x ∈ K, M < |linInterp d R (Sandpile.scenery d σ) x.1 x.2|}
          ≤ ENNReal.ofReal ε) ∧
      (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        (∫ z, z ∂ν = 0) → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        (∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) → ∀ R : ℝ, 1 ≤ R →
        (Sandpile.centeredMassLaw d ν)
            {σ | ∃ x ∈ K, ∃ y ∈ K, dist x y < δ ∧
              η < |linInterp d R (Sandpile.scenery d σ) x.1 x.2
                - linInterp d R (Sandpile.scenery d σ) y.1 y.2|}
          ≤ ENNReal.ofReal ε) := by
  classical
  let θ : ℝ := 1 / 2
  have hθ0 : 0 < θ := by norm_num [θ]
  have hθ1 : θ < 1 := by norm_num [θ]
  have hHK := Sandpile.External.heatKernelBounds
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hβ0 : (0:ℝ) < min (1 - (d : ℝ) / 4) ((1 - θ) / 4) := lt_min (by linarith) (by linarith)
  set β : ℝ := min (1 - (d : ℝ) / 4) ((1 - θ) / 4) with hβdef
  set p₀ : ℝ := 2 + ((d : ℝ) + 2) / β with hp₀def
  have hp₀ : (2:ℝ) ≤ p₀ := by
    have : (0:ℝ) ≤ ((d : ℝ) + 2) / β := by positivity
    rw [hp₀def]; linarith
  have hp₀0 : (0:ℝ) < p₀ := by linarith
  have hp₀1 : (1:ℝ) ≤ p₀ := by linarith
  have hpβ : p₀ * β = 2 * β + ((d : ℝ) + 2) := by
    rw [hp₀def, add_mul, div_mul_cancel₀ _ hβ0.ne']
  have hq : ((d + 1 : ℕ) : ℝ) < p₀ * β := by
    rw [hpβ]
    push_cast
    linarith
  -- the radius of the compact set
  obtain ⟨L₀, hL₀⟩ := (hK.image continuous_snd).isBounded.subset_closedBall
    (0 : Sandpile.Continuum.Space d)
  have hL : (0:ℝ) ≤ max L₀ 0 := le_max_right _ _
  set L : ℝ := max L₀ 0 with hLdef
  have hKL : ∀ x ∈ K, ‖x.2‖ ≤ L := by
    intro x hx
    have hmem : x.2 ∈ Metric.closedBall (0 : Sandpile.Continuum.Space d) L₀ :=
      hL₀ ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact le_trans hmem (le_max_left _ _)
  have hbox : ∀ x ∈ K, toPi x ∈ Set.Icc (boxLo d L) (boxHi d T L) := by
    intro x hx
    have h1 := hKT hx
    exact toPi_mem_box (Set.mem_Icc.mp (Set.mem_prod.mp h1).1).1
      (Set.mem_Icc.mp (Set.mem_prod.mp h1).1).2 (hKL x hx)
  obtain ⟨Mmod, hMmod, hmod⟩ :=
    exists_pi_moment_modulus hHK hd hd3 hθ0 hθ1 p₀ hp₀ T L hT.le hL
  obtain ⟨Mpt, hMpt, hpt⟩ := exists_pi_one_point_moment hHK hd hd3 p₀ hp₀ T L hT.le
  let C : ℝ := |2 ^ p₀ * (2 * ((p₀ / θ₀) ^ p₀ * K₀))|
  have hC : 0 ≤ C := abs_nonneg _
  have hbound : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      (∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) → resampleMoment ν p₀ ≤ C := by
    intro ν _ hexp hK₀
    exact (resampleMoment_le_of_exp_bound θ₀ K₀ p₀ hθ₀ hp₀1 ν hexp hK₀).2.trans
      (le_abs_self _)
  set MM : ℝ := (Mmod + Mpt) * C + 1 with hMMdef
  have hmomhyp : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      (∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) → ∀ R : ℝ, 1 ≤ R →
      ∀ u ∈ Set.Icc (boxLo d L) (boxHi d T L), ∀ v ∈ Set.Icc (boxLo d L) (boxHi d T L),
        ∫ σ, |piField d R u σ - piField d R v σ| ^ p₀ ∂(Sandpile.centeredMassLaw d ν)
          ≤ MM * dist u v ^ (p₀ * β) := by
    intro ν _ hmean hexp hK₀ R hR u hu v hv
    have hint := integrable_abs_rpow_of_exp_moment ν θ₀ hθ₀ hexp p₀ hp₀0.le
    refine le_trans (hmod ν inferInstance hmean hint R hR u hu v hv) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg dist_nonneg _)
    rw [hMMdef]
    nlinarith [hbound ν hexp hK₀, hMpt.le, hMmod.le]
  have hpthyp : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
      (∫ z, z ∂ν = 0) → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      (∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀) → ∀ R : ℝ, 1 ≤ R →
      ∫ σ, |piField d R (boxLo d L) σ| ^ p₀ ∂(Sandpile.centeredMassLaw d ν) ≤ MM := by
    intro ν _ hmean hexp hK₀ R hR
    have hint := integrable_abs_rpow_of_exp_moment ν θ₀ hθ₀ hexp p₀ hp₀0.le
    refine le_trans (hpt ν inferInstance hmean hint R hR) ?_
    rw [hMMdef]
    nlinarith [hbound ν hexp hK₀, hMpt.le, hMmod.le]
  have hconthyp : ∀ R : ℝ, 1 ≤ R → ∀ σ : Site d → ℝ,
      ContinuousOn (fun u => piField d R u σ) (Set.Icc (boxLo d L) (boxHi d T L)) :=
    fun R hR σ => continuousOn_piField hHK hd hd3 hθ0 hθ1 R hR σ T L hT.le hL
  constructor
  · intro ε hε
    obtain ⟨B, hB⟩ := kolmogorovBoundPi_holds (d + 1) (boxLo d L) (boxHi d T L) p₀ (p₀ * β) MM
      hp₀0 hq ε hε
    refine ⟨B, ?_⟩
    intro ν hν hmean hexp hK₀ R hR
    letI := hν
    have hint := integrable_abs_rpow_of_exp_moment ν θ₀ hθ₀ hexp p₀ hp₀0.le
    refine le_trans (measure_mono ?_)
      (hB (Sandpile.centeredMassLaw d ν) inferInstance (piField d R)
        (fun u => measurable_piField R u)
        (fun u hu v hv => integrable_piField_sub_rpow hd ν hp₀1 hint R T L u v hu hv)
        (hmomhyp ν hmean hexp hK₀ R hR)
        (integrable_piField_rpow hd ν hp₀1 hint R T L (boxLo d L)
          (Set.left_mem_Icc.mpr (boxLo_le_boxHi d L T hT.le hL)))
        (hpthyp ν hmean hexp hK₀ R hR) (hconthyp R hR))
    intro σ hσ
    obtain ⟨x, hx, hlt⟩ := hσ
    refine ⟨toPi x, hbox x hx, ?_⟩
    rwa [piField_toPi]
  · intro ε η hε hη
    obtain ⟨δ, hδ0, hδ⟩ :=
      kolmogorovModulusPi_holds (d + 1) (boxLo d L) (boxHi d T L) p₀ (p₀ * β) MM hp₀0 hq ε η hε hη
    refine ⟨δ, hδ0, ?_⟩
    intro ν hν hmean hexp hK₀ R hR
    letI := hν
    have hint := integrable_abs_rpow_of_exp_moment ν θ₀ hθ₀ hexp p₀ hp₀0.le
    refine le_trans (measure_mono ?_)
      (hδ (Sandpile.centeredMassLaw d ν) inferInstance (piField d R)
        (fun u => measurable_piField R u)
        (fun u hu v hv => integrable_piField_sub_rpow hd ν hp₀1 hint R T L u v hu hv)
        (hmomhyp ν hmean hexp hK₀ R hR) (hconthyp R hR))
    intro σ hσ
    obtain ⟨x, hx, y, hy, hdlt, hlt⟩ := hσ
    refine ⟨toPi x, hbox x hx, toPi y, hbox y hy,
      lt_of_le_of_lt (dist_toPi_le x y) hdlt, ?_⟩
    rwa [piField_toPi, piField_toPi]

end Sandpile.Support
