/-
The `p`-th moment of a linear functional of an i.i.d. scenery, in terms of the
`ℓ²` norm of its coefficient vector.

The first conjunct of `lem-weighted-exp-conc` prices the `p`-th moment of a
functional that is Lipschitz in each coordinate with constants `ℓ` by the two
sums `∑ ℓ_i^2` and `∑ ℓ_i^p`.  For the linear functional `ξ ↦ ∑ c_i ξ_i` the
constants are `ℓ_i = |c_i|`, the first sum is the squared `ℓ²` norm of `c`, and
the second is dominated by the same quantity because the `ℓ^p` norm decreases in
`p`.  So the `p`-th moment of the linear functional is at most a constant times
the `ℓ²` norm of `c`, which is what the tightness clause of
`prop:dlt4-heat-potential-invariance` asks of the increment of the interpolated
field.
-/
import Sandpile.Frozen.WeightedExpConcentration
import Sandpile.Support.FiniteCoord
import Sandpile.Support.SceneryBridge
import Sandpile.Support.ContCoeffL2
import LatticeProb.Support.ContSums

open LatticeProb

open MeasureTheory ProbabilityTheory
open Sandpile.Frozen.HeatPotentialInvariance

namespace Sandpile.Support

variable {d : ℕ}

/-- **(β) The `p`-th moment of a linear functional of an i.i.d. scenery.**  The
first conjunct of `lem-weighted-exp-conc` applied to `ξ ↦ ∑ c_i ξ_i`, whose
coordinate Lipschitz constants are `|c_i|`: the square sum is the squared `ℓ²`
norm of `c` and the `p`-th sum is at most its `p`-th power, so the moment is a
constant multiple of the `ℓ²` norm. -/
theorem exists_moment_linear_pi (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν → ∀ c : Fin N → ℝ,
        (∫ ξ, |(∑ i, c i * ξ i)
              - ∫ η, (∑ i, c i * η i) ∂(Measure.pi fun _ : Fin N => ν)| ^ p
            ∂(Measure.pi fun _ : Fin N => ν)) ^ (1 / p)
          ≤ C * Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2) := by
  classical
  obtain ⟨C₀, hC₀, hmom⟩ := Sandpile.Frozen.weighted_exp_concentration.1 p hp
  have hp0 : (0:ℝ) < p := by linarith
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro N ν hν hint c
  haveI := hν
  have hS0 : (0:ℝ) ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSnn : (0:ℝ) ≤ Real.sqrt (∑ i, c i ^ 2) := Real.sqrt_nonneg _
  have hm0 : (0:ℝ) ≤ Sandpile.resampleMoment ν p := LatticeProb.pairMoment_nonneg ν p
  have hmr : (0:ℝ) ≤ Sandpile.resampleMoment ν p ^ (1 / p) := Real.rpow_nonneg hm0 _
  have hF : Measurable (fun ξ : Fin N → ℝ => ∑ i, c i * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have h1p : (1 / p : ℝ) ≠ 0 := by positivity
  by_cases hc : ∀ i, c i = 0
  · have hz : ∀ ξ : Fin N → ℝ, ∑ i, c i * ξ i = 0 := fun ξ =>
      Finset.sum_eq_zero fun i _ => by rw [hc i]; ring
    have hS : ∑ i, c i ^ 2 = 0 := Finset.sum_eq_zero fun i _ => by rw [hc i]; ring
    have hzero : (∫ ξ : Fin N → ℝ, |(∑ i, c i * ξ i)
        - ∫ η, (∑ i, c i * η i) ∂(Measure.pi fun _ : Fin N => ν)| ^ p
        ∂(Measure.pi fun _ : Fin N => ν)) = 0 := by
      simp only [hz, integral_zero, sub_zero, abs_zero]
      rw [Real.zero_rpow (ne_of_gt hp0), integral_zero]
    rw [hS, Real.sqrt_zero, mul_zero, hzero, Real.zero_rpow h1p]
  · rw [not_forall] at hc
    obtain ⟨i₀, hi₀⟩ := hc
    have hne : ∃ i, |c i| ≠ 0 := ⟨i₀, by simpa using hi₀⟩
    have hkey := hmom N (fun _ => ν) (fun _ => hν) (fun ξ => ∑ i, c i * ξ i) hF
      (fun i => |c i|) (fun i => abs_nonneg _) hne
      (fun ξ j y => abs_linear_sub_update_le c ξ j y) (fun _ => hint)
    refine le_trans hkey ?_
    have hfirst : (∑ i, |c i| ^ 2 * Sandpile.resampleMoment ν p ^ (2 / p)) ^ (1 / 2 : ℝ)
        = Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2) := by
      have hsum : ∑ i, |c i| ^ 2 * Sandpile.resampleMoment ν p ^ (2 / p)
          = (∑ i, c i ^ 2) * Sandpile.resampleMoment ν p ^ (2 / p) := by
        rw [← Finset.sum_mul]
        exact congrArg (· * _) (Finset.sum_congr rfl fun i _ => sq_abs (c i))
      rw [hsum, Real.mul_rpow hS0 (Real.rpow_nonneg hm0 _), ← Real.rpow_mul hm0]
      have hexp : 2 / p * (1 / 2 : ℝ) = 1 / p := by field_simp
      rw [hexp, ← Real.sqrt_eq_rpow]
      ring
    have hsecond : (∑ i, |c i| ^ p * Sandpile.resampleMoment ν p) ^ (1 / p)
        ≤ Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2) := by
      have hsum : ∑ i, |c i| ^ p * Sandpile.resampleMoment ν p
          = (∑ i, |c i| ^ p) * Sandpile.resampleMoment ν p := by rw [← Finset.sum_mul]
      have hle : (∑ i, |c i| ^ p) * Sandpile.resampleMoment ν p
          ≤ Real.sqrt (∑ i, c i ^ 2) ^ p * Sandpile.resampleMoment ν p :=
        mul_le_mul_of_nonneg_right (sum_abs_rpow_le p hp c) hm0
      have hnn : (0:ℝ) ≤ (∑ i, |c i| ^ p) * Sandpile.resampleMoment ν p :=
        mul_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hm0
      rw [hsum]
      refine le_trans (Real.rpow_le_rpow hnn hle (by positivity)) ?_
      rw [Real.mul_rpow (Real.rpow_nonneg hSnn _) hm0, ← Real.rpow_mul hSnn]
      have hexp : p * (1 / p : ℝ) = 1 := by field_simp
      rw [hexp, Real.rpow_one]
      ring_nf
      exact le_rfl
    rw [hfirst]
    have := add_le_add (le_refl (Sandpile.resampleMoment ν p ^ (1 / p)
      * Real.sqrt (∑ i, c i ^ 2))) hsecond
    calc C₀ * (Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2)
          + (∑ i, |c i| ^ p * Sandpile.resampleMoment ν p) ^ (1 / p))
        ≤ C₀ * (Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2)
          + Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hC₀.le
      _ = 2 * C₀ * Sandpile.resampleMoment ν p ^ (1 / p) * Real.sqrt (∑ i, c i ^ 2) := by ring

/-- Reading `N` distinct sites of the scenery of a centred mass field carries
its law to the `N`-fold product of the one-site law. -/
theorem measurePreserving_scenery_pick (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    {N : ℕ} (e : Fin N → Site d) (he : Function.Injective e) :
    MeasurePreserving (fun σ : Site d → ℝ => fun i => Sandpile.scenery d σ (e i))
      (Sandpile.centeredMassLaw d ν) (Measure.pi fun _ : Fin N => ν) := by
  have h1 : MeasurePreserving (Sandpile.scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨Sandpile.measurable_scenery d, Sandpile.map_scenery_centeredMassLaw d ν hd⟩
  exact (LatticeProb.measurePreserving_pick _ ν e he).comp h1

/-- Transport of an integral along the reading of `N` distinct sites of the
scenery. -/
theorem integral_scenery_pick (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d) {N : ℕ}
    (e : Fin N → Site d) (he : Function.Injective e) (G : (Fin N → ℝ) → ℝ)
    (hG : AEStronglyMeasurable G (Measure.pi fun _ : Fin N => ν)) :
    ∫ σ, G (fun i => Sandpile.scenery d σ (e i)) ∂(Sandpile.centeredMassLaw d ν)
      = ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin N => ν) := by
  have h := measurePreserving_scenery_pick ν hd e he
  have hmap : (Sandpile.centeredMassLaw d ν).map
      (fun σ : Site d → ℝ => fun i => Sandpile.scenery d σ (e i))
      = Measure.pi fun _ : Fin N => ν := h.map_eq
  have hres := integral_map (μ := Sandpile.centeredMassLaw d ν)
    (φ := fun σ : Site d → ℝ => fun i => Sandpile.scenery d σ (e i)) (f := G)
    h.measurable.aemeasurable (by rwa [hmap])
  rw [hmap] at hres
  exact hres.symm

/-- **(β) The `p`-th moment of the increment of the interpolated rescaled field
under the centred mass law**, in terms of the `ℓ²` norm of the increment of its
coefficient vector.  The field is the linear functional of the scenery with
coefficients `interpCoeff`, the scenery of a centred mass field is an i.i.d.
field, and reading the finitely many sites the two cells reach carries its law
to a product of the one-site law. -/
theorem exists_moment_linInterp_sub_le (hd : 1 ≤ d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν →
      ∀ (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d) (s : Finset (Site d)),
        (∀ ε : Fin d → Bool,
          Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
            (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) →
        (∀ ε : Fin d → Bool,
          Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0)
            (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s) →
        (∫ σ, |(linInterp d R (Sandpile.scenery d σ) r w
                - linInterp d R (Sandpile.scenery d σ) r' w')
              - ∫ τ, (linInterp d R (Sandpile.scenery d τ) r w
                  - linInterp d R (Sandpile.scenery d τ) r' w')
                ∂(Sandpile.centeredMassLaw d ν)| ^ p ∂(Sandpile.centeredMassLaw d ν)) ^ (1 / p)
          ≤ C * Sandpile.resampleMoment ν p ^ (1 / p)
            * Real.sqrt (∑' y : Site d,
                (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2) := by
  classical
  obtain ⟨C, hC, hmom⟩ := exists_moment_linear_pi p hp
  refine ⟨C, hC, ?_⟩
  intro ν hν hint R r r' w w' s hps hqs
  haveI := hν
  have hrep : ∀ σ : Site d → ℝ,
      linInterp d R (Sandpile.scenery d σ) r w - linInterp d R (Sandpile.scenery d σ) r' w'
        = ∑ i : Fin s.card,
            (interpCoeff d R r w (Sandpile.siteEnum s i)
              - interpCoeff d R r' w' (Sandpile.siteEnum s i))
            * Sandpile.scenery d σ (Sandpile.siteEnum s i) := by
    intro σ
    rw [linInterp_eq_sum R r (Sandpile.scenery d σ) w hps,
      linInterp_eq_sum R r' (Sandpile.scenery d σ) w' hqs, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmeas : Measurable (fun ξ : Fin s.card → ℝ =>
      ∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
        - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i) :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hmean : (∫ τ, (linInterp d R (Sandpile.scenery d τ) r w
        - linInterp d R (Sandpile.scenery d τ) r' w') ∂(Sandpile.centeredMassLaw d ν))
      = ∫ η, (∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * η i)
          ∂(Measure.pi fun _ : Fin s.card => ν) := by
    simp only [hrep]
    exact integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
      hmeas.aestronglyMeasurable
  have hmeas2 : Measurable (fun ξ : Fin s.card → ℝ =>
      |(∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
          - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i)
        - ∫ η, (∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
            - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * η i)
            ∂(Measure.pi fun _ : Fin s.card => ν)| ^ p) :=
    ((hmeas.sub measurable_const).abs).pow_const p
  have hlhs : (∫ σ, |(linInterp d R (Sandpile.scenery d σ) r w
                - linInterp d R (Sandpile.scenery d σ) r' w')
              - ∫ τ, (linInterp d R (Sandpile.scenery d τ) r w
                  - linInterp d R (Sandpile.scenery d τ) r' w')
                ∂(Sandpile.centeredMassLaw d ν)| ^ p ∂(Sandpile.centeredMassLaw d ν))
      = ∫ ξ, |(∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
            - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * ξ i)
          - ∫ η, (∑ i, (interpCoeff d R r w (Sandpile.siteEnum s i)
              - interpCoeff d R r' w' (Sandpile.siteEnum s i)) * η i)
              ∂(Measure.pi fun _ : Fin s.card => ν)| ^ p
          ∂(Measure.pi fun _ : Fin s.card => ν) := by
    rw [hmean]
    simp only [hrep]
    exact integral_scenery_pick ν hd (Sandpile.siteEnum s) (Sandpile.siteEnum_injective s) _
      hmeas2.aestronglyMeasurable
  have hsum : ∑ i : Fin s.card, (interpCoeff d R r w (Sandpile.siteEnum s i)
      - interpCoeff d R r' w' (Sandpile.siteEnum s i)) ^ 2
      = ∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2 := by
    rw [Sandpile.sum_siteEnum s
      fun z => (interpCoeff d R r w z - interpCoeff d R r' w' z) ^ 2]
    exact (tsum_coeffDiff_sq R r r' w w' hps hqs).symm
  rw [hlhs, ← hsum]
  exact hmom s.card ν hν hint _

end Sandpile.Support
