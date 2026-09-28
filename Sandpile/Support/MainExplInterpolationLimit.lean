import Sandpile.Support.MainExplAssemblyZ
import Sandpile.Support.MainExplContValueMeas
import Sandpile.Support.MainExplInterp
import Sandpile.Support.MainExplOscGeneral
import Sandpile.Support.MainExplWeak

/-! # Lattice-to-interpolation coupling for Theorem 1.3(i)(b)

Passage from lattice odometer couplings to the multilinear interpolation in
Theorem 1.3(i)(b). The interpolation error is bounded by the oscillation in one
mesh cell, uniformly over a compact set.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile.Continuum

namespace Sandpile.Continuum

variable {d : ℕ}

/-- An interpolation error is bounded by the errors at the corners of its cell. -/
theorem abs_multilinearInterp_sub_le_corners (R : ℝ) (f : Site d → ℝ)
    (z : Space d) (c M : ℝ)
    (hf : ∀ e : Fin d → Bool,
      |f (fun i => ⌊R * z i⌋ + if e i then 1 else 0) - c| ≤ M) :
    |multilinearInterp R f z - c| ≤ M := by
  simpa only [multilinearInterp_sub, multilinearInterp_const] using
    abs_multilinearInterp_le_corners R (fun x => f x - c) z M hf

/-- A compact spatial bound confines the lower corner to a lattice box. -/
theorem abs_floor_scaled_coord_le (R : ℝ) (hR : 1 ≤ R) (ρ : ℝ)
    (z : Space d) (hz : ‖z‖ ≤ ρ) (i : Fin d) :
    |⌊R * z i⌋| ≤ ⌈R * (ρ + 1)⌉ := by
  have hRp : 0 ≤ R := le_trans zero_le_one hR
  have hzi := abs_le.mp ((Sandpile.Support.abs_coord_le_norm z i).trans hz)
  have hfl := Int.floor_le (R * z i)
  have hfl' := Int.lt_floor_add_one (R * z i)
  have hceil := Int.le_ceil (R * (ρ + 1))
  have hlo := mul_le_mul_of_nonneg_left hzi.1 hRp
  have hhi := mul_le_mul_of_nonneg_left hzi.2 hRp
  have hc : |(⌊R * z i⌋ : ℝ)| ≤ (⌈R * (ρ + 1)⌉ : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith
  exact_mod_cast hc

end Sandpile.Continuum

universe u v

namespace Sandpile

/-- Uniformly on a compact set, interpolation and the lower mesh value differ
by a quantity tending to zero in probability. -/
theorem exists_interpolation_mesh_gap
    (hLocalCLT : Sandpile.External.LocalCLT) (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (K : Set (Space d)) (hK : IsCompact K)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      centeredMassLaw d ν {σ | ∃ z ∈ K,
        ε < |multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
          R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋)|}
        ≤ ENNReal.ofReal δ := by
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  obtain ⟨R₀, hR₀, hgap⟩ := exists_odometer_cell_oscillation hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT (ρ + 1) (by positivity) ε δ hε hδ
  refine ⟨max 1 R₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  refine (measure_mono ?_).trans (hgap R ((le_max_right _ _).trans hR))
  rintro σ ⟨z, hz, hbad⟩
  by_contra hgood
  have hzn : ‖z‖ ≤ ρ := by
    simpa only [mem_closedBall, dist_zero_right] using hKρ hz
  have hcorner : ∀ e : Fin d → Bool,
      |R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊
          (fun i => ⌊R * z i⌋ + if e i then 1 else 0) -
        R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋)| ≤ ε := by
    intro e
    apply le_of_not_gt
    intro he
    apply hgood
    refine ⟨(fun i => ⌊R * z i⌋), (fun i => if e i then 1 else 0),
      (fun i => abs_floor_scaled_coord_le R hR1 ρ z hzn i), ?_, ?_⟩
    · intro i
      change |(if e i then (1 : ℤ) else 0)| ≤ 1
      split_ifs <;> norm_num
    · have heq : (d : ℝ) / 2 - 2 = -(2 - (d : ℝ) / 2) := by ring
      simpa only [heq, odometer_eq_odometerOf, Pi.add_def] using he
  exact (not_lt_of_ge (abs_multilinearInterp_sub_le_corners R _ z _ ε hcorner)) hbad

/-- The compact coupling estimate for the multilinearly interpolated odometer. -/
theorem dlt4_interpolated_coupling_of_version
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type v) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d =>
        Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |multilinearInterp R
                  (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ y) u
                - Sandpile.Continuum.brownianValue (B u) PB
                    (fun t y => Z t y p.2)
                    T u|}
          ≤ ENNReal.ofReal δ := by
  obtain ⟨Rm, hRm, hm⟩ := exists_interpolation_mesh_gap hLocalCLT d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp T hT K hK (ε / 2) (δ / 2) (by positivity) (by positivity)
  obtain ⟨Rc, hRc, hc⟩ := dlt4_scaling_of_version hLocalCLT hStab d hd hd3 ν
    hmean hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod ΩB PB B hB hBc hBm K hK T hT
    hZcont hZgrow (ε / 2) (δ / 2) (by positivity) (by positivity)
  refine ⟨max Rm Rc, lt_of_lt_of_le hRm (le_max_left _ _), ?_⟩
  intro R hR
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hc R ((le_max_right _ _).trans hR)
  refine ⟨P, hP, hPf, hPs, ?_⟩
  let E : Set (Site d → ℝ) := {σ | ∃ z ∈ K,
    ε / 2 < |multilinearInterp R
      (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ y) z -
      R ^ (-(2 - (d : ℝ) / 2)) * odometer σ ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋)|}
  let F : Set ((Site d → ℝ) × ΩW) := {p | ∃ z ∈ K,
    ε / 2 < |R ^ (-(2 - (d : ℝ) / 2)) *
      odometerOf (scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋) -
      brownianValue (B z) PB (fun t y => Z t y p.2) T z|}
  have hsub : {p : (Site d → ℝ) × ΩW | ∃ z ∈ K,
    ε < |multilinearInterp R
      (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ y) z -
      brownianValue (B z) PB (fun t y => Z t y p.2) T z|} ⊆ (Prod.fst ⁻¹' E) ∪ F := by
    rintro p ⟨z, hz, hlarge⟩
    by_cases he : p.1 ∈ E
    · exact Or.inl he
    by_cases hf : p ∈ F
    · exact Or.inr hf
    exfalso
    have h₁ : |multilinearInterp R
        (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ y) z -
        R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋)| ≤ ε / 2 :=
      le_of_not_gt (fun h => he ⟨z, hz, h⟩)
    have h₂ : |R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋) -
        brownianValue (B z) PB (fun t y => Z t y p.2) T z| ≤ ε / 2 := by
      rw [odometer_eq_odometerOf]
      exact le_of_not_gt (fun h => hf ⟨z, hz, h⟩)
    have htri := abs_sub_le
      (multilinearInterp R (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ y) z)
      (R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ (fun i => ⌊R * z i⌋))
      (brownianValue (B z) PB (fun t y => Z t y p.2) T z)
    linarith
  have hPE : P (Prod.fst ⁻¹' E) ≤ centeredMassLaw d ν E := by
    rw [← hPf]
    exact Measure.le_map_apply measurable_fst.aemeasurable E
  calc P _ ≤ P ((Prod.fst ⁻¹' E) ∪ F) := measure_mono hsub
    _ ≤ P (Prod.fst ⁻¹' E) + P F := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      add_le_add (hPE.trans (hm R ((le_max_left _ _).trans hR))) hbad
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Finite-dimensional convergence of the interpolated odometer to the Brownian value. -/
theorem brownian_scaling_fdd_of_localCLT
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
    (T : ℝ) (hT : 0 < T) :
    (∀ (m : ℕ) (x : Fin m → Sandpile.Continuum.Space d),
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (j : Fin m) =>
            Sandpile.Continuum.multilinearInterp R
              (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y) (x j))
          atTop
          (fun (ω : Ω) (j : Fin m) =>
            Sandpile.Continuum.brownianValue (B (x j)) P'
              (fun t y => Z t y ω)
              T (x j))
          (fun _ => Sandpile.centeredMassLaw d ν) P) := by
  intro m x
  have hZm : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
      AEMeasurable (Z q.1 q.2) P := by
    intro q hq
    exact (measurable_const.mul (hW.meas _
      (Support.memLp_greenTimeBM hd hd3 hq.1.1 q.2))).aemeasurable.congr
      (hZmod q.1 q.2).symm
  have hYm : AEMeasurable (fun ω j => brownianValue (B (x j)) P'
      (fun t y => Z t y ω) T (x j)) P := by
    apply aemeasurable_pi_lambda
    intro j
    exact Support.aemeasurable_brownianValue_of_growth (B (x j)) P' (x j) (hB (x j))
      (fun t => (hBm (x j) t).measurable) (hBc (x j)) P Z T hT hZm
      (hZcont T hT) (hZgrow T hT)
  refine tendstoInDistribution_of_coupling (centeredMassLaw d ν) P _ _ ?_ hYm ?_
  · intro R
    exact (measurable_pi_lambda _ fun j => measurable_multilinearInterp_apply R _ (x j)
      (measurable_rescaled_odometer_field T R)).aemeasurable
  · intro ε δ hε hδ
    obtain ⟨R₀, hR₀, hc⟩ := dlt4_interpolated_coupling_of_version hLocalCLT hStab d hd hd3 ν
      hmean hvar hvar' θ₀ hθ₀ hexp Ω P W hW Z hZmod Ω' P' B hB hBc hBm
      (Set.range x) (Set.finite_range x).isCompact T hT (hZcont T hT) (hZgrow T hT) ε δ hε hδ
    refine ⟨R₀, ?_⟩
    intro R hR
    obtain ⟨Q, hQ, hQf, hQs, hbad⟩ := hc R hR
    refine ⟨Q, hQ, hQf, hQs, (measure_mono ?_).trans hbad⟩
    intro p hp
    by_contra hn
    have hle : dist
        (fun j => multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * odometer p.1 ⌊T * R ^ 2⌋₊ y) (x j))
        (fun j => brownianValue (B (x j)) P' (fun t y => Z t y p.2) T (x j)) ≤ ε := by
      apply (dist_pi_le_iff hε.le).mpr
      intro j
      rw [Real.dist_eq]
      exact le_of_not_gt (fun h => hn ⟨x j, ⟨j, rfl⟩, h⟩)
    exact not_lt_of_ge hle hp

end Sandpile
