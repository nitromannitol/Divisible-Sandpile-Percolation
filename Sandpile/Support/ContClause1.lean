/-
Clause 1 of `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`) from the
two transfers the continuous modification buys.

The clause asks for a modification `U` of the value which is measurable at each
`(T,x)` and whose law scales.  The modification is the measurable representative
`AEMeasurable.mk` of the value, which exists as soon as the value is almost
everywhere measurable; the law then transfers along the almost-sure equality.
-/
import Sandpile.Support.MeanAValue
import Sandpile.Support.ContValueMeasurable
import Sandpile.Support.ContValueTransfer

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- **Clause 1 of `prop:continuum-value-selfsimilar` from the two transfers.**  If
the value is almost everywhere measurable in the field's sample point and its law
scales, then there is a measurable modification `U` of the value whose law scales. -/
theorem clause1_of_transfers {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (ν2 : ℝ) (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (_hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (_hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (_hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    (hmeas : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB T x ω) PW)
    (hlaw : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      PW.map (fun ω => continuumValue d Z B PB T x ω)
        = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω)) :
    (∃ U : ℝ → Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω => continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) := by
  refine ⟨fun T x => if h : 0 < T then
      AEMeasurable.mk (fun ω => continuumValue d Z B PB T x ω) (hmeas T h x)
    else fun _ => 0, ?_, ?_⟩
  · intro T hT x
    simp only [dif_pos hT]
    exact ⟨AEMeasurable.measurable_mk _,
      (AEMeasurable.ae_eq_mk (f := fun ω => continuumValue d Z B PB T x ω)
        (hmeas T hT x)).symm⟩
  · intro T hT x
    simp only [dif_pos hT, dif_pos (by norm_num : (0:ℝ) < 1)]
    have h1 : (fun ω => continuumValue d Z B PB T x ω)
        =ᵐ[PW] fun ω => AEMeasurable.mk (fun ω => continuumValue d Z B PB T x ω)
          (hmeas T hT x) ω :=
      AEMeasurable.ae_eq_mk (f := fun ω => continuumValue d Z B PB T x ω)
        (hmeas T hT x)
    have h2 : (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω)
        =ᵐ[PW] fun ω => T ^ ((4 - (d : ℝ)) / 4) *
          AEMeasurable.mk (fun ω => continuumValue d Z B PB 1 0 ω)
            (hmeas 1 (by norm_num) 0) ω := by
      filter_upwards [AEMeasurable.ae_eq_mk (f := fun ω => continuumValue d Z B PB 1 0 ω)
        (hmeas 1 (by norm_num) 0)] with ω hω
      rw [hω]
    calc Measure.map (AEMeasurable.mk (fun ω => continuumValue d Z B PB T x ω)
            (hmeas T hT x)) PW
        = Measure.map (fun ω => continuumValue d Z B PB T x ω) PW :=
          (MeasureTheory.Measure.map_congr h1).symm
      _ = Measure.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) *
            continuumValue d Z B PB 1 0 ω) PW := hlaw T hT x
      _ = Measure.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) *
            AEMeasurable.mk (fun ω => continuumValue d Z B PB 1 0 ω)
              (hmeas 1 (by norm_num) 0) ω) PW :=
          MeasureTheory.Measure.map_congr h2

/-- **Clause 1 of `prop:continuum-value-selfsimilar` from the two transfers, with
the measurability hypothesis discharged by the continuous modification.**  This is
`clause1_of_transfers` with the almost-everywhere measurability of the value supplied
by the continuous version of the field. -/
theorem clause1_of_continuous {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (ν2 : ℝ) (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    (hmeas : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB T x ω) PW)
    (hlaw : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      PW.map (fun ω => continuumValue d Z B PB T x ω)
        = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω)) :
    (∃ U : ℝ → Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω => continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) :=
  clause1_of_transfers d ν2 W PW hW Z hZmod hZcont B PB hmeas hlaw

/-- **Clause 1 of `prop:continuum-value-selfsimilar` from the continuity of the
modification.**  This is `clause1_of_transfers` with the two hypotheses the paper's
route supplies: the modification is almost surely continuous on `[0,T] × ℝ^d`, and the
law of the value scales. -/
theorem clause1_of_continuity {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (ν2 : ℝ) (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (hW : IsWhiteNoise d W PW)
    (Z : ℝ → Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Space d),
      Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))))
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    (hmeas : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      AEMeasurable (fun ω => continuumValue d Z B PB T x ω) PW)
    (hlaw : ∀ T : ℝ, 0 < T → ∀ x : Space d,
      PW.map (fun ω => continuumValue d Z B PB T x ω)
        = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * continuumValue d Z B PB 1 0 ω)) :
    (∃ U : ℝ → Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω => continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) :=
  clause1_of_transfers d ν2 W PW hW Z hZmod hZcont B PB hmeas hlaw

end Sandpile.Support
