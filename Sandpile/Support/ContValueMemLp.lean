import Sandpile.Support.MeanAValue
import Sandpile.Support.ContLawTransfer
import Sandpile.Support.ContMeanAsymptotic

/-!
# Square integrability of the continuum value by transfer of law

Square integrability of the continuum value at a general `(T,x)` from the law identity of
clause 1 of `prop:continuum-value-selfsimilar` and square integrability at `(1,0)`. The law
identity `𝒰(T,x) =^d T^β 𝒰(1,0)` transfers `MemLp` across the map, and `MemLp.comp_of_map`
pulls it back along the measurable value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- Square integrability of the continuum value at `(T,x)` from the law identity of
clause 1, square integrability at `(1,0)`, and measurability of the value. -/
theorem memLp_continuumValue_T {ΩW ΩB : Type*} [MeasurableSpace ΩW] [MeasurableSpace ΩB]
    (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ)
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) (PW : Measure ΩW)
    (T : ℝ) (x : Space d) (β : ℝ)
    (h1 : MemLp (fun ω => continuumValue d Z B PB 1 0 ω) 2 PW)
    (hf : AEMeasurable (fun ω => continuumValue d Z B PB T x ω) PW)
    (hmap : PW.map (fun ω => continuumValue d Z B PB T x ω)
      = PW.map (fun ω => T ^ β * continuumValue d Z B PB 1 0 ω)) :
    MemLp (fun ω => continuumValue d Z B PB T x ω) 2 PW := by
  have h2 : MemLp (fun ω => T ^ β * continuumValue d Z B PB 1 0 ω) 2 PW := h1.const_mul (T ^ β)
  have h3 : MemLp (fun y : ℝ => y) 2 (PW.map (fun ω => continuumValue d Z B PB T x ω)) := by
    rw [hmap]
    exact (memLp_map_measure_iff (g := fun y : ℝ => y)
      (f := fun ω => T ^ β * continuumValue d Z B PB 1 0 ω)
      measurable_id.aestronglyMeasurable (h1.const_mul (T ^ β)).aemeasurable).mpr h2
  simpa only [Function.comp_def, id_eq] using h3.comp_of_map hf

end Sandpile.Support
