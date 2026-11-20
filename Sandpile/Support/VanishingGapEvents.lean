import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Events controlled by vanishing expected gaps

If nonnegative integrable gaps have expectations tending to zero, events on
which the gap exceeds a fixed positive threshold have vanishing probability.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

/-- A fixed positive lower bound on a nonnegative gap forces the probability
of the corresponding events to vanish when the gap expectations vanish. -/
theorem Sandpile.Support.tendsto_measure_of_gap_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (gap : ℕ → Ω → ℝ) (hgi : ∀ n, Integrable (gap n) P)
    (hgn : ∀ n ω, 0 ≤ gap n ω)
    (hglim : Tendsto (fun n => ∫ ω, gap n ω ∂P) atTop (𝓝 0))
    (A : ℕ → Set Ω) (ε : ℝ) (hε : 0 < ε)
    (hA : ∀ n ω, ω ∈ A n → ε ≤ gap n ω) :
    Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
  have hbound : ∀ n, P (A n) ≤ ENNReal.ofReal (ε⁻¹ * ∫ ω, gap n ω ∂P) := by
    intro n
    have hi : Integrable (fun ω => ε⁻¹ * gap n ω) P := (hgi n).const_mul _
    have hn : 0 ≤ᵐ[P] fun ω => ε⁻¹ * gap n ω :=
      Eventually.of_forall fun ω => mul_nonneg (inv_nonneg.mpr hε.le) (hgn n ω)
    have hh := hi.measure_le_integral hn (s := A n) (fun ω hω => by
      have hg := hA n ω hω
      have hm := mul_le_mul_of_nonneg_left hg (inv_nonneg.mpr hε.le)
      simpa only [inv_mul_cancel₀ hε.ne'] using hm)
    simpa only [integral_const_mul] using hh
  have hmul : Tendsto (fun n => ε⁻¹ * ∫ ω, gap n ω ∂P) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := ε⁻¹)).mul hglim
  have hlim : Tendsto (fun n => ENNReal.ofReal (ε⁻¹ * ∫ ω, gap n ω ∂P)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hmul
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound
