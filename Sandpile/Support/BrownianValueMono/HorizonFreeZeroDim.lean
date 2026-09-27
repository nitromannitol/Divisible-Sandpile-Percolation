import Sandpile.Support.BrownianValueMono.AffineZeroDim
import Sandpile.Support.StopMeasurable

/-!
# Horizon-freeness of the payoff in dimension zero

`HorizonFreeIncrement` (`Sandpile/Support/ExplHorizon.lean`) says that a fixed admissible
stopping time's payoff does not depend on the horizon it is measured from. In positive dimension
this comes from the backward heat-increment martingale along the motion. In dimension zero the
space `Space 0` is a single point, so the motion cannot move away from its starting point, and
the affine structure of the field (`gaussianPotential_eq_affine_zero_dim`) makes the increment
`Z(T,z,ω) - Z(T - a, z, ω)` equal to `c(ω) · a` for every `a`, independently of `T`: the
`τ`-dependent terms cancel by direct computation, with no martingale theory needed at all.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- **In dimension zero, the payoff of a fixed admissible stopping time does not depend on the
horizon.** The space `Space 0` is a single point, so the motion is forced to stay at its
starting point, and the reward, being exactly affine in time on the strip (samplewise), has
the same increment `c · (T - s)` whichever horizon it is measured from. -/
theorem horizonFreeIncrement_zero_dim {ΩB : Type*} [MeasurableSpace ΩB] {PB : Measure ΩB}
    [IsProbabilityMeasure PB] {z : Space 0} {B : ℝ≥0 → ΩB → Space 0}
    (hBm : ∀ t, StronglyMeasurable (B t)) (h : ℝ → Space 0 → ℝ) (c : ℝ) (s T : ℝ)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (haff : ∀ s' ∈ Set.Icc (0 : ℝ) T, h s' z = s' * c) :
    HorizonFreeIncrement B PB h s T z := by
  intro τ hτ hτs
  have hBz : ∀ b : ΩB, B (τ b) b = z := fun b => Subsingleton.elim _ _
  have hτm : Measurable τ := Sandpile.Continuum.IsBrownianStopping.measurable hτ hBm
  have hτnn : ∀ b, (0 : ℝ) ≤ (τ b : ℝ) := fun b => (τ b).coe_nonneg
  have hτint : Integrable (fun b => (τ b : ℝ)) PB := by
    have hm : AEStronglyMeasurable (fun b => (τ b : ℝ)) PB :=
      (measurable_coe_nnreal_real.comp hτm).aestronglyMeasurable
    apply Integrable.mono' (integrable_const s) hm
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (hτnn b)]
    exact hτs b
  have h1 : ∀ b, h (s - τ b) (B (τ b) b) = s * c - (τ b : ℝ) * c := by
    intro b
    rw [hBz b, haff (s - τ b) ⟨by linarith [hτs b], by linarith [hτnn b, hsT]⟩]
    ring
  have h2 : ∀ b, h (T - τ b) (B (τ b) b) = T * c - (τ b : ℝ) * c := by
    intro b
    rw [hBz b, haff (T - τ b) ⟨by linarith [hτs b, hsT], by linarith [hτnn b]⟩]
    ring
  have h3 : h s z = s * c := haff s ⟨hs0, hsT⟩
  have h4 : h T z = T * c := haff T ⟨hs0.trans hsT, le_refl T⟩
  rw [h3, h4]
  have e1 : (fun b => -h (s - τ b) (B (τ b) b)) = fun b => -(s * c) + (τ b : ℝ) * c := by
    funext b
    rw [h1 b]
    ring
  have e2 : (fun b => -h (T - τ b) (B (τ b) b)) = fun b => -(T * c) + (τ b : ℝ) * c := by
    funext b
    rw [h2 b]
    ring
  rw [e1, e2, integral_add (integrable_const (-(s * c))) (hτint.mul_const c),
    integral_add (integrable_const (-(T * c))) (hτint.mul_const c), integral_const, integral_const]
  simp only [smul_eq_mul, probReal_univ]
  ring

end Sandpile.Continuum
