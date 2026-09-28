import Sandpile.Support.ExplBallSplit

/-!
# Ball localization for the Gaussian heat potential

`lem:brownian-ball-localization` (`sandpile.tex:1647-1658`) for the Gaussian heat potential
`Z` of `eq:dlt4-linear-gaussian-potential`, in the shape of the frozen statement of the node
(`brownian_ball_localization_gaussian`).

The field of the lemma is `Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))`, which is
`gaussianPotential d ν2 W` at a frozen sample point of the white noise; the value `𝒰_Z`
averages over the Brownian motion only (`sandpile.tex:970-974`), so the inequality is an
inequality between two functions of that sample point and is stated almost surely in it.

Two hypotheses are carried here that the frozen statement does not carry, and that the
paper's proof of the lattice analogue needs: the motion has continuous paths for every
sample point, and the per-point bundle `BallLocalizationInput`, whose only substantive
field is the strong Markov step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- `𝒰_h(T,u) ≥ 0` for a motion that starts at `u` only almost surely. -/
theorem brownianValue_nonneg_ae (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T : ℝ) (hT : 0 ≤ T) (u : Space d)
    (hstart : ∀ᵐ ω ∂P, B 0 ω = u) (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    0 ≤ brownianValue B P h T u :=
  brownianValue_nonneg B P h T u (neg_le_brownianDiscount_ae B P h T hT u hstart hbdd)

/-- The bundle of `lem:brownian-ball-localization` needs only three of its four fields: the
boundedness of the localized attainable set follows from that of the full one. -/
theorem BallLocalizationInput.of (B : Space d → ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A : ℝ) (K : Set (Space d)) (u : Space d)
    (hFull : BddAbove (stoppingPayoffs (B u) P h T))
    (hFar : BddAbove (farValues B P h T A K))
    (hStep : BallExcessStep (B u) P h T A u (sSup (farValues B P h T A K))) :
    BallLocalizationInput B P h T A K u :=
  ⟨hFull, bddAbove_ballStoppingPayoffs (B u) P h T A u hFull, hFar, hStep⟩

/-- **Ball localization of the Brownian value for the Gaussian heat potential.**  The
conclusion of `lem:brownian-ball-localization` (`sandpile.tex:1653-1657`), character for
character as the node's frozen statement writes it, from the strong Markov step and the
continuity of the paths of the motion.  The value is evaluated at a field `Z` that is a
modification of the Gaussian heat potential, as fixed at `sandpile.tex:1019-1021`. -/
theorem brownian_ball_localization_gaussian (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d),
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW)
        (_W : (Space d → ℝ) → ΩW → ℝ) (_ν2 : ℝ),
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
        (∀ᵐ ω ∂PW, ∀ u ∈ K, BallLocalizationInput B PB
          (fun t z => Z t z ω) T A K u) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        brownianValue (B u) PB (fun t z => Z t z ω) T u -
            brownianValueBall (B u) PB (fun t z => Z t z ω) T A u ≤
          C * Real.exp (-(c * A ^ 2 / T)) *
            sSup {v : ℝ | ∃ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) ∧
              v = brownianValue (B z) PB
                (fun t x => Z t x ω) T z} := by
  obtain ⟨C, c, hC, hc, hmain⟩ := ball_localization_of_input d
  refine ⟨C, c, hC, hc, ?_⟩
  intro T hT A hA K ΩW mΩW PW _W _ν2 ΩB mΩB PB hPB B hBrown hcont Z hinput
  filter_upwards [hinput] with ω hω
  intro u hu
  exact hmain T hT A hA K ΩB PB B hBrown hcont
    (fun t z => Z t z ω) u hu (hω u hu)

end Sandpile.Continuum
