/-
Two facts about the Brownian optimal-stopping value that the proof of
Theorem 1.3(i)(b) and the localization lemma need, and which do not depend on any
filtration: the gap between two values built from close rewards, and the
monotonicity of the value in its horizon.

`abs_brownianDiscount_sub_le` is the Brownian half of the sentence "the analogous
Brownian estimate holds" at `sandpile.tex:1922`: a bound on the payoff gap that is
uniform over admissible stopping times bounds the gap between the two suprema.  It
is the exact counterpart of `Sandpile.abs_stoppingSup_sub_le`.

`brownianValue_mono_horizon` is the monotonicity `𝒰_h(t,z) ≤ 𝒰_h(T,z)` for `t ≤ T`
that the right-hand side of `lem:brownian-ball-localization`
(`sandpile.tex:1653-1657`) uses and that the paper never states.  In the lattice
lemma the monotonicity is structural, because `u_t(x)` is a supremum over a family
of stopping times that grows with `t`; in the continuum it is NOT, because
`𝒰_h(t,x) = h(t,x) + sup_{τ ≤ t} E_x[-h(t-τ,B_τ)]` (`sandpile.tex:1071-1075`)
changes both the family of `τ` and the time index of the field when `t` changes.
What makes it true is that the PAYOFF of a fixed admissible `τ` does not depend on
the horizon, and that is `HorizonFreeIncrement` below.  Given it, the monotonicity
is exactly the growth of the family, and that is proved here.

For the field `Z` of `eq:dlt4-linear-gaussian-potential` the horizon-freeness is
the occupation-density identity
`g_t^{BM}(x,y) - E_x g_{t-τ}^{BM}(B_τ,y) = E_x L_τ(y)`, whose right-hand side does
not mention `t`; in the Chapman-Kolmogorov form,
`E_x p_{t-τ}^{BM}(B_τ,y) = p_t^{BM}(x,y)`, so the `t`-derivative of the increment
vanishes.  At a deterministic time that is Chapman-Kolmogorov; at a stopping time
it is the strong Markov property, which `Sandpile.Continuum.IsBrownian` does not
supply.  So the hypothesis is stated and used, not assumed away: everything that
does not need the strong Markov property is proved.
-/
import Sandpile.Support.ExplBallLocal

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- Two Brownian discounts built from rewards whose payoffs differ by at most `E` differ
by at most `E`.  The Brownian half of the cutoff-error step of `sandpile.tex:1908-1922`. -/
theorem abs_brownianDiscount_sub_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h h' : ℝ → Space d → ℝ) (T E : ℝ) (hT : 0 ≤ T)
    (hbdd : BddAbove (stoppingPayoffs B P h T))
    (hbdd' : BddAbove (stoppingPayoffs B P h' T))
    (hgap : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      |(∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) - ∫ ω, -h' (T - τ ω) (B (τ ω) ω) ∂P| ≤ E) :
    |brownianDiscount B P h T - brownianDiscount B P h' T| ≤ E := by
  have hmem : ∀ k : ℝ → Space d → ℝ,
      (∫ ω, -k (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P) ∈ stoppingPayoffs B P k T := fun k =>
    ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT, rfl⟩
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2 (csSup_le ⟨_, hmem h⟩ ?_)
    rintro a ⟨τ, hτ, hτT, rfl⟩
    have h1 := hgap τ hτ hτT
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ ω, -h' (T - τ ω) (B (τ ω) ω) ∂P) ≤ brownianDiscount B P h' T :=
      le_csSup hbdd' ⟨τ, hτ, hτT, rfl⟩
    linarith [h1.1]
  · refine sub_le_iff_le_add.2 (csSup_le ⟨_, hmem h'⟩ ?_)
    rintro a ⟨τ, hτ, hτT, rfl⟩
    have h1 := hgap τ hτ hτT
    rw [abs_sub_le_iff] at h1
    have h2 : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) ≤ brownianDiscount B P h T :=
      le_csSup hbdd ⟨τ, hτ, hτT, rfl⟩
    linarith [h1.2]

/-- **The payoff of a fixed admissible stopping time does not depend on the horizon.**
For the Gaussian heat potential this is the occupation-density identity: the reward
`h(t,z) - E h(t-τ, B_τ)` is the white noise of the expected occupation measure of the
motion up to `τ`, which does not mention `t`. -/
def HorizonFreeIncrement (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (t T : ℝ) (z : Space d) : Prop :=
  ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ t) →
    h t z + ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P
      = h T z + ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P

/-- **`𝒰_h(t,z) ≤ 𝒰_h(T,z)` for `t ≤ T`**, the monotonicity in the horizon that the
right-hand side of `lem:brownian-ball-localization` uses.  Given that the payoff of a
fixed stopping time does not depend on the horizon, the family of admissible stopping
times grows with the horizon and the supremum grows with it. -/
theorem brownianValue_mono_horizon (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (t T : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) (z : Space d)
    (hinc : HorizonFreeIncrement B P h t T z)
    (hbdd : BddAbove (stoppingPayoffs B P h T)) :
    brownianValue B P h t z ≤ brownianValue B P h T z := by
  have hne : (stoppingPayoffs B P h t).Nonempty :=
    ⟨∫ ω, -h (t - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P,
      ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using ht, rfl⟩⟩
  have hkey : ∀ a ∈ stoppingPayoffs B P h t,
      h t z + a ≤ h T z + sSup (stoppingPayoffs B P h T) := by
    rintro a ⟨τ, hτ, hbt, rfl⟩
    have hb : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) ∈ stoppingPayoffs B P h T :=
      ⟨τ, hτ, fun ω => le_trans (hbt ω) htT, rfl⟩
    rw [hinc τ hτ hbt]
    have := le_csSup hbdd hb
    linarith
  have hsup : sSup (stoppingPayoffs B P h t)
      ≤ h T z + sSup (stoppingPayoffs B P h T) - h t z := by
    refine csSup_le hne fun a ha => ?_
    have := hkey a ha
    linarith
  have h1 : brownianDiscount B P h t = sSup (stoppingPayoffs B P h t) :=
    brownianDiscount_eq_sSup B P h t
  have h2 : brownianDiscount B P h T = sSup (stoppingPayoffs B P h T) :=
    brownianDiscount_eq_sSup B P h T
  unfold brownianValue
  rw [h1, h2]
  linarith

/-- The Brownian payoff gap between a reward and its cut-off version is paid by the
cutoff error, which is the Brownian half of the display at `sandpile.tex:1908-1922`. -/
theorem abs_integral_sub_cutoff_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T E : ℝ) (τ : ΩB → ℝ≥0) (χ : Space d → ℝ)
    (hχ1 : ∀ y, χ y ≤ 1)
    (hf : Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P)
    (hχf : Integrable (fun ω => -(χ (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) P)
    (hE : (∫ ω, (1 - χ (B (τ ω) ω)) * |h (T - τ ω) (B (τ ω) ω)| ∂P) ≤ E) :
    |(∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P)
        - ∫ ω, -(χ (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω)) ∂P| ≤ E := by
  have hdiff : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P)
        - ∫ ω, -(χ (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω)) ∂P
      = ∫ ω, (1 - χ (B (τ ω) ω)) * -h (T - τ ω) (B (τ ω) ω) ∂P := by
    rw [← MeasureTheory.integral_sub hf hχf]
    congr 1
    funext ω
    ring
  rw [hdiff]
  calc |∫ ω, (1 - χ (B (τ ω) ω)) * -h (T - τ ω) (B (τ ω) ω) ∂P|
      ≤ ∫ ω, |(1 - χ (B (τ ω) ω)) * -h (T - τ ω) (B (τ ω) ω)| ∂P :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ ω, (1 - χ (B (τ ω) ω)) * |h (T - τ ω) (B (τ ω) ω)| ∂P := by
        congr 1
        funext ω
        rw [abs_mul, abs_of_nonneg (by linarith [hχ1 (B (τ ω) ω)]), abs_neg]
    _ ≤ E := hE

end Sandpile.Continuum
