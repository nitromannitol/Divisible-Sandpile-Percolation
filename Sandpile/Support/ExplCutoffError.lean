import Sandpile.Support.ExplValueGap
import Sandpile.Support.ExplBallExit
import Sandpile.Support.Localization

/-!
# The Brownian half of the cutoff error

The Brownian half of the cutoff error of `sandpile.tex:1908-1922`.

The display at `sandpile.tex:1908-1921` bounds, uniformly over stopping times, the contribution to
the optimal-stopping value of the region where the cutoff `χ_A` is not one, and the sentence at
`sandpile.tex:1922` says that the analogous Brownian estimate holds. For a reward bounded by `M`
the Brownian estimate is exactly the Brownian maximal estimate: the integrand vanishes unless the
motion has left the ball of radius `A` about the origin, and a motion started at a point of norm
at most `ρ` has then moved a distance at least `A - ρ`, an event whose probability is at most
`C e^{-c(A-ρ)²/(2T)}` by the closed-ball exit tail
`Sandpile.Continuum.exists_ball_exit_tail_closed_uniform`, whose constants depend only on the
dimension.

The horizon of the exit tail is `2T` rather than `T` because an admissible stopping time may equal
the horizon, while the tail is stated for the motion strictly before its horizon.

What this does NOT contain is the walk half of the same display, where the reward is not bounded
uniformly in `A`: there the dyadic annuli, the Green-kernel estimates and `lem:weighted-exp-conc`
are needed to bound the field on the annulus by a power of its radius.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- Off the ball of radius `A` the complement of the cutoff is at most one, and on it it
vanishes: the cutoff error of a quantity bounded by `M` is at most `M` times the indicator
of the complement of the ball. -/
theorem cutoff_compl_mul_abs_le_indicator (A M : ℝ) (hA : 0 < A) (hM : 0 ≤ M)
    (y : Space d) (v : ℝ) (hv : |v| ≤ M) :
    (1 - cutoff A y) * |v| ≤ Set.indicator {z : Space d | A ≤ ‖z‖} (fun _ => M) y := by
  rcases le_or_gt A ‖y‖ with hy | hy
  · have hmem : y ∈ {z : Space d | A ≤ ‖z‖} := hy
    rw [Set.indicator_of_mem hmem]
    have h0 : 0 ≤ cutoff A y := cutoff_nonneg A y
    have h1 : cutoff A y ≤ 1 := cutoff_le_one A y
    have habs : 0 ≤ |v| := abs_nonneg v
    nlinarith
  · have hmem : y ∉ {z : Space d | A ≤ ‖z‖} := by
      simp only [Set.mem_setOf_eq, not_le]
      exact hy
    rw [Set.indicator_of_notMem hmem]
    have hone : cutoff A y = 1 := cutoff_eq_one_of_norm_le A hA y hy.le
    rw [hone]
    simp

/-- **The Brownian cutoff error is paid by the displacement probability.**  A reward bounded
by `M` contributes only when the motion has reached the complement of the ball of radius `A`,
which from a starting point of norm at most `ρ` means a displacement of at least `A - ρ`. -/
theorem integral_cutoff_le_measure (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T A M ρ : ℝ) (x : Space d)
    (hA : 0 < A) (hM : 0 ≤ M) (hx : ‖x‖ ≤ ρ)
    (hbound : ∀ (s : ℝ) (y : Space d), |h s y| ≤ M)
    (τ : ΩB → ℝ≥0)
    (hmeas : MeasurableSet {ω | A - ρ ≤ ‖B (τ ω) ω - x‖})
    (hint : Integrable
      (fun ω => (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) P) :
    (∫ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P)
      ≤ M * P.real {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} := by
  have hpt : ∀ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)|
      ≤ Set.indicator {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} (fun _ => M) ω := by
    intro ω
    rcases le_or_gt A ‖B (τ ω) ω‖ with hy | hy
    · have hmem : ω ∈ {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} := by
        have hnorm : ‖B (τ ω) ω‖ - ‖x‖ ≤ ‖B (τ ω) ω - x‖ := norm_sub_norm_le _ _
        simp only [Set.mem_setOf_eq]
        linarith
      rw [Set.indicator_of_mem hmem]
      have h0 : 0 ≤ cutoff A (B (τ ω) ω) := cutoff_nonneg A _
      have h1 : cutoff A (B (τ ω) ω) ≤ 1 := cutoff_le_one A _
      have habs : |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ≤ M := hbound _ _
      have hab0 : 0 ≤ |h (T - (τ ω : ℝ)) (B (τ ω) ω)| := abs_nonneg _
      nlinarith
    · have hone : cutoff A (B (τ ω) ω) = 1 :=
        cutoff_eq_one_of_norm_le A hA _ hy.le
      rw [hone]
      simp only [sub_self, zero_mul]
      exact Set.indicator_nonneg (fun _ _ => hM) ω
  calc ∫ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P
      ≤ ∫ ω, Set.indicator {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} (fun _ => M) ω ∂P :=
        integral_mono hint ((integrable_const M).indicator hmeas) hpt
    _ = P.real {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} * M := by
        rw [integral_indicator_const M hmeas]
        rfl
    _ = M * P.real {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} := by ring

/-- **The Brownian cutoff error, with Gaussian decay in the cutoff radius.**  The constants
depend only on the dimension; they are bound before the horizon, before the radius and
before the reward. -/
theorem exists_brownian_cutoff_bound (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (x : Space d) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
          ∀ (h : ℝ → Space d → ℝ) (T A M ρ : ℝ), 0 < T → 0 ≤ M → ‖x‖ ≤ ρ → ρ < A →
            (∀ (s : ℝ) (y : Space d), |h s y| ≤ M) →
            ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) →
              MeasurableSet {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} →
              Integrable
                (fun ω => (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) P →
              (∫ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P)
                ≤ M * (C * Real.exp (-(c * (A - ρ) ^ 2 / (2 * T)))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := exists_ball_exit_tail_closed_uniform d
  refine ⟨C, c, hC, hc, ?_⟩
  intro x Ω mΩ P hP B hB h T A M ρ hT hM hxρ hρA hbound τ hτT hmeas hint
  have hA : 0 < A := lt_of_le_of_lt (le_trans (norm_nonneg x) hxρ) hρA
  have hbase := integral_cutoff_le_measure B P h T A M ρ x hA hM hxρ hbound τ hmeas hint
  have hsub : {ω | A - ρ ≤ ‖B (τ ω) ω - x‖}
      ⊆ {ω | ∃ s : ℝ≥0, (s : ℝ) < 2 * T ∧ A - ρ ≤ ‖B s ω - x‖} := by
    intro ω hω
    exact ⟨τ ω, by linarith [hτT ω], hω⟩
  have hmono : P.real {ω | A - ρ ≤ ‖B (τ ω) ω - x‖}
      ≤ P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < 2 * T ∧ A - ρ ≤ ‖B s ω - x‖} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  have htl := htail x Ω mΩ P hP B hB (A - ρ) (by linarith) (2 * T) (by linarith)
  calc (∫ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ∂P)
      ≤ M * P.real {ω | A - ρ ≤ ‖B (τ ω) ω - x‖} := hbase
    _ ≤ M * P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < 2 * T ∧ A - ρ ≤ ‖B s ω - x‖} :=
        mul_le_mul_of_nonneg_left hmono hM
    _ ≤ M * (C * Real.exp (-(c * (A - ρ) ^ 2 / (2 * T)))) :=
        mul_le_mul_of_nonneg_left htl hM

/-- A bounded reward has a bounded set of attainable payoffs. -/
theorem bddAbove_stoppingPayoffs_of_bound (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsProbabilityMeasure P] (h : ℝ → Space d → ℝ) (T M : ℝ)
    (hb : ∀ (s : ℝ) (y : Space d), |h s y| ≤ M)
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P) :
    BddAbove (stoppingPayoffs B P h T) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, hτT, rfl⟩
  calc ∫ ω, -h (T - (τ ω : ℝ)) (B (τ ω) ω) ∂P ≤ ∫ _ω : ΩB, M ∂P := by
        refine integral_mono (hint τ hτ hτT) (integrable_const M) ?_
        intro ω
        exact le_trans (neg_le_abs _) (hb _ _)
    _ = M := by simp


/-- **The Brownian cutoff error of the four-term bound, with Gaussian decay in `A`.** -/
theorem exists_brownianDiscount_cutoff_gap (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (x : Space d) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
          ∀ (h : ℝ → Space d → ℝ) (T A M ρ : ℝ), 0 < T → 0 ≤ M → ‖x‖ ≤ ρ → ρ < A →
            (∀ (s : ℝ) (y : Space d), |h s y| ≤ M) →
            BddAbove (stoppingPayoffs B P h T) →
            BddAbove (stoppingPayoffs B P (fun s y => cutoff A y * h s y) T) →
            (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
              Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P) →
            (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
              Integrable (fun ω => -(cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) P) →
            (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
              Integrable
                (fun ω => (1 - cutoff A (B (τ ω) ω)) * |h (T - (τ ω : ℝ)) (B (τ ω) ω)|) P) →
            (∀ τ : Ω → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
              MeasurableSet {ω | A - ρ ≤ ‖B (τ ω) ω - x‖}) →
            |brownianDiscount B P h T
                - brownianDiscount B P (fun s y => cutoff A y * h s y) T|
              ≤ M * (C * Real.exp (-(c * (A - ρ) ^ 2 / (2 * T)))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := exists_brownian_cutoff_bound d
  refine ⟨C, c, hC, hc, ?_⟩
  intro x Ω mΩ P hP B hB h T A M ρ hT hM hxρ hρA hb hbdd hbdd' hf hχf hint hmeas
  refine abs_brownianDiscount_sub_cutoffDiscount_le B P h T A
    (M * (C * Real.exp (-(c * (A - ρ) ^ 2 / (2 * T))))) hT.le hbdd hbdd' hf hχf ?_
  intro τ hτ hτT
  exact hbound x Ω mΩ P hP B hB h T A M ρ hT hM hxρ hρA hb τ hτT (hmeas τ hτ hτT)
    (hint τ hτ hτT)


end Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- **The walk cutoff error is paid by the probability of leaving the ball**, for a reward
bounded on the region where the cutoff is not one.  This is the single-annulus form of the
display at `sandpile.tex:1908-1921`. -/
theorem integral_cutoff_le_measure_walk (hd : 1 ≤ d) (x : Site d)
    (τ : (ℕ → Site d) → ℕ) (F : ℕ → (ℕ → Site d) → ℝ) (A R M : ℝ) (hA : 0 < A)
    (hb : ∀ (k : ℕ) (X : ℕ → Site d), |F k X| ≤ M)
    (hmeas : MeasurableSet
      {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖})
    (hint : Integrable
      (fun X => (1 - Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|) (walkLaw d x)) :
    (∫ X, (1 - Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X| ∂(walkLaw d x))
      ≤ M * (walkLaw d x).real
        {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖} := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hpt : ∀ X : ℕ → Site d,
      (1 - Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X|
        ≤ Set.indicator
          {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖}
          (fun _ => M) X := by
    intro X
    rcases le_or_gt A ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖ with hy | hy
    · have hmemX : X ∈ {X : ℕ → Site d |
          A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖} := hy
      rw [Set.indicator_of_mem hmemX]
      have h0 : 0 ≤ Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X))) := Sandpile.Continuum.cutoff_nonneg A _
      have h1 : Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X))) ≤ 1 := Sandpile.Continuum.cutoff_le_one A _
      have habs : |F (τ X) X| ≤ M := hb _ _
      have hab0 : 0 ≤ |F (τ X) X| := abs_nonneg _
      nlinarith
    · have hmem : X ∉ {X : ℕ → Site d |
          A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖} := by
        simp only [Set.mem_setOf_eq, not_le]
        exact hy
      rw [Set.indicator_of_notMem hmem,
        Sandpile.Continuum.cutoff_eq_one_of_norm_le A hA _ hy.le]
      simp
  calc (∫ X, (1 - Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X (τ X)))) * |F (τ X) X| ∂(walkLaw d x))
      ≤ ∫ X, Set.indicator
          {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖}
          (fun _ => M) X ∂(walkLaw d x) :=
        integral_mono hint ((integrable_const M).indicator hmeas) hpt
    _ = (walkLaw d x).real
        {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖} * M := by
        rw [integral_indicator_const M hmeas]
        rfl
    _ = M * (walkLaw d x).real
        {X : ℕ → Site d | A ≤ ‖Sandpile.External.Lclt.scaledSite R (X (τ X))‖} := by ring


end Sandpile
