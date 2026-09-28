import Sandpile.Support.StopMeasurable
import Sandpile.Support.KillLip
import Sandpile.Support.LimBallBounds

/-!
# Lipschitz reward comparisons for Brownian stopping values

Reward comparisons for the natural Brownian stopping class. Bounded continuous rewards have
integrable payoffs at every admissible time. The full, ball and cube discounts are 1-Lipschitz;
adding the initial reward gives the corresponding 2-Lipschitz value estimate. The comparisons all
factor through the abstract supremum-difference bound `abs_sSup_attainable_sub_le` (two
suprema over a common index set with bounded and close-in-value payoffs are themselves close)
applied to `abs_constrained_brownianDiscount_sub_le`, and are specialized to the full time strip
(`abs_brownianDiscount_sub_le_of_continuousOn`), a closed ball
(`abs_brownianDiscountBall_sub_le_of_continuousOn`), and a closed cube
(`abs_brownianDiscountCube_sub_le_of_continuousOn`) by restricting the admissible stopping times
with the constraint predicate `C`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Sandpile.Continuum


/-- If `f` and `g` are two payoff functions on a common nonempty index set `A`, each bounded
(by `M` and `N` respectively) and pointwise close (`|f i - g i| ≤ E`), then their suprema over
`A` are within `E` of each other: bounding each supremum by the other's value plus `E` via
`csSup_le` and `le_csSup` on both sides. -/
theorem Sandpile.Continuum.abs_sSup_attainable_sub_le {ι : Type*} (A : ι → Prop)
    (hne : ∃ i, A i) (f g : ι → ℝ) (M N E : ℝ)
    (hf : ∀ i, A i → |f i| ≤ M) (hg : ∀ i, A i → |g i| ≤ N)
    (hfg : ∀ i, A i → |f i - g i| ≤ E) :
    |sSup {a : ℝ | ∃ i, A i ∧ a = f i} - sSup {a : ℝ | ∃ i, A i ∧ a = g i}| ≤ E := by
  obtain ⟨i₀, hi₀⟩ := hne
  have hfn : ({a : ℝ | ∃ i, A i ∧ a = f i} : Set ℝ).Nonempty := ⟨f i₀, i₀, hi₀, rfl⟩
  have hgn : ({a : ℝ | ∃ i, A i ∧ a = g i} : Set ℝ).Nonempty := ⟨g i₀, i₀, hi₀, rfl⟩
  have hfb : BddAbove {a : ℝ | ∃ i, A i ∧ a = f i} := by
    refine ⟨M, ?_⟩
    rintro a ⟨i, hi, rfl⟩
    exact (le_abs_self _).trans (hf i hi)
  have hgb : BddAbove {a : ℝ | ∃ i, A i ∧ a = g i} := by
    refine ⟨N, ?_⟩
    rintro a ⟨i, hi, rfl⟩
    exact (le_abs_self _).trans (hg i hi)
  rw [abs_sub_le_iff]
  constructor
  · refine sub_le_iff_le_add.2 (csSup_le hfn ?_)
    rintro a ⟨i, hi, rfl⟩
    have h₁ := (abs_sub_le_iff.1 (hfg i hi)).1
    have h₂ := le_csSup hgb (show g i ∈ {a : ℝ | ∃ i, A i ∧ a = g i} from ⟨i, hi, rfl⟩)
    linarith
  · refine sub_le_iff_le_add.2 (csSup_le hgn ?_)
    rintro a ⟨i, hi, rfl⟩
    have h₁ := (abs_sub_le_iff.1 (hfg i hi)).2
    have h₂ := le_csSup hfb (show f i ∈ {a : ℝ | ∃ i, A i ∧ a = f i} from ⟨i, hi, rfl⟩)
    linarith


/-- The general reward-comparison lemma behind the Lipschitz bounds of this file: for rewards
`h`, `g` continuous on the time strip and bounded (by `M`, `N`) and close (within `E`) almost
surely at every stopping time `τ` satisfying a constraint `C` (with `C` satisfied by the constant
zero stopping time), the suprema of the discounted payoffs `∫ -h(T - τ, B τ)` and
`∫ -g(T - τ, B τ)` over such `τ` differ by at most `E`. Combines
`Sandpile.Continuum.integrable_brownian_payoff_of_continuousOn` for integrability, a bound on
`∫ -h - ∫ -g` via `norm_integral_le_of_norm_le_const`, and `abs_sSup_attainable_sub_le` to pass
from pointwise closeness to closeness of the suprema. -/
theorem Sandpile.Continuum.abs_constrained_brownianDiscount_sub_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {x : Sandpile.Continuum.Space d}
    {B : ℝ≥0 → Ω → Sandpile.Continuum.Space d} {P : Measure Ω} [IsProbabilityMeasure P]
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (C : (Ω → ℝ≥0) → Prop) (hC : C (fun _ => 0))
    (h g : ℝ → Sandpile.Continuum.Space d → ℝ) (T M N E : ℝ) (hT : 0 ≤ T)
    (hh : ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => h q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hg : ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => g q.1 q.2)
      (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) → C τ → ∀ᵐ ω ∂P, |h (T - τ ω) (B (τ ω) ω)| ≤ M)
    (gb : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) → C τ → ∀ᵐ ω ∂P, |g (T - τ ω) (B (τ ω) ω)| ≤ N)
    (hgap : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) → C τ → ∀ᵐ ω ∂P,
      |h (T - τ ω) (B (τ ω) ω) - g (T - τ ω) (B (τ ω) ω)| ≤ E) :
    |sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
        (∀ ω, (τ ω : ℝ) ≤ T) ∧ C τ ∧ a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P} -
      sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
        (∀ ω, (τ ω : ℝ) ≤ T) ∧ C τ ∧ a = ∫ ω, -g (T - τ ω) (B (τ ω) ω) ∂P}| ≤ E := by
  let A := fun τ : Ω → ℝ≥0 => Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ T) ∧ C τ
  have hne : ∃ τ, A τ :=
    ⟨fun _ => 0, Sandpile.Continuum.isBrownianStopping_const B 0, fun _ => by simpa using hT, hC⟩
  have hfb : ∀ τ, A τ → |∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P| ≤ M := by
    intro τ ha
    have he := norm_integral_le_of_norm_le_const (f := fun ω => -h (T - τ ω) (B (τ ω) ω))
      ((hb τ ha.1 ha.2.1 ha.2.2).mono fun ω hω => by
        simpa only [norm_neg, Real.norm_eq_abs] using hω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using he
  have hgb : ∀ τ, A τ → |∫ ω, -g (T - τ ω) (B (τ ω) ω) ∂P| ≤ N := by
    intro τ ha
    have he := norm_integral_le_of_norm_le_const (f := fun ω => -g (T - τ ω) (B (τ ω) ω))
      ((gb τ ha.1 ha.2.1 ha.2.2).mono fun ω hω => by
        simpa only [norm_neg, Real.norm_eq_abs] using hω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using he
  have hfg : ∀ τ, A τ → |(∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) -
      ∫ ω, -g (T - τ ω) (B (τ ω) ω) ∂P| ≤ E := by
    intro τ ha
    have hi := Sandpile.Continuum.integrable_brownian_payoff_of_continuousOn hB ha.1 h T M hh
      ha.2.1 (hb τ ha.1 ha.2.1 ha.2.2)
    have gi := Sandpile.Continuum.integrable_brownian_payoff_of_continuousOn hB ha.1 g T N hg
      ha.2.1 (gb τ ha.1 ha.2.1 ha.2.2)
    rw [← integral_sub hi gi]
    have he := norm_integral_le_of_norm_le_const
      (f := fun ω => -h (T - τ ω) (B (τ ω) ω) - -g (T - τ ω) (B (τ ω) ω))
      ((hgap τ ha.1 ha.2.1 ha.2.2).mono fun ω hω => by
        simpa only [Real.norm_eq_abs, neg_sub_neg, abs_sub_comm] using hω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using he
  simpa only [A, and_assoc] using Sandpile.Continuum.abs_sSup_attainable_sub_le A hne
    (fun τ => ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P)
    (fun τ => ∫ ω, -g (T - τ ω) (B (τ ω) ω) ∂P) M N E hfb hgb hfg


namespace Sandpile.Continuum

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {u : Space d} {B : ℝ≥0 → Ω → Space d}

/-- The full discount is 1-Lipschitz for rewards continuous and bounded on the time strip. -/
theorem abs_brownianDiscount_sub_le_of_continuousOn (hB : IsBrownian d u B P)
    (h g : ℝ → Space d → ℝ) (T M N E : ℝ) (hT : 0 ≤ T)
    (hh : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hg : ContinuousOn (fun q : ℝ × Space d => g q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ s ∈ Set.Icc 0 T, ∀ y, |h s y| ≤ M)
    (gb : ∀ s ∈ Set.Icc 0 T, ∀ y, |g s y| ≤ N)
    (hgap : ∀ s ∈ Set.Icc 0 T, ∀ y, |h s y - g s y| ≤ E) :
    |brownianDiscount B P h T - brownianDiscount B P g T| ≤ E := by
  have hm : ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) → ∀ ω,
      T - (τ ω : ℝ) ∈ Set.Icc 0 T := fun τ ht ω =>
    ⟨sub_nonneg.mpr (ht ω), sub_le_self _ (τ ω).coe_nonneg⟩
  have he := abs_constrained_brownianDiscount_sub_le hB (fun _ => True) trivial h g T M N E
    hT hh hg (fun τ _ ht _ => Filter.Eventually.of_forall fun ω => hb _ (hm τ ht ω) _)
    (fun τ _ ht _ => Filter.Eventually.of_forall fun ω => gb _ (hm τ ht ω) _)
    (fun τ _ ht _ => Filter.Eventually.of_forall fun ω => hgap _ (hm τ ht ω) _)
  simpa only [brownianDiscount, true_and] using he

/-- The ball discount comparison uses bounds only on the closed ball. -/
theorem abs_brownianDiscountBall_sub_le_of_continuousOn (hB : IsBrownian d u B P)
    (h g : ℝ → Space d → ℝ) (T A M N E : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (hh : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hg : ContinuousOn (fun q : ℝ × Space d => g q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ s ∈ Set.Icc 0 T, ∀ y, ‖y - u‖ ≤ A → |h s y| ≤ M)
    (gb : ∀ s ∈ Set.Icc 0 T, ∀ y, ‖y - u‖ ≤ A → |g s y| ≤ N)
    (hgap : ∀ s ∈ Set.Icc 0 T, ∀ y, ‖y - u‖ ≤ A → |h s y - g s y| ≤ E) :
    |brownianDiscountBall B P h T A u - brownianDiscountBall B P g T A u| ≤ E := by
  let C := fun τ : Ω → ℝ≥0 => ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ‖B s ω - u‖ ≤ A
  have hC : C (fun _ => 0) :=
    Filter.Eventually.of_forall (fun _ s hs =>
      False.elim (not_lt_of_ge (show (0 : ℝ≥0) ≤ s from zero_le) hs))
  have hB' : LatticeProb.IsBrownianSpace d u B P := ⟨hB.start, hB.coord, hB.indep⟩
  have hm : ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) → C τ →
      ∀ᵐ ω ∂P, T - (τ ω : ℝ) ∈ Set.Icc 0 T ∧ ‖B (τ ω) ω - u‖ ≤ A := by
    intro τ ht hc
    filter_upwards [hB'.cont, hB.start, hc] with ω hw h0 hcω
    refine ⟨⟨sub_nonneg.mpr (ht ω), sub_le_self _ (τ ω).coe_nonneg⟩, ?_⟩
    exact Sandpile.Support.stopped_position_mem_closedBall hw u A (τ ω)
      (by simpa only [h0, sub_self, norm_zero] using hA) hcω
  exact abs_constrained_brownianDiscount_sub_le hB C hC h g T M N E hT hh hg
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => hb _ hw.1 _ hw.2)
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => gb _ hw.1 _ hw.2)
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => hgap _ hw.1 _ hw.2)

/-- The cube discount is 1-Lipschitz using bounds only inside the closed cube. -/
theorem abs_brownianDiscountCube_sub_le_of_continuousOn (hB : IsBrownian d u B P)
    (h g : ℝ → Space d → ℝ) (T L M N E : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hh : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hg : ContinuousOn (fun q : ℝ × Space d => g q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ s ∈ Set.Icc 0 T, ∀ y, (∀ i, |y i - u i| ≤ L) → |h s y| ≤ M)
    (gb : ∀ s ∈ Set.Icc 0 T, ∀ y, (∀ i, |y i - u i| ≤ L) → |g s y| ≤ N)
    (hgap : ∀ s ∈ Set.Icc 0 T, ∀ y, (∀ i, |y i - u i| ≤ L) → |h s y - g s y| ≤ E) :
    |brownianDiscountCube B P h T L u - brownianDiscountCube B P g T L u| ≤ E := by
  let C := fun τ : Ω → ℝ≥0 => ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L
  have hC : C (fun _ => 0) :=
    Filter.Eventually.of_forall (fun _ s hs =>
      False.elim (not_lt_of_ge (show (0 : ℝ≥0) ≤ s from zero_le) hs))
  have hB' : LatticeProb.IsBrownianSpace d u B P := ⟨hB.start, hB.coord, hB.indep⟩
  have hm : ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) → C τ →
      ∀ᵐ ω ∂P, T - (τ ω : ℝ) ∈ Set.Icc 0 T ∧ ∀ i, |B (τ ω) ω i - u i| ≤ L := by
    intro τ ht hc
    filter_upwards [ae_cube_at_stop B P u L hL hB'.cont hB.start τ hc] with ω hw
    exact ⟨⟨sub_nonneg.mpr (ht ω), sub_le_self _ (τ ω).coe_nonneg⟩, hw⟩
  exact abs_constrained_brownianDiscount_sub_le hB C hC h g T M N E hT hh hg
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => hb _ hw.1 _ hw.2)
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => gb _ hw.1 _ hw.2)
    (fun τ _ ht hc => (hm τ ht hc).mono fun ω hw => hgap _ hw.1 _ hw.2)

/-- A continuous cube reward bounded on the cube has an integrable payoff at every killed time. -/
theorem integrable_cube_payoff_of_continuousOn (hB : IsBrownian d u B P)
    (h : ℝ → Space d → ℝ) (T L M : ℝ) (hL : 0 ≤ L)
    (hh : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ s ∈ Set.Icc 0 T, ∀ y, (∀ i, |y i - u i| ≤ L) → |h s y| ≤ M)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStopping B τ) (ht : ∀ ω, (τ ω : ℝ) ≤ T)
    (hc : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) :
    Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P := by
  have hB' : LatticeProb.IsBrownianSpace d u B P := ⟨hB.start, hB.coord, hB.indep⟩
  refine integrable_brownian_payoff_of_continuousOn hB hτ h T M hh ht ?_
  filter_upwards [ae_cube_at_stop B P u L hL hB'.cont hB.start τ hc] with ω hw
  exact hb _ ⟨sub_nonneg.mpr (ht ω), sub_le_self _ (τ ω).coe_nonneg⟩ _ hw

/-- Cube payoffs are bounded above by a bound on the reward inside the cube. -/
theorem bddAbove_cubeStoppingPayoffs_of_continuousOn (hB : IsBrownian d u B P)
    (h : ℝ → Space d → ℝ) (T L M : ℝ) (hL : 0 ≤ L)
    (hh : ContinuousOn (fun q : ℝ × Space d => h q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ))
    (hb : ∀ s ∈ Set.Icc 0 T, ∀ y, (∀ i, |y i - u i| ≤ L) → |h s y| ≤ M) :
    BddAbove (cubeStoppingPayoffs B P h T L u) := by
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, ht, hc, rfl⟩
  have hi := integrable_cube_payoff_of_continuousOn hB h T L M hL hh hb τ hτ ht hc
  have hB' : LatticeProb.IsBrownianSpace d u B P := ⟨hB.start, hB.coord, hB.indep⟩
  have he : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) ≤ ∫ _ω : Ω, M ∂P := by
    refine integral_mono_ae hi (integrable_const M) ?_
    filter_upwards [ae_cube_at_stop B P u L hL hB'.cont hB.start τ hc] with ω hw
    exact (neg_le_abs _).trans (hb _ ⟨sub_nonneg.mpr (ht ω), sub_le_self _ (τ ω).coe_nonneg⟩ _ hw)
  simpa using he

end Sandpile.Continuum
