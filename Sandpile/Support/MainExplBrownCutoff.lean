/-
The Brownian half of the cutoff error of `sandpile.tex:1908-1921`, which the
paper records in one sentence ("The analogous Brownian estimate holds",
`sandpile.tex:1922`).

The walk half is `Sandpile.exists_walk_cutoff_error`, and the structure is the
same: outside the ball of radius `A` the region is cut into the dyadic annuli
`2^jA ≤ |y| < 2^{j+1}A`, on the `j`-th annulus a reward of polynomial growth is
at most a fixed power of the radius, and the ball-exit estimate gives a Gaussian
tail for reaching that annulus, so the sum of the products is small once `A` is
large.  The one place where the two halves differ is the confinement that makes
the sum finite: the walk takes at most `t_R` steps, so its scaled position is
bounded by a DETERMINISTIC radius and only finitely many annuli are charged,
while Brownian motion has no such bound.  Here the finite sums are taken over
the event that the motion has not left the ball of radius `2^{n+1}A`, those
events exhaust the space, and the estimate passes to the limit by dominated
convergence, the dominating function being the integrand itself.

The estimate is uniform in the starting point of scaled norm at most `ρ`, in the
stopping time below the horizon, and in the probability space, because the
ball-exit estimate is.
-/
import Sandpile.Support.ExplDyadic
import Sandpile.Support.ExplBallExit
import Sandpile.Support.StopMeasurable

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- **The ball-exit estimate on a realization space of any size.**  The estimate is a
statement about the law of the motion and the shared library proves it for a space in
every universe; the form used below therefore quantifies over `Type*`, so that it can be
applied on the realization space a statement of the paper carries. -/
theorem Sandpile.Support.exists_ball_exit_tail_closed_uniform (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (u : Sandpile.Continuum.Space d) (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Sandpile.Continuum.Space d,
          Sandpile.Continuum.IsBrownian d u B P →
          ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T →
            P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
              ≤ C * Real.exp (-(c * A ^ 2 / T)) := by
  obtain ⟨C, c, hC, hc, h⟩ := LatticeProb.brownian_exit_tail_closed d
  refine ⟨C, c, hC, hc, ?_⟩
  intro u Ω mΩ P hP B hB A hA T hT
  have hle := h u Ω P hP B (Sandpile.Continuum.isBrownianSpace_of_isBrownian hB) A hA T hT
  have hpos : (0 : ℝ) ≤ C * Real.exp (-(c * A ^ 2 / T)) := by positivity
  calc P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}
      = (P {ω | ∃ s : ℝ≥0, (s : ℝ) < T ∧ A ≤ ‖B s ω - u‖}).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * Real.exp (-(c * A ^ 2 / T)))).toReal :=
        ENNReal.toReal_mono (by simp) hle
    _ = C * Real.exp (-(c * A ^ 2 / T)) := ENNReal.toReal_ofReal hpos

namespace Sandpile.Continuum

variable {d : ℕ}

/-- **The motion reaches the `j`-th dyadic annulus about the origin with a Gaussian
probability.**  From a start of norm at most `ρ`, reaching norm `2^jA` means moving
`2^jA - ρ`, which is at least half of `2^jA` once `2ρ ≤ A`.  The constants depend only on
the dimension; the rate is an eighth of the rate of the ball-exit estimate. -/
theorem exists_brownian_annulus_reach_bound (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ T : ℝ, 0 < T →
      ∀ (x : Space d) (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
        ∀ ρ A : ℝ, 0 ≤ ρ → ‖x‖ ≤ ρ → 2 * ρ ≤ A → 4 ≤ A →
        ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) → ∀ j : ℕ,
          P.real {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}
            ≤ C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hexit⟩ := Sandpile.Support.exists_ball_exit_tail_closed_uniform d
  refine ⟨C₀, c₀ / 8, hC₀, by positivity, ?_⟩
  intro T hT x Ω mΩ P hP B hB ρ A hρ hxρ hρA hA4 τ hτT j
  have hA0 : (0 : ℝ) < A := by linarith
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have h2jA : A ≤ 2 ^ j * A := by nlinarith
  set r : ℝ := 2 ^ j * A - ρ with hrdef
  have hrhalf : 2 ^ j * A / 2 ≤ r := by
    have h1 : ρ ≤ A / 2 := by linarith
    have h2 : ρ ≤ 2 ^ j * A / 2 := by linarith
    linarith
  have hr0 : (0 : ℝ) < r := by nlinarith
  have hsub : {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}
      ⊆ {ω | ∃ s : ℝ≥0, (s : ℝ) < 2 * T ∧ r ≤ ‖B s ω - x‖} := by
    intro ω hω
    have hnorm : ‖B (τ ω) ω‖ - ‖x‖ ≤ ‖B (τ ω) ω - x‖ := norm_sub_norm_le _ _
    have hle : 2 ^ j * A ≤ ‖B (τ ω) ω‖ := hω
    exact ⟨τ ω, by linarith [hτT ω], by simp only [hrdef]; linarith⟩
  have hmono : P.real {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}
      ≤ P.real {ω | ∃ s : ℝ≥0, (s : ℝ) < 2 * T ∧ r ≤ ‖B s ω - x‖} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  have htl := hexit x Ω mΩ P hP B hB r hr0 (2 * T) (by linarith)
  have hexple : Real.exp (-(c₀ * r ^ 2 / (2 * T)))
      ≤ Real.exp (-(c₀ / 8 * (2 ^ j * A) ^ 2 / T)) := by
    refine Real.exp_le_exp.mpr ?_
    have hsq : (2 ^ j * A) ^ 2 / 4 ≤ r ^ 2 := by nlinarith [hrhalf, hr0.le]
    have hkey : c₀ / 8 * (2 ^ j * A) ^ 2 / T ≤ c₀ * r ^ 2 / (2 * T) := by
      rw [div_le_div_iff₀ hT (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hc₀.le hT.le)]
    linarith
  calc P.real {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}
      ≤ C₀ * Real.exp (-(c₀ * r ^ 2 / (2 * T))) := le_trans hmono htl
    _ ≤ C₀ * Real.exp (-(c₀ / 8 * (2 ^ j * A) ^ 2 / T)) :=
        mul_le_mul_of_nonneg_left hexple hC₀.le

/-- **The Brownian cutoff error of `sandpile.tex:1922`.**  For a quantity bounded on the
`j`-th dyadic annulus by a fixed power of the radius, the cutoff error is at most `ε` once
the cutoff radius is large enough, uniformly over the probability space, the starting points
of norm at most `ρ` and the stopping times below the horizon.  No confinement is assumed: the
finite sums are taken over the events that the motion has not left the ball of radius
`2^{n+1}A`, and those exhaust the space. -/
theorem exists_brownian_cutoff_error (d : ℕ) (p : ℕ) {K T ε : ℝ} (hK : 0 ≤ K)
    (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ (x : Space d) (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
        ∀ ρ : ℝ, 0 ≤ ρ → ‖x‖ ≤ ρ → 2 * ρ ≤ A →
        ∀ τ : Ω → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ T) →
        ∀ V : Ω → ℝ,
          (∀ j : ℕ, MeasurableSet {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}) →
          (∀ (ω : Ω) (j : ℕ), B (τ ω) ω ∈ dyadicAnnulus A j →
            |V ω| ≤ K * (2 ^ (j + 1) * A) ^ p) →
          Integrable (fun ω => (1 - cutoff A (B (τ ω) ω)) * |V ω|) P →
          (∫ ω, (1 - cutoff A (B (τ ω) ω)) * |V ω| ∂P) ≤ ε := by
  classical
  obtain ⟨C, c, hC, hc, hreach⟩ := exists_brownian_annulus_reach_bound d
  obtain ⟨A₀, hA₀1, hA₀⟩ := exists_cutoff_radius p hK hC.le hc hT hε
  refine ⟨max A₀ 4, le_max_right _ _, ?_⟩
  intro A hA x Ω mΩ P hP B hB ρ hρ hxρ hρA τ hτT V hmeas hV hint
  have hAA₀ : A₀ ≤ A := le_trans (le_max_left _ _) hA
  have hA4 : (4 : ℝ) ≤ A := le_trans (le_max_right _ _) hA
  have hA0 : (0 : ℝ) < A := by linarith
  set Y : Ω → Space d := fun ω => B (τ ω) ω with hY
  set f : Ω → ℝ := fun ω => (1 - cutoff A (Y ω)) * |V ω| with hf
  set M : ℕ → ℝ := fun j => K * (2 ^ (j + 1) * A) ^ p with hM
  have hM0 : ∀ j, 0 ≤ M j := fun j => by simp only [hM]; positivity
  have hf0 : ∀ ω, 0 ≤ f ω := by
    intro ω
    have h1 : cutoff A (Y ω) ≤ 1 := cutoff_le_one A (Y ω)
    have := abs_nonneg (V ω)
    simp only [hf]
    nlinarith
  set S : ℕ → Set Ω := fun n => {ω | ‖Y ω‖ < 2 ^ (n + 1) * A} with hS
  have hSm : ∀ n, MeasurableSet (S n) := by
    intro n
    have h := (hmeas (n + 1)).compl
    have he : (S n) = {ω | 2 ^ (n + 1) * A ≤ ‖Y ω‖}ᶜ := by
      ext ω; simp only [hS, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [he]; exact h
  have hstep : ∀ n : ℕ, (∫ ω, Set.indicator (S n) f ω ∂P) ≤ ε := by
    intro n
    have hint2 : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1),
        Set.indicator {ω' : Ω | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω) P :=
      integrable_finsetSum _ (fun j _ => (integrable_const (M j)).indicator (hmeas j))
    have hae : ∀ ω, Set.indicator (S n) f ω
        ≤ ∑ j ∈ Finset.range (n + 1),
            Set.indicator {ω' : Ω | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω := by
      intro ω
      by_cases hω : ω ∈ S n
      · rw [Set.indicator_of_mem hω]
        exact cutoff_compl_mul_le_sum_indicator A hA0 n M hM0 Y V ω hω
          (fun j _ hj => hV ω j hj)
      · rw [Set.indicator_of_notMem hω]
        exact Finset.sum_nonneg fun j _ =>
          Set.indicator_nonneg (fun _ _ => hM0 j) ω
    calc (∫ ω, Set.indicator (S n) f ω ∂P)
        ≤ ∫ ω, ∑ j ∈ Finset.range (n + 1),
            Set.indicator {ω' : Ω | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω ∂P :=
          integral_mono (hint.indicator (hSm n)) hint2 hae
      _ = ∑ j ∈ Finset.range (n + 1),
            ∫ ω, Set.indicator {ω' : Ω | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω ∂P :=
          integral_finsetSum _ (fun j _ => (integrable_const (M j)).indicator (hmeas j))
      _ = ∑ j ∈ Finset.range (n + 1), M j * P.real {ω : Ω | 2 ^ j * A ≤ ‖Y ω‖} := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [integral_indicator_const (M j) (hmeas j)]
          simp only [smul_eq_mul, Measure.real]
          ring
      _ ≤ ∑ j ∈ Finset.range (n + 1),
            (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T))) := by
          refine Finset.sum_le_sum ?_
          intro j _
          exact mul_le_mul_of_nonneg_left
            (hreach T hT x Ω mΩ P hP B hB ρ A hρ hxρ hρA hA4 τ hτT j) (hM0 j)
      _ ≤ ε := hA₀ A hAA₀ n
  have hconv : Filter.Tendsto (fun n => ∫ ω, Set.indicator (S n) f ω ∂P)
      Filter.atTop (nhds (∫ ω, f ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence f
      (fun n => ((hint.indicator (hSm n)).1)) hint ?_ ?_
    · intro n
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hω : ω ∈ S n
      · rw [Set.indicator_of_mem hω, abs_of_nonneg (hf0 ω)]
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact hf0 ω
    · filter_upwards with ω
      have hex : ∃ N : ℕ, ‖Y ω‖ < 2 ^ (N + 1) * A := by
        obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (‖Y ω‖ / A) (by norm_num : (1 : ℝ) < 2)
        refine ⟨N, ?_⟩
        rw [div_lt_iff₀ hA0] at hN
        have h2 : (2 : ℝ) ^ N * A ≤ 2 ^ (N + 1) * A := by
          have : (2 : ℝ) ^ N ≤ 2 ^ (N + 1) := by
            apply pow_le_pow_right₀ (by norm_num); omega
          nlinarith
        linarith
      obtain ⟨N, hN⟩ := hex
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hmem : ω ∈ S n := by
        simp only [hS, Set.mem_setOf_eq]
        have h2 : (2 : ℝ) ^ (N + 1) * A ≤ 2 ^ (n + 1) * A := by
          have : (2 : ℝ) ^ (N + 1) ≤ 2 ^ (n + 1) := by
            apply pow_le_pow_right₀ (by norm_num); omega
          nlinarith
        linarith
      rw [Set.indicator_of_mem hmem]
  exact le_of_tendsto hconv (Filter.Eventually.of_forall hstep)

/-- **`E₃` of the four-term bound for a reward of polynomial growth.**  The Brownian discount
of a reward and of its cut-off version differ by at most `ε` once the cutoff radius is large
enough, uniformly over the probability space and over the starting points of norm at most `ρ`.
This is the hypothesis `hcutB` of `Sandpile.abs_rescaled_odometer_sub_brownianValue_le` at the
Gaussian heat potential, which has no bound on the strip but grows polynomially there;
`Sandpile.Continuum.exists_brownianDiscount_cutoff_gap` is the same statement for a reward
with a uniform bound. -/
theorem exists_brownianDiscount_cutoff_gap_of_growth (d : ℕ) (p : ℕ) {K T ε : ℝ}
    (hK : 0 ≤ K) (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 4 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∀ (x : Space d) (Ω : Type*) (_ : MeasurableSpace Ω) (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → Space d, IsBrownian d x B P →
        ∀ ρ : ℝ, 0 ≤ ρ → ‖x‖ ≤ ρ → 2 * ρ ≤ A →
        ∀ h : ℝ → Space d → ℝ,
          (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Space d, |h s y| ≤ K * (1 + ‖y‖) ^ p) →
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
            ∀ j : ℕ, MeasurableSet {ω | 2 ^ j * A ≤ ‖B (τ ω) ω‖}) →
          |brownianDiscount B P h T
              - brownianDiscount B P (fun s y => cutoff A y * h s y) T| ≤ ε := by
  obtain ⟨A₀, hA₀4, hA₀⟩ := exists_brownian_cutoff_error d p
    (K := K * 2 ^ p) (T := T) (ε := ε) (by positivity) hT hε
  refine ⟨A₀, hA₀4, ?_⟩
  intro A hA x Ω mΩ P hP B hB ρ hρ hxρ hρA h hgrow hbdd hbdd' hf hχf hint hmeas
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₀4 hA
  have hA0 : (0 : ℝ) < A := by linarith
  refine abs_brownianDiscount_sub_cutoffDiscount_le B P h T A ε hT.le hbdd hbdd' hf hχf ?_
  intro τ hτ hτT
  refine hA₀ A hA x Ω mΩ P hP B hB ρ hρ hxρ hρA τ hτT
    (fun ω => h (T - (τ ω : ℝ)) (B (τ ω) ω)) (hmeas τ hτ hτT) ?_ (hint τ hτ hτT)
  intro ω j hj
  have h2j : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hz1 : (1 : ℝ) ≤ 2 ^ (j + 1) * A := by nlinarith
  have hmem : T - (τ ω : ℝ) ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hτT ω], sub_le_self T (τ ω).coe_nonneg⟩
  have hb := hgrow _ hmem (B (τ ω) ω)
  have hlt : ‖B (τ ω) ω‖ < 2 ^ (j + 1) * A := hj.2
  have hstep : (1 + ‖B (τ ω) ω‖) ^ p ≤ (2 * (2 ^ (j + 1) * A)) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    linarith
  have hpow : (2 * (2 ^ (j + 1) * A)) ^ p = 2 ^ p * (2 ^ (j + 1) * A) ^ p := mul_pow _ _ _
  calc |h (T - (τ ω : ℝ)) (B (τ ω) ω)| ≤ K * (1 + ‖B (τ ω) ω‖) ^ p := hb
    _ ≤ K * (2 * (2 ^ (j + 1) * A)) ^ p := mul_le_mul_of_nonneg_left hstep hK
    _ = K * 2 ^ p * (2 ^ (j + 1) * A) ^ p := by rw [hpow]; ring


/-- **The event that the stopped motion has reached a given radius is measurable**, which is
the side condition of `exists_brownian_cutoff_error` at every dyadic radius.  A bounded
stopping time of the motion's natural filtration is measurable as soon as the motion is, and
the stopped position is then measurable because the paths are continuous. -/
theorem measurableSet_reach_brownian {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → Space d} {τ : Ω → ℝ≥0}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω)
    (hτ : IsBrownianStopping B τ) (c : ℝ) :
    MeasurableSet {ω | c ≤ ‖B (τ ω) ω‖} :=
  ((measurable_stopped_position hm hc
    (hτ.measurable (fun t => (hm t).stronglyMeasurable))).norm) measurableSet_Ici


end Sandpile.Continuum
