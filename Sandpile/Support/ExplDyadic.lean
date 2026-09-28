import Sandpile.Support.ExplCutoffError

/-!
# The dyadic annulus decomposition of the cutoff error

The cutoff error outside a ball of radius `A` is controlled by decomposing the exterior into
dyadic annuli `2^j A ≤ ‖y‖ < 2^{j+1} A`. `exists_dyadic_index` and
`cutoff_compl_mul_le_sum_indicator` place each confined point in exactly one annulus and bound
the error there, and `integral_cutoff_le_sum_reach` integrates this bound against the
probability of reaching each annulus's inner radius. When the bound on the `j`-th annulus is a
fixed power `K (2^{j+1}A)^p` and the probability of reaching it decays like a Gaussian tail
`C e^{-c(2^jA)^2/T}`, `dyadic_term_le` shows each term is at most a constant times a geometric
ratio `(2^p e^{-cA/T})^j`, using that `4^j ≥ j + 1`. Summing this geometric series gives
`exists_cutoff_radius`: the total error is at most any `ε > 0` once the cutoff radius `A` is
large enough, uniformly in the number of confined annuli.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The `j`-th dyadic annulus outside the ball of radius `A`: the points of norm at least
`2^j A` and less than `2^{j+1} A`. -/
def dyadicAnnulus (A : ℝ) (j : ℕ) : Set (Space d) :=
  {y | 2 ^ j * A ≤ ‖y‖ ∧ ‖y‖ < 2 ^ (j + 1) * A}

/-- A point outside the ball of radius `A` and inside the ball of radius `2^{n+1}A` lies in
one of the first `n+1` dyadic annuli. -/
theorem exists_dyadic_index {A : ℝ} {y : Space d} (hy : A ≤ ‖y‖) :
    ∀ n : ℕ, ‖y‖ < 2 ^ (n + 1) * A → ∃ j ≤ n, y ∈ dyadicAnnulus A j := by
  intro n
  induction n with
  | zero =>
      intro h0
      refine ⟨0, le_refl 0, ?_⟩
      constructor
      · simpa using hy
      · simpa using h0
  | succ n ih =>
      intro hsucc
      rcases lt_or_ge ‖y‖ (2 ^ (n + 1) * A) with h | h
      · obtain ⟨j, hj, hmem⟩ := ih h
        exact ⟨j, Nat.le_succ_of_le hj, hmem⟩
      · exact ⟨n + 1, le_refl _, ⟨h, hsucc⟩⟩

/-- The cutoff error at one point, for a quantity bounded by `M j` on the `j`-th annulus, is
at most the sum over the annuli of `M j` on the event that the inner radius is reached. -/
theorem cutoff_compl_mul_le_sum_indicator {X : Type*} (A : ℝ) (hA : 0 < A) (n : ℕ)
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j) (Y : X → Space d) (V : X → ℝ) (ω : X)
    (hconf : ‖Y ω‖ < 2 ^ (n + 1) * A)
    (hV : ∀ j ≤ n, Y ω ∈ dyadicAnnulus A j → |V ω| ≤ M j) :
    (1 - cutoff A (Y ω)) * |V ω|
      ≤ ∑ j ∈ Finset.range (n + 1),
          Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω := by
  rcases lt_or_ge ‖Y ω‖ A with h | h
  · have hone : cutoff A (Y ω) = 1 := cutoff_eq_one_of_norm_le A hA _ h.le
    rw [hone, sub_self, zero_mul]
    refine Finset.sum_nonneg ?_
    intro j _
    exact Set.indicator_nonneg (fun _ _ => hM j) ω
  · obtain ⟨j, hj, hmem⟩ := exists_dyadic_index h n hconf
    have hmemr : ω ∈ {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} := hmem.1
    have hterm : Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω = M j :=
      Set.indicator_of_mem hmemr _
    have hle : (1 - cutoff A (Y ω)) * |V ω| ≤ M j := by
      have h0 : 0 ≤ cutoff A (Y ω) := cutoff_nonneg A _
      have h1 : cutoff A (Y ω) ≤ 1 := cutoff_le_one A _
      have habs : |V ω| ≤ M j := hV j hj hmem
      have hab0 : 0 ≤ |V ω| := abs_nonneg _
      nlinarith
    refine hle.trans ?_
    rw [← hterm]
    refine Finset.single_le_sum
      (f := fun j => Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω)
      ?_ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    intro i _
    exact Set.indicator_nonneg (fun _ _ => hM i) ω

/-- **The dyadic sum of `sandpile.tex:1908-1921`.**  The cutoff error of a quantity bounded
by `M j` on the `j`-th dyadic annulus is at most the sum of `M j` against the probability of
reaching the inner radius of that annulus. -/
theorem integral_cutoff_le_sum_reach {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (A : ℝ) (hA : 0 < A) (n : ℕ)
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j) (Y : X → Space d) (V : X → ℝ)
    (hmeas : ∀ j, MeasurableSet {ω : X | 2 ^ j * A ≤ ‖Y ω‖})
    (hconf : ∀ᵐ ω ∂μ, ‖Y ω‖ < 2 ^ (n + 1) * A)
    (hV : ∀ ω, ∀ j ≤ n, Y ω ∈ dyadicAnnulus A j → |V ω| ≤ M j)
    (hint : Integrable (fun ω => (1 - cutoff A (Y ω)) * |V ω|) μ) :
    (∫ ω, (1 - cutoff A (Y ω)) * |V ω| ∂μ)
      ≤ ∑ j ∈ Finset.range (n + 1), M j * μ.real {ω : X | 2 ^ j * A ≤ ‖Y ω‖} := by
  have hint2 : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1),
      Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω) μ :=
    integrable_finsetSum _ (fun j _ => (integrable_const (M j)).indicator (hmeas j))
  have hae : ∀ᵐ ω ∂μ, (1 - cutoff A (Y ω)) * |V ω|
      ≤ ∑ j ∈ Finset.range (n + 1),
          Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω := by
    filter_upwards [hconf] with ω hω
    exact cutoff_compl_mul_le_sum_indicator A hA n M hM Y V ω hω (hV ω)
  calc (∫ ω, (1 - cutoff A (Y ω)) * |V ω| ∂μ)
      ≤ ∫ ω, ∑ j ∈ Finset.range (n + 1),
          Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω ∂μ :=
        integral_mono_ae hint hint2 hae
    _ = ∑ j ∈ Finset.range (n + 1),
          ∫ ω, Set.indicator {ω' : X | 2 ^ j * A ≤ ‖Y ω'‖} (fun _ => M j) ω ∂μ :=
        integral_finsetSum _ (fun j _ => (integrable_const (M j)).indicator (hmeas j))
    _ = ∑ j ∈ Finset.range (n + 1), M j * μ.real {ω : X | 2 ^ j * A ≤ ‖Y ω‖} := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [integral_indicator_const (M j) (hmeas j)]
        simp [Measure.real, mul_comm]

/-- `4^j` dominates `j+1`: the elementary inequality that turns the Gaussian tail on the
`j`-th annulus into a geometric factor. -/
theorem nat_succ_le_four_pow (j : ℕ) : ((j : ℝ) + 1) ≤ 4 ^ j := by
  induction j with
  | zero => norm_num
  | succ k ih =>
      have h1 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
      have h4 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
      rw [h4]
      push_cast
      nlinarith [ih, h1]

/-- A geometric series of ratio at most one half has partial sums at most two. -/
theorem sum_pow_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (m : ℕ) :
    ∑ j ∈ Finset.range m, r ^ j ≤ 2 := by
  calc ∑ j ∈ Finset.range m, r ^ j ≤ ∑ j ∈ Finset.range m, (1 / 2 : ℝ) ^ j := by
        refine Finset.sum_le_sum ?_
        intro j _
        exact pow_le_pow_left₀ hr0 hr j
    _ ≤ 2 := sum_geometric_two_le m

/-- A power times a decaying exponential tends to zero. -/
theorem tendsto_pow_mul_exp_neg_const_mul (p : ℕ) {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun x : ℝ => x ^ p * Real.exp (-(b * x))) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun x : ℝ => (b * x) ^ p * Real.exp (-(b * x)))
      Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp
      (Filter.Tendsto.const_mul_atTop hb Filter.tendsto_id)
  have h3 : Filter.Tendsto
      (fun x : ℝ => (b ^ p)⁻¹ * ((b * x) ^ p * Real.exp (-(b * x))))
      Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul ((b ^ p)⁻¹) h
  refine Filter.Tendsto.congr ?_ h3
  intro x
  rw [mul_pow]
  field_simp

/-- The same, with the rate written as the paper writes it. -/
theorem tendsto_pow_mul_exp_neg_div (p : ℕ) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    Filter.Tendsto (fun A : ℝ => A ^ p * Real.exp (-(c * A / T))) Filter.atTop (nhds 0) := by
  have h := tendsto_pow_mul_exp_neg_const_mul p (div_pos hc hT)
  refine Filter.Tendsto.congr (fun x => ?_) h
  rw [div_mul_eq_mul_div]

/-- The `j`-th term of the dyadic sum is at most a constant times the `j`-th power of
`2^p e^{-cA/T}`: the power of the radius contributes `(2^p)^j`, and the Gaussian tail
contributes `e^{-cA/T}` to the power `j+1`, because `4^j ≥ j+1` and `A^2 ≥ A`. -/
theorem dyadic_term_le (p : ℕ) {K C c T A : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hc : 0 < c)
    (hT : 0 < T) (hA : 1 ≤ A) (j : ℕ) :
    (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T)))
      ≤ (K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T)))
        * ((2 : ℝ) ^ p * Real.exp (-(c * A / T))) ^ j := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
  have hr0 : (0 : ℝ) < Real.exp (-(c * A / T)) := Real.exp_pos _
  have hpow : ((2 : ℝ) ^ (j + 1)) ^ p = 2 ^ p * ((2 : ℝ) ^ p) ^ j := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have h4 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hsucc : ((j : ℝ) + 1) ≤ 4 ^ j := nat_succ_le_four_pow j
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hexple : Real.exp (-(c * (2 ^ j * A) ^ 2 / T))
      ≤ Real.exp (-(c * A / T)) ^ (j + 1) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hkey : ((j : ℝ) + 1) * A ≤ (2 ^ j * A) ^ 2 := by
      rw [mul_pow, h4]
      nlinarith [hsucc, hAA, hA0]
    have hpos : (0 : ℝ) < c * T⁻¹ := by positivity
    push_cast
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hkey hpos.le]
  have hnn : (0 : ℝ) ≤ K * (2 ^ (j + 1) * A) ^ p := by positivity
  calc (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T)))
      ≤ (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * A / T)) ^ (j + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        exact mul_le_mul_of_nonneg_left hexple hC
    _ = (K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T)))
        * ((2 : ℝ) ^ p * Real.exp (-(c * A / T))) ^ j := by
        rw [mul_pow, hpow, mul_pow]
        ring

/-- **The dyadic sum is small once the cutoff radius is large**, uniformly in the number of
annuli: for a field bounded on the `j`-th annulus by `K (2^{j+1}A)^p` and a Gaussian tail
`C e^{-c(2^jA)^2/T}` for reaching it, every partial sum is at most `ε` once `A ≥ A₀`.  This
is the estimate the display at `sandpile.tex:1908-1921` asserts. -/
theorem exists_cutoff_radius (p : ℕ) {K C c T ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hc : 0 < c) (hT : 0 < T) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ n : ℕ,
      ∑ j ∈ Finset.range (n + 1),
        (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T))) ≤ ε := by
  have hlim1 : Filter.Tendsto (fun A : ℝ => (2 : ℝ) ^ p * Real.exp (-(c * A / T)))
      Filter.atTop (nhds 0) := by
    have h0 := tendsto_pow_mul_exp_neg_div 0 hc hT
    simpa using Filter.Tendsto.const_mul ((2 : ℝ) ^ p) h0
  have hlim2 : Filter.Tendsto
      (fun A : ℝ => (2 * (K * C * 2 ^ p)) * (A ^ p * Real.exp (-(c * A / T))))
      Filter.atTop (nhds 0) := by
    simpa using
      Filter.Tendsto.const_mul (2 * (K * C * 2 ^ p)) (tendsto_pow_mul_exp_neg_div p hc hT)
  have he1 : ∀ᶠ A : ℝ in Filter.atTop, (2 : ℝ) ^ p * Real.exp (-(c * A / T)) < 1 / 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) hlim1
  have he2 : ∀ᶠ A : ℝ in Filter.atTop,
      (2 * (K * C * 2 ^ p)) * (A ^ p * Real.exp (-(c * A / T))) < ε :=
    Filter.Tendsto.eventually_lt_const hε hlim2
  obtain ⟨A₁, hA₁⟩ :=
    Filter.eventually_atTop.mp (he1.and (he2.and (Filter.eventually_ge_atTop (1 : ℝ))))
  refine ⟨max 1 A₁, le_max_left _ _, ?_⟩
  intro A hA n
  obtain ⟨hg1, hg2, _⟩ := hA₁ A (le_trans (le_max_right _ _) hA)
  have hA1 : (1 : ℝ) ≤ A := le_trans (le_max_left _ _) hA
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA1
  have hr0 : (0 : ℝ) < Real.exp (-(c * A / T)) := Real.exp_pos _
  have hconst : (0 : ℝ) ≤ K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T)) := by positivity
  have hratio0 : (0 : ℝ) ≤ (2 : ℝ) ^ p * Real.exp (-(c * A / T)) := by positivity
  calc ∑ j ∈ Finset.range (n + 1),
        (K * (2 ^ (j + 1) * A) ^ p) * (C * Real.exp (-(c * (2 ^ j * A) ^ 2 / T)))
      ≤ ∑ j ∈ Finset.range (n + 1),
          (K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T)))
            * ((2 : ℝ) ^ p * Real.exp (-(c * A / T))) ^ j :=
        Finset.sum_le_sum (fun j _ => dyadic_term_le p hK hC hc hT hA1 j)
    _ = (K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T)))
          * ∑ j ∈ Finset.range (n + 1), ((2 : ℝ) ^ p * Real.exp (-(c * A / T))) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ (K * C * 2 ^ p * A ^ p * Real.exp (-(c * A / T))) * 2 :=
        mul_le_mul_of_nonneg_left (sum_pow_le_two hratio0 hg1.le (n + 1)) hconst
    _ ≤ ε := by nlinarith [hg2]

end Sandpile.Continuum
