/-
The last-visit estimate of `sandpile.tex:4760-4776`
(label `lem:dgt4-weighted-last-visits`).

The paper proves it from the ergodic theorem for the stationary sequence
`I_i^∞` of never-return indicators, summation by parts, and the fact that
`I_{i,j} - I_i^∞` is the event that the first return is finite and later than
`j`.  The proof here replaces the ergodic theorem by a second moment: the
correlation of `I_0^∞` and `I_k^∞` is at most twice
`ρ_k - ρ_∞ = P_0(k < τ_0^+ < ∞)` (`Sandpile.abs_cov_survInd_le`), whose Cesaro
means vanish, so the weighted sum of the `I_i^∞` concentrates at the rate
`ε^{-1} (n^{-1} ∑_{m≤n}(ρ_m - ρ_∞))^{1/2}`.  The mean is
`G(0,0)^{-1} ∑_{i≤j} (n-i)^{-1}`, and the harmonic segment differs from
`-log(1 - j/n)` by at most `(n-j)^{-1}`.

The three errors are collected in `Sandpile.lastVisit_eventually`, which is the
lemma in the vocabulary of `Sandpile.visitInd`; the frozen statement reads the
same sum through the paper's indicator `I_{i,j}`.
-/
import Sandpile.Support.LinEscape
import Sandpile.Support.LinHarmonic

open LatticeProb

open MeasureTheory Filter Topology

namespace Sandpile
variable {d : ℕ}

/-- The distance between two times, as a natural number. -/
def lag (i i' : ℕ) : ℕ := (i - i') + (i' - i)

theorem lag_self_add (i k : ℕ) : lag i (i + k) = k := by unfold lag; omega

theorem lag_comm (i i' : ℕ) : lag i i' = lag i' i := by unfold lag; omega

theorem lag_le_of_le {i i' : ℕ} (h : i' ≤ i) : lag i i' = i - i' := by unfold lag; omega

theorem lag_le_of_ge {i i' : ℕ} (h : i ≤ i') : lag i i' = i' - i := by unfold lag; omega

theorem abs_cov_pair_le [NeZero d] (i i' : ℕ) :
    |(∫ X, survInd i X * survInd i' X ∂(walkLaw d 0)) - escProb d * escProb d|
      ≤ 2 * (retProb d (lag i i') - escProb d) := by
  rcases le_total i i' with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [lag_self_add]
    exact abs_cov_survInd_le i k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [lag_comm, lag_self_add]
    have h2 := abs_cov_survInd_le (d := d) i' k
    have hcomm : ∀ X : ℕ → Site d, survInd (i' + k) X * survInd i' X
        = survInd i' X * survInd (i' + k) X := fun X => mul_comm _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hcomm)]
    exact h2

theorem sum_lag_le (N : ℕ) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) (i : ℕ) (hi : i < N) :
    ∑ i' ∈ Finset.range N, f (lag i i') ≤ 2 * ∑ m ∈ Finset.range N, f m := by
  classical
  set s₁ : Finset ℕ := (Finset.range N).filter (fun i' => i' ≤ i) with hs₁
  set s₂ : Finset ℕ := (Finset.range N).filter (fun i' => ¬ i' ≤ i) with hs₂
  have hsplit : ∑ i' ∈ Finset.range N, f (lag i i')
      = (∑ i' ∈ s₁, f (lag i i')) + ∑ i' ∈ s₂, f (lag i i') :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun i' => i' ≤ i)
      (fun i' => f (lag i i'))).symm
  have h1 : ∑ i' ∈ s₁, f (lag i i') ≤ ∑ m ∈ Finset.range N, f m := by
    have hcongr : ∑ i' ∈ s₁, f (lag i i') = ∑ i' ∈ s₁, f (i - i') := by
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [lag_le_of_le (Finset.mem_filter.mp hi').2]
    have hinj : ∀ x ∈ s₁, ∀ y ∈ s₁, i - x = i - y → x = y := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      omega
    have hsub : s₁.image (fun i' => i - i') ⊆ Finset.range N := by
      intro m hm
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_range.mpr (by omega)
    rw [hcongr, ← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hf m
  have h2 : ∑ i' ∈ s₂, f (lag i i') ≤ ∑ m ∈ Finset.range N, f m := by
    have hcongr : ∑ i' ∈ s₂, f (lag i i') = ∑ i' ∈ s₂, f (i' - i) := by
      refine Finset.sum_congr rfl fun i' hi' => ?_
      have := (Finset.mem_filter.mp hi').2
      rw [lag_le_of_ge (by omega)]
    have hinj : ∀ x ∈ s₂, ∀ y ∈ s₂, x - i = y - i → x = y := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      omega
    have hsub : s₂.image (fun i' => i' - i) ⊆ Finset.range N := by
      intro m hm
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hm
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
      exact Finset.mem_range.mpr (by omega)
    rw [hcongr, ← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hf m
  rw [hsplit]
  linarith

theorem integral_sq_finsum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hint2 : ∀ i ∈ s, ∀ i' ∈ s, Integrable (fun ω => f i ω * f i' ω) μ) :
    ∫ ω, (∑ i ∈ s, f i ω) ^ 2 ∂μ = ∑ i ∈ s, ∑ i' ∈ s, ∫ ω, f i ω * f i' ω ∂μ := by
  have hpt : ∀ ω, (∑ i ∈ s, f i ω) ^ 2 = ∑ i ∈ s, ∑ i' ∈ s, f i ω * f i' ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_finsetSum s (fun i hi => integrable_finsetSum s fun i' hi' => hint2 i hi i' hi')]
  exact Finset.sum_congr rfl fun i hi =>
    integral_finsetSum s (fun i' hi' => hint2 i hi i' hi')

/-- The centred survival indicators have the covariance of the survival
indicators. -/
theorem integral_centered_mul [NeZero d] (i i' : ℕ) :
    ∫ X, (survInd i X - escProb d) * (survInd i' X - escProb d) ∂(walkLaw d 0)
      = (∫ X, survInd i X * survInd i' X ∂(walkLaw d 0)) - escProb d * escProb d := by
  have hii' : Integrable (fun X : ℕ → Site d => survInd i X * survInd i' X) (walkLaw d 0) :=
    integrable_of_bdd ((measurable_survInd i).mul (measurable_survInd i')) (C := 1) fun X => by
      rw [abs_mul, abs_of_nonneg (survInd_nonneg i X), abs_of_nonneg (survInd_nonneg i' X)]
      exact mul_le_one₀ (survInd_le_one i X) (survInd_nonneg i' X) (survInd_le_one i' X)
  have hpt : ∀ X : ℕ → Site d,
      (survInd i X - escProb d) * (survInd i' X - escProb d)
        = survInd i X * survInd i' X - escProb d * survInd i X - escProb d * survInd i' X
          + escProb d * escProb d := by
    intro X; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have h1 : Integrable (fun X : ℕ → Site d =>
      survInd i X * survInd i' X - escProb d * survInd i X) (walkLaw d 0) :=
    hii'.sub ((integrable_survInd i).const_mul _)
  have h2 : Integrable (fun X : ℕ → Site d =>
      survInd i X * survInd i' X - escProb d * survInd i X - escProb d * survInd i' X)
      (walkLaw d 0) := h1.sub ((integrable_survInd i').const_mul _)
  rw [integral_add h2 (integrable_const _), integral_sub h1 ((integrable_survInd i').const_mul _),
    integral_sub hii' ((integrable_survInd i).const_mul _), integral_const_mul, integral_const_mul,
    integral_survInd i, integral_survInd i', integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

/-! ### The two weighted sums -/

noncomputable def wcoef (n i : ℕ) : ℝ := 1 / ((n : ℝ) - (i : ℝ))

noncomputable def lvSum (n j : ℕ) (X : ℕ → Site d) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), visitInd i (j - i) X * wcoef n i

noncomputable def svSum (n j : ℕ) (X : ℕ → Site d) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), survInd i X * wcoef n i

/-- `∑_{m ≤ n} (ρ_m - ρ_∞)`, the paper's `∑_{k≤n} P_0(k < τ_0^+ < ∞)`. -/
noncomputable def tailSum (d n : ℕ) : ℝ := ∑ m ∈ Finset.range (n + 1), (retProb d m - escProb d)

theorem wcoef_pos {n i : ℕ} (h : i < n) : 0 < wcoef n i := by
  have : (i : ℝ) < (n : ℝ) := by exact_mod_cast h
  unfold wcoef
  positivity

theorem wcoef_le {n i j : ℕ} (hij : i ≤ j) (hj : j < n) : wcoef n i ≤ wcoef n j := by
  have hi : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  unfold wcoef
  apply one_div_le_one_div_of_le (by linarith)
  linarith

theorem integrable_lvSum [NeZero d] (n j : ℕ) : Integrable (lvSum (d := d) n j) (walkLaw d 0) :=
  integrable_finsetSum _ fun i _ => (integrable_visitInd i (j - i)).mul_const _

theorem integrable_svSum [NeZero d] (n j : ℕ) : Integrable (svSum (d := d) n j) (walkLaw d 0) :=
  integrable_finsetSum _ fun i _ => (integrable_survInd i).mul_const _

theorem integral_lvSum [NeZero d] (n j : ℕ) :
    ∫ X, lvSum (d := d) n j X ∂(walkLaw d 0)
      = ∑ i ∈ Finset.range (j + 1), retProb d (j - i) * wcoef n i := by
  simp only [lvSum]
  rw [integral_finsetSum _ fun i _ => (integrable_visitInd i (j - i)).mul_const _]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_mul_const, integral_visitInd i (j - i)]

theorem integral_svSum [NeZero d] (n j : ℕ) :
    ∫ X, svSum (d := d) n j X ∂(walkLaw d 0)
      = ∑ i ∈ Finset.range (j + 1), escProb d * wcoef n i := by
  simp only [svSum]
  rw [integral_finsetSum _ fun i _ => (integrable_survInd i).mul_const _]
  exact Finset.sum_congr rfl fun i _ => by
    rw [integral_mul_const, integral_survInd i]

theorem svSum_le_lvSum [NeZero d] {n j : ℕ} (hj : j < n) (X : ℕ → Site d) :
    svSum (d := d) n j X ≤ lvSum (d := d) n j X := by
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact mul_le_mul_of_nonneg_right (survInd_le_visitInd i (j - i) X)
    (le_of_lt (wcoef_pos (lt_of_le_of_lt hij hj)))

theorem retProb_sub_escProb_nonneg [NeZero d] (m : ℕ) : 0 ≤ retProb d m - escProb d :=
  sub_nonneg.mpr (escProb_le_retProb m)

theorem tailSum_nonneg [NeZero d] (n : ℕ) : 0 ≤ tailSum d n :=
  Finset.sum_nonneg fun m _ => retProb_sub_escProb_nonneg m

/-- The paper's step "`I_{i,j} - I_i^∞` occurs precisely when the first return
is finite and later than `j`". -/
theorem integral_abs_lvSum_sub_svSum_le [NeZero d] {n j : ℕ} (hj : j < n) :
    ∫ X, |lvSum (d := d) n j X - svSum (d := d) n j X| ∂(walkLaw d 0)
      ≤ tailSum d n * wcoef n j := by
  have habs : ∀ X : ℕ → Site d,
      |lvSum (d := d) n j X - svSum (d := d) n j X|
        = lvSum (d := d) n j X - svSum (d := d) n j X := fun X =>
    abs_of_nonneg (sub_nonneg.mpr (svSum_le_lvSum hj X))
  rw [integral_congr_ae (Filter.Eventually.of_forall habs),
    integral_sub (integrable_lvSum n j) (integrable_svSum n j), integral_lvSum, integral_svSum,
    ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      retProb d (j - i) * wcoef n i - escProb d * wcoef n i
        ≤ (retProb d (j - i) - escProb d) * wcoef n j := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : retProb d (j - i) * wcoef n i - escProb d * wcoef n i
        = (retProb d (j - i) - escProb d) * wcoef n i := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (wcoef_le hij hj) (retProb_sub_escProb_nonneg (j - i))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (wcoef_pos hj))
  have hre : ∑ i ∈ Finset.range (j + 1), (retProb d (j - i) - escProb d)
      = ∑ m ∈ Finset.range (j + 1), (retProb d m - escProb d) := by
    have := Finset.sum_range_reflect (fun m => retProb d m - escProb d) (j + 1)
    simpa using this
  rw [hre]
  simp only [tailSum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => retProb_sub_escProb_nonneg m
  intro m hm
  exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hm; omega)

/-! ### The variance of the survival sum -/

theorem abs_survInd_sub_escProb_le [NeZero d] (i : ℕ) (X : ℕ → Site d) :
    |survInd i X - escProb d| ≤ 1 := by
  have h1 : escProb d ≤ 1 := le_trans (escProb_le_retProb 0) (retProb_le_one 0)
  have h2 : (0 : ℝ) ≤ escProb d := escProb_nonneg
  have h3 := survInd_nonneg i X
  have h4 := survInd_le_one i X
  rw [abs_le]
  constructor <;> linarith

theorem integrable_centered_mul [NeZero d] (n i i' : ℕ) :
    Integrable (fun X : ℕ → Site d =>
      (survInd i X - escProb d) * wcoef n i * ((survInd i' X - escProb d) * wcoef n i'))
      (walkLaw d 0) := by
  refine integrable_of_bdd (((measurable_survInd i).sub measurable_const).mul measurable_const
    |>.mul (((measurable_survInd i').sub measurable_const).mul measurable_const))
    (C := |wcoef n i| * |wcoef n i'|) fun X => ?_
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |survInd i X - escProb d| * |wcoef n i| ≤ 1 * |wcoef n i| :=
    mul_le_mul_of_nonneg_right (abs_survInd_sub_escProb_le i X) (abs_nonneg _)
  have h2 : |survInd i' X - escProb d| * |wcoef n i'| ≤ 1 * |wcoef n i'| :=
    mul_le_mul_of_nonneg_right (abs_survInd_sub_escProb_le i' X) (abs_nonneg _)
  have hn1 : 0 ≤ |survInd i X - escProb d| * |wcoef n i| := by positivity
  calc |survInd i X - escProb d| * |wcoef n i| *
        (|survInd i' X - escProb d| * |wcoef n i'|)
      ≤ (1 * |wcoef n i|) * (1 * |wcoef n i'|) := by
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = |wcoef n i| * |wcoef n i'| := by ring

theorem svSum_sub_integral [NeZero d] (n j : ℕ) (X : ℕ → Site d) :
    svSum (d := d) n j X - ∫ Y, svSum (d := d) n j Y ∂(walkLaw d 0)
      = ∑ i ∈ Finset.range (j + 1), (survInd i X - escProb d) * wcoef n i := by
  rw [integral_svSum]
  simp only [svSum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integral_sq_svSum_sub [NeZero d] {n j : ℕ} (hj : j < n) :
    ∫ X, (svSum (d := d) n j X - ∫ Y, svSum (d := d) n j Y ∂(walkLaw d 0)) ^ 2 ∂(walkLaw d 0)
      ≤ 4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2 := by
  have hwj : 0 < wcoef n j := wcoef_pos hj
  rw [integral_congr_ae (Filter.Eventually.of_forall fun X => by
      rw [svSum_sub_integral (d := d) n j X]),
    integral_sq_finsum _ _ _ fun i _ i' _ => integrable_centered_mul n i i']
  have hterm : ∀ i ∈ Finset.range (j + 1), ∀ i' ∈ Finset.range (j + 1),
      (∫ X, (survInd i X - escProb d) * wcoef n i * ((survInd i' X - escProb d) * wcoef n i')
        ∂(walkLaw d 0))
        ≤ 2 * (retProb d (lag i i') - escProb d) * (wcoef n j) ^ 2 := by
    intro i hi i' hi'
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hij' : i' ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    have hwi : 0 < wcoef n i := wcoef_pos (lt_of_le_of_lt hij hj)
    have hwi' : 0 < wcoef n i' := wcoef_pos (lt_of_le_of_lt hij' hj)
    have hrw : ∀ X : ℕ → Site d,
        (survInd i X - escProb d) * wcoef n i * ((survInd i' X - escProb d) * wcoef n i')
          = (wcoef n i * wcoef n i') *
            ((survInd i X - escProb d) * (survInd i' X - escProb d)) := fun X => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw), integral_const_mul,
      integral_centered_mul]
    have hcov := abs_cov_pair_le (d := d) i i'
    have hcov' := (abs_le.mp hcov).2
    have hprod : wcoef n i * wcoef n i' ≤ (wcoef n j) ^ 2 := by
      have := mul_le_mul (wcoef_le hij hj) (wcoef_le hij' hj) (le_of_lt hwi')
        (le_of_lt (wcoef_pos hj))
      nlinarith [this]
    have hnn : 0 ≤ 2 * (retProb d (lag i i') - escProb d) := by
      have := retProb_sub_escProb_nonneg (d := d) (lag i i'); linarith
    nlinarith [hcov', hprod, mul_pos hwi hwi', hnn]
  refine le_trans (Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun i' hi' => hterm i hi i' hi') ?_
  have hrow : ∀ i ∈ Finset.range (j + 1),
      ∑ i' ∈ Finset.range (j + 1), 2 * (retProb d (lag i i') - escProb d) * (wcoef n j) ^ 2
        ≤ 4 * tailSum d n * (wcoef n j) ^ 2 := by
    intro i hi
    have hlagsum := sum_lag_le (j + 1) (fun m => retProb d m - escProb d)
      (fun m => retProb_sub_escProb_nonneg m) i (Finset.mem_range.mp hi)
    have hsub : ∑ m ∈ Finset.range (j + 1), (retProb d m - escProb d) ≤ tailSum d n := by
      simp only [tailSum]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => retProb_sub_escProb_nonneg m
      intro m hm
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hm; omega)
    have hfac : ∑ i' ∈ Finset.range (j + 1),
        2 * (retProb d (lag i i') - escProb d) * (wcoef n j) ^ 2
        = (2 * (wcoef n j) ^ 2) *
          ∑ i' ∈ Finset.range (j + 1), (retProb d (lag i i') - escProb d) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i' _ => by ring
    rw [hfac]
    have hwsq : 0 < (wcoef n j) ^ 2 := by positivity
    nlinarith [hlagsum, hsub, hwsq]
  refine le_trans (Finset.sum_le_sum hrow) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [this]
  nlinarith [tailSum_nonneg (d := d) n, sq_nonneg (wcoef n j)]

/-! ### From the variance to the mean absolute deviation -/

theorem measurable_svSum (n j : ℕ) : Measurable (svSum (d := d) n j) :=
  Finset.measurable_sum _ fun i _ => (measurable_survInd i).mul_const _

theorem abs_svSum_le (n j : ℕ) (X : ℕ → Site d) :
    |svSum (d := d) n j X| ≤ ∑ i ∈ Finset.range (j + 1), |wcoef n i| := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  rw [abs_of_nonneg (survInd_nonneg i X)]
  exact survInd_le_one i X

theorem integral_abs_svSum_sub_le [NeZero d] {n j : ℕ} (hj : j < n) :
    ∫ X, |svSum (d := d) n j X - ∫ Y, svSum (d := d) n j Y ∂(walkLaw d 0)| ∂(walkLaw d 0)
      ≤ Real.sqrt (4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2) := by
  set m : ℝ := ∫ Y, svSum (d := d) n j Y ∂(walkLaw d 0) with hm
  set V : ℝ := 4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2 with hV
  have hVnn : 0 ≤ V := by
    have h1 := tailSum_nonneg (d := d) n
    have h2 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have h3 : (0 : ℝ) ≤ (wcoef n j) ^ 2 := sq_nonneg _
    rw [hV]; positivity
  have hbase : Integrable (fun X : ℕ → Site d => svSum (d := d) n j X - m) (walkLaw d 0) :=
    (integrable_svSum n j).sub (integrable_const _)
  have habs : Integrable (fun X : ℕ → Site d => |svSum (d := d) n j X - m|) (walkLaw d 0) :=
    hbase.abs
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |wcoef n i| with hK
  have hsq : Integrable (fun X : ℕ → Site d => |svSum (d := d) n j X - m| ^ 2) (walkLaw d 0) := by
    refine integrable_of_bdd (((measurable_svSum n j).sub measurable_const).abs.pow_const 2)
      (C := (K + |m|) ^ 2) fun X => ?_
    have h1 : |svSum (d := d) n j X - m| ≤ K + |m| := by
      have ha := abs_svSum_le (d := d) n j X
      have hb : |svSum (d := d) n j X - m| ≤ |svSum (d := d) n j X| + |m| := abs_sub _ _
      rw [hK]; linarith
    have h2 : 0 ≤ |svSum (d := d) n j X - m| := abs_nonneg _
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ |svSum (d := d) n j X - m| ^ 2)]
    exact pow_le_pow_left₀ h2 h1 2
  have hcs := sq_integral_le (walkLaw d 0) (fun X => |svSum (d := d) n j X - m|) habs hsq
  have hid : ∀ X : ℕ → Site d, |svSum (d := d) n j X - m| ^ 2
      = (svSum (d := d) n j X - m) ^ 2 := fun X => sq_abs _
  rw [integral_congr_ae (Filter.Eventually.of_forall hid)] at hcs
  have hle : ∫ X, (svSum (d := d) n j X - m) ^ 2 ∂(walkLaw d 0) ≤ V := integral_sq_svSum_sub hj
  have hnn : 0 ≤ ∫ X, |svSum (d := d) n j X - m| ∂(walkLaw d 0) :=
    integral_nonneg fun X => abs_nonneg _
  calc ∫ X, |svSum (d := d) n j X - m| ∂(walkLaw d 0)
      = Real.sqrt ((∫ X, |svSum (d := d) n j X - m| ∂(walkLaw d 0)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt V := Real.sqrt_le_sqrt (le_trans hcs hle)

/-! ### The last-visit estimate -/

theorem one_le_green (hd : 3 ≤ d) : (1 : ℝ) ≤ green d 0 0 := by
  have h := LatticeProb.one_le_srwGreenInf_origin (d := d) hd
  rw [Sandpile.External.Sec16.green_eq d 0 0, sub_zero]
  exact h

theorem measurable_lvSum (n j : ℕ) : Measurable (lvSum (d := d) n j) :=
  Finset.measurable_sum _ fun i _ => (measurable_visitInd i (j - i)).mul_const _

theorem integral_abs_main_le [NeZero d] (hd : 3 ≤ d) {n j : ℕ} (hj : j < n) (hn : 0 < n) :
    ∫ X, |green d 0 0 * lvSum (d := d) n j X + Real.log (1 - (j : ℝ) / (n : ℝ))|
        ∂(walkLaw d 0)
      ≤ green d 0 0 * (tailSum d n * wcoef n j)
        + green d 0 0 * Real.sqrt (4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2)
        + wcoef n j := by
  have hG1' : (1 : ℝ) ≤ green d 0 0 := one_le_green hd
  have hne : green d 0 0 ≠ 0 := by linarith
  have hesc' : green d 0 0 * escProb d = 1 := by
    rw [escProb_eq hd, mul_one_div, div_self hne]
  set G : ℝ := green d 0 0 with hGdef
  have hG1 : (1 : ℝ) ≤ G := hG1'
  have hG0 : (0 : ℝ) < G := by linarith
  set m : ℝ := ∫ Y, svSum (d := d) n j Y ∂(walkLaw d 0) with hm
  set L : ℝ := Real.log (1 - (j : ℝ) / (n : ℝ)) with hL
  -- the deterministic term
  have hGm : G * m + L
      = (∑ i ∈ Finset.range (j + 1), (1 : ℝ) / ((n : ℝ) - (i : ℝ))) + L := by
    rw [hm, integral_svSum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hesc : G * escProb d = 1 := hesc'
    calc G * (escProb d * wcoef n i) = (G * escProb d) * wcoef n i := by ring
      _ = wcoef n i := by rw [hesc, one_mul]
      _ = (1 : ℝ) / ((n : ℝ) - (i : ℝ)) := rfl
  have hdet : |G * m + L| ≤ wcoef n j := by
    rw [hGm, hL]
    exact abs_harm_log n j hj hn
  -- the pointwise decomposition
  have hpt : ∀ X : ℕ → Site d,
      |G * lvSum (d := d) n j X + L|
        ≤ G * |lvSum (d := d) n j X - svSum (d := d) n j X|
          + G * |svSum (d := d) n j X - m| + |G * m + L| := by
    intro X
    have hsplit : G * lvSum (d := d) n j X + L
        = G * (lvSum (d := d) n j X - svSum (d := d) n j X)
          + G * (svSum (d := d) n j X - m) + (G * m + L) := by ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    refine add_le_add (le_trans (abs_add_le _ _) ?_) le_rfl
    rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt hG0)]
  -- integrability
  have hint1 : Integrable (fun X : ℕ → Site d =>
      |lvSum (d := d) n j X - svSum (d := d) n j X|) (walkLaw d 0) :=
    ((integrable_lvSum n j).sub (integrable_svSum n j)).abs
  have hint2 : Integrable (fun X : ℕ → Site d => |svSum (d := d) n j X - m|)
      (walkLaw d 0) := ((integrable_svSum n j).sub (integrable_const _)).abs
  have hintL : Integrable (fun X : ℕ → Site d =>
      |G * lvSum (d := d) n j X + L|) (walkLaw d 0) :=
    (((integrable_lvSum n j).const_mul G).add (integrable_const _)).abs
  have hintR : Integrable (fun X : ℕ → Site d =>
      G * |lvSum (d := d) n j X - svSum (d := d) n j X|
        + G * |svSum (d := d) n j X - m| + |G * m + L|) (walkLaw d 0) :=
    ((hint1.const_mul G).add (hint2.const_mul G)).add (integrable_const _)
  have hsum1 : Integrable (fun X : ℕ → Site d =>
      G * |lvSum (d := d) n j X - svSum (d := d) n j X|
        + G * |svSum (d := d) n j X - m|) (walkLaw d 0) :=
    (hint1.const_mul G).add (hint2.const_mul G)
  refine le_trans (integral_mono hintL hintR hpt) ?_
  rw [integral_add hsum1 (integrable_const _),
    integral_add (hint1.const_mul G) (hint2.const_mul G), integral_const_mul, integral_const_mul,
    integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  have hA := integral_abs_lvSum_sub_svSum_le (d := d) hj
  have hB := integral_abs_svSum_sub_le (d := d) hj
  have hsqrtnn : 0 ≤ Real.sqrt (4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2) :=
    Real.sqrt_nonneg _
  nlinarith [hA, hB, hdet, hG0]

theorem tendsto_tailSum_div [NeZero d] :
    Tendsto (fun n : ℕ => tailSum d n / (n : ℝ)) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  have hc := cesaro_small (fun m => retProb d m - escProb d) tendsto_retProb (η / 2)
    (by linarith)
  filter_upwards [hc, eventually_ge_atTop 1] with n hcn hn1
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnn : 0 ≤ tailSum d n := tailSum_nonneg n
  have hcn' : tailSum d n ≤ η / 2 * (n : ℝ) := hcn
  have hle : tailSum d n / (n : ℝ) ≤ η / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

/-- **The last-visit estimate.**  This is `sandpile.tex:4755-4771`
(label `lem:dgt4-weighted-last-visits`) in the vocabulary of `visitInd`. -/
theorem lastVisit_eventually [NeZero d] (hd : 3 ≤ d) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ ⌊(1 - ε) * (n : ℝ)⌋₊ →
      ∫ X, |green d 0 0 * lvSum (d := d) n j X + Real.log (1 - (j : ℝ) / (n : ℝ))|
        ∂(walkLaw d 0) ≤ η := by
  have hG1 : (1 : ℝ) ≤ green d 0 0 := one_le_green hd
  have hG0 : (0 : ℝ) < green d 0 0 := by linarith
  set G : ℝ := green d 0 0 with hGdef
  set u : ℕ → ℝ := fun n => tailSum d n / (n : ℝ) with hu
  have hut : Tendsto u atTop (nhds 0) := tendsto_tailSum_div
  have h1 : Tendsto (fun n : ℕ => G / ε * u n) atTop (nhds 0) := by
    simpa using hut.const_mul (G / ε)
  have h2 : Tendsto (fun n : ℕ => G * Real.sqrt (8 / ε ^ 2 * u n)) atTop (nhds 0) := by
    have hs : Tendsto (fun n : ℕ => 8 / ε ^ 2 * u n) atTop (nhds 0) := by
      simpa using hut.const_mul (8 / ε ^ 2)
    have hsq : Tendsto (fun n : ℕ => Real.sqrt (8 / ε ^ 2 * u n)) atTop (nhds 0) := by
      have hcomp := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
      simpa [Function.comp_def, Real.sqrt_zero] using hcomp
    simpa using hsq.const_mul G
  have h3 : Tendsto (fun n : ℕ => 1 / (ε * (n : ℝ))) atTop (nhds 0) := by
    have hb : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have heq : ∀ n : ℕ, (1 / ε) * ((1 : ℝ) / (n : ℝ)) = 1 / (ε * (n : ℝ)) := by
      intro n; rw [div_mul_div_comm, one_mul]
    have hc : Tendsto (fun n : ℕ => (1 / ε) * ((1 : ℝ) / (n : ℝ))) atTop
        (nhds ((1 / ε) * 0)) := hb.const_mul _
    rw [mul_zero] at hc
    exact hc.congr heq
  have hbound : Tendsto (fun n : ℕ =>
      G / ε * u n + G * Real.sqrt (8 / ε ^ 2 * u n) + 1 / (ε * (n : ℝ))) atTop (nhds 0) := by
    simpa using (h1.add h2).add h3
  filter_upwards [eventually_ge_atTop 1, hbound.eventually_lt_const hη] with n hn1 hbn
  intro j hj
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : 0 < n := hn1
  have hfloor : (0 : ℝ) ≤ (1 - ε) * (n : ℝ) := by
    have : (0 : ℝ) ≤ 1 - ε := by linarith
    positivity
  have hjr : (j : ℝ) ≤ (1 - ε) * (n : ℝ) :=
    le_trans (by exact_mod_cast Nat.cast_le.mpr hj) (Nat.floor_le hfloor)
  have hεn : 0 < ε * (n : ℝ) := by positivity
  have hjn : (j : ℝ) < (n : ℝ) := by nlinarith [hjr, hεn]
  have hjlt : j < n := by exact_mod_cast hjn
  have hgap : ε * (n : ℝ) ≤ (n : ℝ) - (j : ℝ) := by nlinarith [hjr]
  have hgap0 : (0 : ℝ) < ε * (n : ℝ) := by positivity
  have hw : wcoef n j ≤ 1 / (ε * (n : ℝ)) := by
    unfold wcoef
    exact one_div_le_one_div_of_le hgap0 hgap
  have hw0 : 0 < wcoef n j := wcoef_pos hjlt
  have hT : 0 ≤ tailSum d n := tailSum_nonneg n
  -- the three pieces
  have hp1 : G * (tailSum d n * wcoef n j) ≤ G / ε * u n := by
    have : tailSum d n * wcoef n j ≤ tailSum d n * (1 / (ε * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hw hT
    have hueq : G / ε * u n = G * (tailSum d n * (1 / (ε * (n : ℝ)))) := by
      rw [hu]
      field_simp
    rw [hueq]
    exact mul_le_mul_of_nonneg_left this (le_of_lt hG0)
  have hp2 : 4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2 ≤ 8 / ε ^ 2 * u n := by
    have hj2 : (j : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
    have hwsq : (wcoef n j) ^ 2 ≤ (1 / (ε * (n : ℝ))) ^ 2 := by
      have := hw
      nlinarith [hw0.le, hw]
    have hueq : 8 / ε ^ 2 * u n = 8 * (n : ℝ) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2 := by
      rw [hu]
      field_simp
    rw [hueq]
    have hstep1 : 4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2
        ≤ 4 * ((j : ℝ) + 1) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2 := by
      have hnn : 0 ≤ 4 * ((j : ℝ) + 1) * tailSum d n := by positivity
      exact mul_le_mul_of_nonneg_left hwsq hnn
    have hstep2 : 4 * ((j : ℝ) + 1) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2
        ≤ 8 * (n : ℝ) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2 := by
      have hkey : 4 * ((j : ℝ) + 1) ≤ 8 * (n : ℝ) := by linarith
      have hnn2 : 0 ≤ tailSum d n * (1 / (ε * (n : ℝ))) ^ 2 := by positivity
      calc 4 * ((j : ℝ) + 1) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2
          = (4 * ((j : ℝ) + 1)) * (tailSum d n * (1 / (ε * (n : ℝ))) ^ 2) := by ring
        _ ≤ (8 * (n : ℝ)) * (tailSum d n * (1 / (ε * (n : ℝ))) ^ 2) :=
            mul_le_mul_of_nonneg_right hkey hnn2
        _ = 8 * (n : ℝ) * tailSum d n * (1 / (ε * (n : ℝ))) ^ 2 := by ring
    linarith
  have hp2' : G * Real.sqrt (4 * ((j : ℝ) + 1) * tailSum d n * (wcoef n j) ^ 2)
      ≤ G * Real.sqrt (8 / ε ^ 2 * u n) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp2) (le_of_lt hG0)
  have hmain := integral_abs_main_le (d := d) hd hjlt hn0
  linarith [hmain, hp1, hp2', hw, hbn]

end Sandpile
