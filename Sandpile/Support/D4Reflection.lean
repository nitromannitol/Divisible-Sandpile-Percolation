import Sandpile.Support.D4Mean
import Sandpile.Support.HeightLower

/-!
# The reflection window: nonnegativity, domination, and its mean

Step 3 of `prop:d4-pointwise-linearization` (`sandpile.tex:3128-3186`). The window of reflection
terms `reflectionSum ζ n t x = ∑_{k<n} P^k r_{t-1-k}(x)`, with `r_s = (-ζ - P u_s)_+`, is
nonnegative (`reflectionSum_nonneg`) and is below `u_t(x) - V_t(x)`
(`reflectionSum_le_diffField`). Its mean is the growth of the mean odometer over the window,
`E u_t(0) - E u_{t-n}(0)` (`integral_reflectionSum`), which the concavity of the mean odometer
bounds by `(n/(t-n)) E u_{t-n}(0)` (`meanOdometerOf_window_le`). The last section bounds the two
tails of the window around its mean: a Markov bound (`measure_reflectionSum_markov`) and, once the
level exceeds twice the mean, an exponential bound inherited from the tail of `u_t - V_t`
(`measure_reflectionSum_tail_four`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The window `∑_{k<n} P^k r_{t-1-k}` of `eq:d4-proof-two-terms`. -/
noncomputable def reflectionSum (ζ : Site d → ℝ) (n t : ℕ) (x : Site d) : ℝ :=
  ∑ k ∈ Finset.range n, (avg^[k] (reflectionTerm ζ (t - 1 - k))) x

/-- Iterating the averaging operator `avg` preserves nonnegativity of `f`. -/
theorem avg_iterate_nonneg {f : Site d → ℝ} (hf : ∀ y, 0 ≤ f y) (k : ℕ) (x : Site d) :
    0 ≤ (avg^[k] f) x := by
  have h := avg_iterate_mono (d := d) k (f := fun _ => (0 : ℝ)) (g := f) hf x
  rwa [avg_iterate_zero] at h

/-- The window `reflectionSum` is nonnegative, as a sum of nonnegative averaged reflection
terms. -/
theorem reflectionSum_nonneg (ζ : Site d → ℝ) (n t : ℕ) (x : Site d) :
    0 ≤ reflectionSum ζ n t x :=
  Finset.sum_nonneg fun k _ => avg_iterate_nonneg (reflectionTerm_nonneg ζ _) k x

/-- `u_t - V_t ≥ 0`: the reflection only adds. -/
theorem diffField_nonneg (ζ : Site d → ℝ) : ∀ (t : ℕ) (x : Site d), 0 ≤ diffField ζ t x := by
  intro t
  induction t with
  | zero => intro x; rw [diffField_zero]
  | succ s ih =>
      intro x
      rw [diffField_succ]
      have h1 : 0 ≤ avg (diffField ζ s) x := avg_nonneg ih x
      have h2 : 0 ≤ reflectionTerm ζ s x := reflectionTerm_nonneg ζ s x
      linarith

/-- The window is below the difference (`sandpile.tex:3172-3178`). -/
theorem reflectionSum_le_diffField (ζ : Site d → ℝ) {n t : ℕ} (hn : n ≤ t) (x : Site d) :
    reflectionSum ζ n t x ≤ diffField ζ t x := by
  rw [diffField_decomp ζ n t hn x]
  have h := avg_iterate_nonneg (d := d) (diffField_nonneg ζ (t - n)) n x
  rw [reflectionSum]
  linarith

/-! ### The mean of the window -/

/-- Rewrites the reflection term via the odometer recursion
`odometerOf_succ_eq_add_reflection`. -/
theorem reflectionTerm_eq_sub (ζ : Site d → ℝ) (s : ℕ) (y : Site d) :
    reflectionTerm ζ s y = odometerOf ζ (s + 1) y - ζ y - avg (odometerOf ζ s) y := by
  rw [odometerOf_succ_eq_add_reflection ζ s y]; ring

/-- The averaged odometer `avg (odometerOf ζ s)` is integrable, since `avg` unfolds to a finite
heat-kernel-weighted sum of integrable odometer values (`integrable_odometerOf`). -/
theorem integrable_avg_odometerOf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (s : ℕ) (y : Site d) :
    Integrable (fun ζ : Site d → ℝ => avg (odometerOf ζ s) y) (LatticeProb.iidLaw d ν) := by
  classical
  have hrw : ∀ ζ : Site d → ℝ, avg (odometerOf ζ s) y
      = ∑ z ∈ boxFinset y 1, heatKernel d 1 y z * odometerOf ζ s z := by
    intro ζ
    have h : avg (odometerOf ζ s) y = (avg^[1] fun z => odometerOf ζ s z) y := by
      rw [Function.iterate_one]
    rw [h, avg_iterate, tsum_heatKernel_mul_eq_sum]
  refine Integrable.congr ?_ (Filter.Eventually.of_forall fun ζ => (hrw ζ).symm)
  exact integrable_finsetSum _ fun z _ => (integrable_odometerOf d ν hpos s z).const_mul _

/-- The reflection term `reflectionTerm ζ s` is integrable, by rewriting it via
`reflectionTerm_eq_sub` as a difference of integrable odometer, coordinate, and
averaged-odometer terms. -/
theorem integrable_reflectionTerm (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) (s : ℕ)
    (y : Site d) :
    Integrable (fun ζ : Site d → ℝ => reflectionTerm ζ s y) (LatticeProb.iidLaw d ν) := by
  refine Integrable.congr ?_
    (Filter.Eventually.of_forall fun ζ => (reflectionTerm_eq_sub ζ s y).symm)
  exact ((integrable_odometerOf d ν hpos (s + 1) y).sub (integrable_coord ν hint y)).sub
    (integrable_avg_odometerOf ν hpos s y)

/-- The mean of a reflection term is the increment of the mean odometer, at
every site. -/
theorem integral_reflectionTerm (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (s : ℕ) (y : Site d) :
    ∫ ζ, reflectionTerm ζ s y ∂(LatticeProb.iidLaw d ν)
      = (∫ ζ, odometerOf ζ (s + 1) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ s 0 ∂(LatticeProb.iidLaw d ν) := by
  have hI1 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (s + 1) y)
      (LatticeProb.iidLaw d ν) := integrable_odometerOf d ν hpos (s + 1) y
  have hI2 : Integrable (fun ζ : Site d → ℝ => ζ y) (LatticeProb.iidLaw d ν) :=
    integrable_coord ν hint y
  have hI3 : Integrable (fun ζ : Site d → ℝ => avg (odometerOf ζ s) y)
      (LatticeProb.iidLaw d ν) := integrable_avg_odometerOf ν hpos s y
  have hI12 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (s + 1) y - ζ y)
      (LatticeProb.iidLaw d ν) := hI1.sub hI2
  have hA : ∫ ζ : Site d → ℝ, (odometerOf ζ (s + 1) y - ζ y - avg (odometerOf ζ s) y)
        ∂(LatticeProb.iidLaw d ν)
      = (∫ ζ : Site d → ℝ, (odometerOf ζ (s + 1) y - ζ y) ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ : Site d → ℝ, avg (odometerOf ζ s) y ∂(LatticeProb.iidLaw d ν) :=
    integral_sub hI12 hI3
  have hB : ∫ ζ : Site d → ℝ, (odometerOf ζ (s + 1) y - ζ y) ∂(LatticeProb.iidLaw d ν)
      = (∫ ζ : Site d → ℝ, odometerOf ζ (s + 1) y ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ : Site d → ℝ, ζ y ∂(LatticeProb.iidLaw d ν) := integral_sub hI1 hI2
  have hC : ∫ ζ : Site d → ℝ, avg (odometerOf ζ s) y ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, odometerOf ζ s 0 ∂(LatticeProb.iidLaw d ν) := by
    have h1 : ∫ ζ : Site d → ℝ, avg (odometerOf ζ s) y ∂(LatticeProb.iidLaw d ν)
        = ∫ ζ, (avg^[1] fun z => odometerOf ζ s z) y ∂(LatticeProb.iidLaw d ν) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      rw [Function.iterate_one]
    rw [h1, integral_avg_odometerOf hd ν hpos 1 s y]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ => reflectionTerm_eq_sub ζ s y),
    hA, hB, hC, integral_coord ν hint, hmean, sub_zero,
    integral_odometerOf_eq d ν (s + 1) y]

/-- Smoothing does not move the mean of a reflection term. -/
theorem integral_avg_iterate_reflectionTerm (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (k s : ℕ) (x : Site d) :
    ∫ ζ, (avg^[k] (reflectionTerm ζ s)) x ∂(LatticeProb.iidLaw d ν)
      = (∫ ζ, odometerOf ζ (s + 1) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ s 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  have hrw : ∀ ζ : Site d → ℝ, (avg^[k] (reflectionTerm ζ s)) x
      = ∑ z ∈ boxFinset x k, heatKernel d k x z * reflectionTerm ζ s z := by
    intro ζ
    rw [avg_iterate, tsum_heatKernel_mul_eq_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    integral_finsetSum _ fun z _ => (integrable_reflectionTerm ν hint hpos s z).const_mul _]
  have hz : ∀ z ∈ boxFinset x k,
      ∫ ζ, heatKernel d k x z * reflectionTerm ζ s z ∂(LatticeProb.iidLaw d ν)
        = heatKernel d k x z * ((∫ ζ, odometerOf ζ (s + 1) 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ s 0 ∂(LatticeProb.iidLaw d ν)) := by
    intro z _
    rw [integral_const_mul, integral_reflectionTerm hd ν hint hmean hpos s z]
  rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, sum_heatKernel_boxFinset hd k x, one_mul]

/-- Each iterated average `avg^[k] (reflectionTerm ζ s)` is integrable, by unfolding it as a
finite heat-kernel-weighted sum of integrable reflection terms (`integrable_reflectionTerm`). -/
theorem integrable_avg_iterate_reflectionTerm (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) (k s : ℕ)
    (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => (avg^[k] (reflectionTerm ζ s)) x)
      (LatticeProb.iidLaw d ν) := by
  classical
  have hrw : ∀ ζ : Site d → ℝ, (avg^[k] (reflectionTerm ζ s)) x
      = ∑ z ∈ boxFinset x k, heatKernel d k x z * reflectionTerm ζ s z := by
    intro ζ
    rw [avg_iterate, tsum_heatKernel_mul_eq_sum]
  refine Integrable.congr ?_ (Filter.Eventually.of_forall fun ζ => (hrw ζ).symm)
  exact integrable_finsetSum _ fun z _ => (integrable_reflectionTerm ν hint hpos s z).const_mul _

/-- The window `reflectionSum ζ n t` is integrable, as a finite sum of integrable iterated
averages of reflection terms. -/
theorem integrable_reflectionSum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν) (n t : ℕ)
    (x : Site d) :
    Integrable (fun ζ : Site d → ℝ => reflectionSum ζ n t x) (LatticeProb.iidLaw d ν) :=
  integrable_finsetSum _ fun k _ =>
    integrable_avg_iterate_reflectionTerm ν hint hpos k (t - 1 - k) x

/-- **The mean of the window is the growth of the mean odometer over the
window** (`sandpile.tex:3144-3153`). -/
theorem integral_reflectionSum (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (x : Site d) :
    ∀ n t : ℕ, n ≤ t →
      ∫ ζ, reflectionSum ζ n t x ∂(LatticeProb.iidLaw d ν)
        = (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ (t - n) 0 ∂(LatticeProb.iidLaw d ν) := by
  intro n
  induction n with
  | zero =>
      intro t _
      have h : ∀ ζ : Site d → ℝ, reflectionSum ζ 0 t x = 0 := fun ζ => by
        rw [reflectionSum]; simp
      rw [integral_congr_ae (Filter.Eventually.of_forall h)]
      simp
  | succ n ih =>
      intro t hn
      have hnt : n ≤ t := by omega
      have hidx : t - 1 - n = t - (n + 1) := by omega
      have hidx2 : (t - 1 - n) + 1 = t - n := by omega
      have hsplit : ∀ ζ : Site d → ℝ, reflectionSum ζ (n + 1) t x
          = reflectionSum ζ n t x + (avg^[n] (reflectionTerm ζ (t - 1 - n))) x := fun ζ => by
        rw [reflectionSum, reflectionSum, Finset.sum_range_succ]
      rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
        integral_add (integrable_reflectionSum ν hint hpos n t x)
          (integrable_avg_iterate_reflectionTerm ν hint hpos n (t - 1 - n) x),
        ih t hnt, integral_avg_iterate_reflectionTerm hd ν hint hmean hpos n (t - 1 - n) x,
        hidx2, hidx]
      ring

/-- **The window bound** `eq:d4-reflection-window-mean-bound`: the increments of
the mean odometer are nonincreasing, so the last `n` of them are at most
`n/(t-n)` times the first `t-n`. -/
theorem meanOdometerOf_window_le (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n t : ℕ) (hn : n ≤ t) :
    ((t - n : ℕ) : ℝ) * ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ (t - n) 0 ∂(LatticeProb.iidLaw d ν))
      ≤ (n : ℝ) * ∫ ζ, odometerOf ζ (t - n) 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set m : ℕ → ℝ := fun j => ∫ ζ, odometerOf ζ j 0 ∂P with hmdef
  set D : ℕ → ℝ := fun j => m (j + 1) - m j with hD
  have hm0 : m 0 = 0 := by simp [hmdef, odometerOf]
  have hDanti : Antitone D := antitone_nat_of_succ_le fun j =>
    meanOdometerOf_concave hd ν hint hmean hpos j
  have htel : ∀ j : ℕ, ∑ i ∈ Finset.range j, D i = m j := by
    intro j
    have := Finset.sum_range_sub m j
    rw [hm0] at this
    simpa [hD] using this
  have hIco : ∑ i ∈ Finset.Ico (t - n) t, D i = m t - m (t - n) := by
    rw [Finset.sum_Ico_eq_sub _ (by omega : t - n ≤ t), htel, htel]
  have hcard : (Finset.Ico (t - n) t).card = n := by
    rw [Nat.card_Ico]; omega
  have hupper : ∑ i ∈ Finset.Ico (t - n) t, D i ≤ (n : ℝ) * D (t - n) := by
    have h := Finset.sum_le_card_nsmul (Finset.Ico (t - n) t) D (D (t - n))
      (fun i hi => hDanti (Finset.mem_Ico.mp hi).1)
    rw [hcard, nsmul_eq_mul] at h
    exact h
  have hlower : ((t - n : ℕ) : ℝ) * D (t - n) ≤ m (t - n) := by
    have h := Finset.card_nsmul_le_sum (Finset.range (t - n)) D (D (t - n))
      (fun i hi => hDanti (le_of_lt (Finset.mem_range.mp hi)))
    rw [Finset.card_range, nsmul_eq_mul, htel] at h
    exact h
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have htn0 : (0 : ℝ) ≤ ((t - n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((t - n : ℕ) : ℝ) * (m t - m (t - n))
      = ((t - n : ℕ) : ℝ) * ∑ i ∈ Finset.Ico (t - n) t, D i := by rw [hIco]
    _ ≤ ((t - n : ℕ) : ℝ) * ((n : ℝ) * D (t - n)) :=
        mul_le_mul_of_nonneg_left hupper htn0
    _ = (n : ℝ) * (((t - n : ℕ) : ℝ) * D (t - n)) := by ring
    _ ≤ (n : ℝ) * m (t - n) := mul_le_mul_of_nonneg_left hlower hn0

/-! ### The two tails of the window -/

/-- **The Markov bound**, the first branch of
`eq:d4-reflection-window-centered-tail`.  The window is nonnegative, so its
deviation above and below its mean are both controlled by the mean. -/
theorem measure_reflectionSum_markov (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (n t : ℕ) (x : Site d) (u : ℝ) (hu : 0 < u) :
    LatticeProb.iidLaw d ν {ζ : Site d → ℝ | u < |reflectionSum ζ n t x -
        ∫ η, reflectionSum η n t x ∂(LatticeProb.iidLaw d ν)|}
      ≤ ENNReal.ofReal (2 * (∫ η, reflectionSum η n t x ∂(LatticeProb.iidLaw d ν)) / u) := by
  classical
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set EY : ℝ := ∫ η, reflectionSum η n t x ∂P with hEY
  have hEY0 : 0 ≤ EY := integral_nonneg fun ζ => reflectionSum_nonneg ζ n t x
  set A : Set (Site d → ℝ) := {ζ : Site d → ℝ | u < |reflectionSum ζ n t x - EY|} with hA
  rcases lt_or_ge u EY with hbig | hsmall
  · refine le_trans prob_le_one ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hu]
    linarith
  · have hsub : A ⊆ {ζ : Site d → ℝ | u ≤ reflectionSum ζ n t x} := by
      intro ζ hζ
      simp only [hA, Set.mem_setOf_eq] at hζ
      simp only [Set.mem_setOf_eq]
      rcases lt_or_ge (reflectionSum ζ n t x) EY with hle | hgt
      · exfalso
        have h1 : |reflectionSum ζ n t x - EY| = EY - reflectionSum ζ n t x := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [h1] at hζ
        have := reflectionSum_nonneg ζ n t x
        linarith
      · have h1 : |reflectionSum ζ n t x - EY| = reflectionSum ζ n t x - EY := by
          rw [abs_of_nonneg (by linarith)]
        rw [h1] at hζ
        linarith
    have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (f := fun ζ : Site d → ℝ => reflectionSum ζ n t x)
      (Filter.Eventually.of_forall fun ζ => reflectionSum_nonneg ζ n t x)
      (integrable_reflectionSum ν hint hpos n t x) u
    have hreal : P.real A ≤ 2 * EY / u := by
      have h1 : P.real A ≤ P.real {ζ : Site d → ℝ | u ≤ reflectionSum ζ n t x} :=
        measureReal_mono hsub (measure_ne_top _ _)
      rw [le_div_iff₀ hu]
      nlinarith [hmarkov, h1, hEY0, measureReal_nonneg (μ := P) (s := A)]
    have hfin : P A ≠ ⊤ := measure_ne_top _ _
    calc P A = ENNReal.ofReal (P.real A) := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (2 * EY / u) := ENNReal.ofReal_le_ofReal hreal

/-- **The exponential bound**, the second branch of
`eq:d4-reflection-window-centered-tail`.  Once the level is twice the mean, the
window can only deviate upwards, and it is below `u_t - V_t`, whose upper tail
is `lem:d4-difference-tail`. -/
theorem measure_reflectionSum_tail_four (hVS : Sandpile.External.VarianceScale)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ A₀ c C : ℝ, 1 ≤ A₀ ∧ 0 < c ∧ 0 < C ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ w, w ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ n t : ℕ, n ≤ t → 2 ≤ t → ∀ x : Site 4, ∀ u : ℝ,
          2 * (∫ η, reflectionSum η n t x ∂(LatticeProb.iidLaw 4 ν)) ≤ u →
          2 * A₀ * Real.log ((t : ℝ) + 2) ≤ u →
          LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | u < |reflectionSum ζ n t x -
              ∫ η, reflectionSum η n t x ∂(LatticeProb.iidLaw 4 ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * (u / 2 - A₀ * Real.log ((t : ℝ) + 2))))
              / ((t : ℝ) + 2) ^ 2) := by
  classical
  obtain ⟨A₀, c, C, hA₀, hc, hC, hdt⟩ := exists_difference_tail_four hVS θ₀ K₀ hθ₀
  refine ⟨A₀, c, C, hA₀, hc, hC, ?_⟩
  intro ν hprob hmean hexpint hexp n t hnt ht x u hu2 hulog
  haveI := hprob
  set P : Measure (Site 4 → ℝ) := LatticeProb.iidLaw 4 ν with hP
  set EY : ℝ := ∫ η, reflectionSum η n t x ∂P with hEY
  have hEY0 : 0 ≤ EY := integral_nonneg fun ζ => reflectionSum_nonneg ζ n t x
  have hu0 : 0 ≤ u := by linarith
  set v : ℝ := u / 2 - A₀ * Real.log ((t : ℝ) + 2) with hv
  have hv0 : 0 ≤ v := by rw [hv]; linarith
  have hsub : {ζ : Site 4 → ℝ | u < |reflectionSum ζ n t x - EY|}
      ⊆ {ζ : Site 4 → ℝ | A₀ * Real.log ((t : ℝ) + 2) + v <
        odometerOf ζ t x - membrane ζ t x} := by
    intro ζ hζ
    simp only [Set.mem_setOf_eq] at hζ ⊢
    have hYnn : 0 ≤ reflectionSum ζ n t x := reflectionSum_nonneg ζ n t x
    have hhalf : u / 2 < reflectionSum ζ n t x := by
      rcases lt_or_ge (reflectionSum ζ n t x) EY with hle | hgt
      · exfalso
        have h1 : |reflectionSum ζ n t x - EY| = EY - reflectionSum ζ n t x := by
          rw [abs_of_nonpos (by linarith)]; ring
        rw [h1] at hζ
        linarith
      · have h1 : |reflectionSum ζ n t x - EY| = reflectionSum ζ n t x - EY := by
          rw [abs_of_nonneg (by linarith)]
        rw [h1] at hζ
        linarith
    have hle := reflectionSum_le_diffField ζ hnt x
    rw [diffField] at hle
    rw [hv]
    linarith
  calc P {ζ : Site 4 → ℝ | u < |reflectionSum ζ n t x - EY|}
      ≤ P {ζ : Site 4 → ℝ | A₀ * Real.log ((t : ℝ) + 2) + v <
          odometerOf ζ t x - membrane ζ t x} := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * Real.exp (-(c * v)) / ((t : ℝ) + 2) ^ 2) :=
        hdt ν hprob hmean hexpint hexp t ht x v hv0

end Sandpile
