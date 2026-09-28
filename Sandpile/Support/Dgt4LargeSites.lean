import Sandpile.Support.Dgt4CaseBStep1
import Sandpile.Support.Dgt4LowerTailMoment

/-!
# Step 1 of case (b), reduced to its conditional deviation estimate

Step 1 of case (b) of `prop:dgt4-contact-asymptotics` (`sandpile.tex:5349-5381`), reduced to its
conditional deviation estimate.

Step 1 proves `eq:dgt4-small-origin-neighbor-average`,
`\P(Pw_n(0)\leq\E Pw_n(0)/6)/\P(-\zeta(0)>\E Pw_n(0))\to0`, by splitting according to the number
of sites of the box that carry an unusually large contribution:
`A_n=\{z\in Q(0,n+1)\setminus\{0\}:-G(0,z)\zeta(z)/G(0,0)>\eta_n\E Pw_n(0)\}` with
`\eta_n=1/(K\log\E Pw_n(0))`.

Two of the three pieces are proved here. The first is the estimate
`\P(|A_n|\geq2)\leq C(p)(\eta_n\E Pw_n(0))^{-2p}=o(\P(-\zeta(0)>\E Pw_n(0)))`
(`sandpile.tex:5357-5359`): the events `\{z\in A_n\}` are events of distinct coordinates of the
i.i.d. field and are therefore independent (`iidLaw_two_site`); at least two of finitely many
pairwise independent events occur with probability at most the square of the sum of their
probabilities (`measure_two_le_sq_of_pairwise_indep`); Markov's inequality at exponent `p` bounds
the one-site probability by `\E|\zeta(0)|^p(c_z/t)^p`; and the sum of `c_z^p` over the box is
bounded by the convergent series of `eq:dgt4-green-tail`. Nothing in this chain needs the site
weights to be strictly positive: a site of weight zero simply never belongs to `A_n`, and the
one-site bound is then trivial. The second piece is the splitting itself,
`measure_inter_card_le_one_le`, together with the comparison of the conditional bound with the
lower tail.

What remains is `SmallAverageConditional`, the conditional deviation estimate of
`sandpile.tex:5361-5381`: given that at most one site carries a large contribution, the neighbour
average falls below a sixth of its mean with conditional probability at most
`(\E Pw_n(0))^{-\beta}`. That is the Freedman step of the paper, and it is the only remaining
input of the heavy-tailed branch of `prop:dgt4-contact-asymptotics`.
-/

open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- Markov's inequality for one site of `A_n`: the probability that the weighted scenery
value at `z` exceeds the level `t` is at most `\E|\zeta(0)|^p (c_z/t)^p`.  A site of weight
zero carries an empty event, so no positivity of the weight is needed. -/
theorem measure_site_threshold_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (z : Sandpile.Site d) {c t p : ℝ} (hc : 0 ≤ c) (hp : 0 < p)
    (hmom : Integrable (fun y : ℝ => |y| ^ p) ν) (ht : 0 < t) :
    ((LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | t < -(c * ζ z)}).toReal
      ≤ (∫ y, |y| ^ p ∂ν) * c ^ p / t ^ p := by
  have hMnn : (0 : ℝ) ≤ ∫ y, |y| ^ p ∂ν :=
    integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg y) p
  have htp : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hmapz : (LatticeProb.iidLaw d ν).map (fun ζ : Sandpile.Site d → ℝ => ζ z) = ν :=
    MeasureTheory.Measure.infinitePi_map_eval (fun _ : Sandpile.Site d => ν) z
  have hmeasB : MeasurableSet {y : ℝ | t < -(c * y)} := by
    have hm : Measurable fun y : ℝ => -(c * y) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hval : (LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | t < -(c * ζ z)}
      = ν {y : ℝ | t < -(c * y)} := by
    rw [show {ζ : Sandpile.Site d → ℝ | t < -(c * ζ z)}
        = (fun ζ : Sandpile.Site d → ℝ => ζ z) ⁻¹' {y : ℝ | t < -(c * y)} from rfl,
      ← MeasureTheory.Measure.map_apply (measurable_pi_apply z) hmeasB, hmapz]
  rw [hval]
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hempty : {y : ℝ | t < -(c * y)} = (∅ : Set ℝ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt, ← hc0,
        zero_mul, neg_zero]
      linarith
    rw [hempty]
    simp only [measure_empty, ENNReal.toReal_zero]
    rw [← hc0, Real.zero_rpow (ne_of_gt hp)]
    simp
  · have hIio : {y : ℝ | t < -(c * y)} = Set.Iio (-(t / c)) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_Iio, ← neg_div, lt_div_iff₀ hcpos]
      constructor <;> intro h <;> nlinarith [mul_comm y c]
    rw [hIio]
    have hkey := lowerTail_div_le_moment_mul ν hp hmom hcpos ht
    have h2 : (ν (Set.Iio (-(t / c)))).toReal = LatticeProb.lowerTail ν (t / c) := rfl
    rw [h2]
    refine hkey.trans (le_of_eq ?_)
    rw [Real.div_rpow hcpos.le ht.le]
    field_simp



/-- The one-site threshold event is a coordinate event, and the coordinate has law `\nu`. -/
theorem measure_site_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : Sandpile.Site d)
    (c t : ℝ) :
    (LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | t < -(c * ζ z)}
      = ν {y : ℝ | t < -(c * y)} := by
  have hmeasB : MeasurableSet {y : ℝ | t < -(c * y)} := by
    have hm : Measurable fun y : ℝ => -(c * y) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hmapz : (LatticeProb.iidLaw d ν).map (fun ζ : Sandpile.Site d → ℝ => ζ z) = ν :=
    MeasureTheory.Measure.infinitePi_map_eval (fun _ : Sandpile.Site d => ν) z
  rw [show {ζ : Sandpile.Site d → ℝ | t < -(c * ζ z)}
      = (fun ζ : Sandpile.Site d → ℝ => ζ z) ⁻¹' {y : ℝ | t < -(c * y)} from rfl,
    ← MeasureTheory.Measure.map_apply (measurable_pi_apply z) hmeasB, hmapz]

/-- `\P(|A_n|\geq2)\leq(\sum_z\P(z\in A_n))^2` of `sandpile.tex:5352-5354`: the one-site
events are events of distinct coordinates of the i.i.d. field, hence independent. -/
theorem measure_two_large_sites_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Sandpile.Site d)) (c : Sandpile.Site d → ℝ) (t : ℝ) :
    (LatticeProb.iidLaw d ν)
        {ζ | 2 ≤ (s.filter fun z => t < -(c z * ζ z)).card}
      ≤ (∑ z ∈ s, (LatticeProb.iidLaw d ν)
          {ζ : Sandpile.Site d → ℝ | t < -(c z * ζ z)}) ^ 2 := by
  have hmeasB : ∀ z : Sandpile.Site d, MeasurableSet {y : ℝ | t < -(c z * y)} := by
    intro z
    have hm : Measurable fun y : ℝ => -(c z * y) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hindep : ∀ z₁ z₂ : Sandpile.Site d, z₁ ≠ z₂ →
      (LatticeProb.iidLaw d ν)
          ({ζ : Sandpile.Site d → ℝ | t < -(c z₁ * ζ z₁)} ∩
            {ζ : Sandpile.Site d → ℝ | t < -(c z₂ * ζ z₂)})
        = (LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | t < -(c z₁ * ζ z₁)} *
          (LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | t < -(c z₂ * ζ z₂)} := by
    intro z₁ z₂ hz
    have hcap : {ζ : Sandpile.Site d → ℝ | t < -(c z₁ * ζ z₁)} ∩
        {ζ : Sandpile.Site d → ℝ | t < -(c z₂ * ζ z₂)}
        = {ζ : Sandpile.Site d → ℝ |
            ζ z₁ ∈ {y : ℝ | t < -(c z₁ * y)} ∧ ζ z₂ ∈ {y : ℝ | t < -(c z₂ * y)}} := rfl
    rw [hcap, iidLaw_two_site ν hz (hmeasB z₁) (hmeasB z₂), measure_site_eq ν z₁,
      measure_site_eq ν z₂]
  exact measure_two_le_sq_of_pairwise_indep (P := LatticeProb.iidLaw d ν) s
    (fun z => {ζ : Sandpile.Site d → ℝ | t < -(c z * ζ z)}) hindep

/-- The bound of `measure_two_large_sites_le`, with the one-site probabilities each bounded
by Markov's inequality (`measure_site_threshold_le`): the probability that at least two sites
of `s` exceed the threshold `t`, weighted by `c`, is at most the square of
`(∫|z|^p dν) (∑_{z ∈ s} c z^p) / t^p`. -/
theorem measure_two_large_sites_le_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Sandpile.Site d)) (c : Sandpile.Site d → ℝ) (hc : ∀ z, 0 ≤ c z)
    {p t : ℝ} (hp : 0 < p) (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) (ht : 0 < t) :
    ((LatticeProb.iidLaw d ν)
        {ζ | 2 ≤ (s.filter fun z => t < -(c z * ζ z)).card}).toReal
      ≤ ((∫ z, |z| ^ p ∂ν) * (∑ z ∈ s, c z ^ p) / t ^ p) ^ 2 := by
  have hMnn : 0 ≤ ∫ z, |z| ^ p ∂ν :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg z) p
  have htp : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hsum : (∑ z ∈ s, (LatticeProb.iidLaw d ν)
        {ζ : Sandpile.Site d → ℝ | t < -(c z * ζ z)}).toReal
      ≤ (∫ z, |z| ^ p ∂ν) * (∑ z ∈ s, c z ^ p) / t ^ p := by
    rw [ENNReal.toReal_sum (fun z _ => measure_ne_top _ _)]
    refine le_trans (Finset.sum_le_sum
      (fun z _ => measure_site_threshold_le ν z (hc z) hp hmom ht)) (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.sum_div]
  have hle := measure_two_large_sites_le ν s c t
  have hfin : (∑ z ∈ s, (LatticeProb.iidLaw d ν)
      {ζ : Sandpile.Site d → ℝ | t < -(c z * ζ z)}) ^ 2 ≠ ⊤ := by
    refine ENNReal.pow_ne_top ?_
    exact (ENNReal.sum_lt_top.mpr fun z _ => measure_lt_top _ _).ne
  have h1 : ((LatticeProb.iidLaw d ν)
      {ζ | 2 ≤ (s.filter fun z => t < -(c z * ζ z)).card}).toReal
      ≤ ((∑ z ∈ s, (LatticeProb.iidLaw d ν)
          {ζ : Sandpile.Site d → ℝ | t < -(c z * ζ z)}) ^ 2).toReal :=
    ENNReal.toReal_mono hfin hle
  refine h1.trans ?_
  rw [ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hsum 2

/-- `measure_two_large_sites_le_moment`, with the finite weight sum `∑_{z ∈ s} c z^p` replaced
by the tail of a summable dominating family `b` with `c z^p ≤ b z`, so the bound holds
uniformly over `s` with `∑' z, b z` in place of the finite sum. -/
theorem measure_two_large_sites_le_tsum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : Finset (Sandpile.Site d)) (c : Sandpile.Site d → ℝ) (hc : ∀ z, 0 ≤ c z)
    {p t : ℝ} (hp : 0 < p) (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) (ht : 0 < t)
    (b : Sandpile.Site d → ℝ) (hbnn : ∀ z, 0 ≤ b z) (hb : ∀ z, c z ^ p ≤ b z)
    (hsum : Summable b) :
    ((LatticeProb.iidLaw d ν)
        {ζ | 2 ≤ (s.filter fun z => t < -(c z * ζ z)).card}).toReal
      ≤ ((∫ z, |z| ^ p ∂ν) * (∑' z, b z) / t ^ p) ^ 2 := by
  refine (measure_two_large_sites_le_moment ν s c hc hp hmom ht).trans ?_
  have hMnn : 0 ≤ ∫ z, |z| ^ p ∂ν :=
    integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg z) p
  have htp : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht p
  have hle : ∑ z ∈ s, c z ^ p ≤ ∑' z, b z :=
    le_trans (Finset.sum_le_sum fun z _ => hb z) (hsum.sum_le_tsum s fun z _ => hbnn z)
  have hnn : 0 ≤ (∫ z, |z| ^ p ∂ν) * (∑ z ∈ s, c z ^ p) / t ^ p := by
    have hs : 0 ≤ ∑ z ∈ s, c z ^ p :=
      Finset.sum_nonneg fun z _ => Real.rpow_nonneg (hc z) p
    positivity
  refine pow_le_pow_left₀ hnn ?_ 2
  gcongr


/-- `\P(|A_n|\geq2)=o(\P(-\zeta(0)>\E Pw_n(0)))` (`sandpile.tex:5353-5354`), for any site
weights whose `p`-th powers are dominated by a summable family and any exhaustion of the
lattice by boxes. -/
theorem tendsto_measure_two_large_sites_div_lowerTail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α p K : ℝ}
    (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (c b : Sandpile.Site d → ℝ) (hc : ∀ z, 0 ≤ c z) (hbnn : ∀ z, 0 ≤ b z)
    (hb : ∀ z, c z ^ p ≤ b z) (hsumb : Summable b)
    (s : ℕ → Finset (Sandpile.Site d)) (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ =>
        ((LatticeProb.iidLaw d ν)
            {ζ | 2 ≤ ((s n).filter fun z =>
              a n / (K * Real.log (a n)) < -(c z * ζ z)).card}).toReal
          / LatticeProb.lowerTail ν (a n)) atTop (𝓝 0) := by
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    LatticeProb.pos_of_antitone_of_eventually_pos (LatticeProb.antitone_lowerTail ν)
      (LatticeProb.eventually_pos_of_regularlyVarying hrv (LatticeProb.lowerTail_nonneg ν))
  have hmain := tendsto_level_pow_div_lowerTail ν (α := α) (p := p) (K := K)
    (A := (∫ z, |z| ^ p ∂ν) * (∑' z : Sandpile.Site d, b z)) hpα hK hrv a ha
  refine squeeze_zero' ?_ ?_ hmain
  · filter_upwards with n
    exact div_nonneg ENNReal.toReal_nonneg (hTpos _).le
  · filter_upwards [ha.eventually_ge_atTop (Real.exp 1)] with n hn
    have hx0 : (0 : ℝ) < a n := lt_of_lt_of_le (Real.exp_pos 1) hn
    have hL : (1 : ℝ) ≤ Real.log (a n) := by
      have h := Real.log_le_log (Real.exp_pos 1) hn
      rwa [Real.log_exp] at h
    have hL0 : (0 : ℝ) < Real.log (a n) := lt_of_lt_of_le one_pos hL
    have ht : (0 : ℝ) < a n / (K * Real.log (a n)) := by positivity
    have hnum := measure_two_large_sites_le_tsum ν (s n) c hc hp hmom ht b hbnn hb hsumb
    exact div_le_div_of_nonneg_right hnum (hTpos (a n)).le

/-- The first estimate of Step 1 of case (b), at the weights of `A_n`. -/
theorem tendsto_measure_two_large_sites_green_div_lowerTail
    (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α p K : ℝ}
    (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p)
    (s : ℕ → Finset (Sandpile.Site d)) (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ =>
        ((LatticeProb.iidLaw d ν)
            {ζ | 2 ≤ ((s n).filter fun z =>
              a n / (K * Real.log (a n)) <
                -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z)).card}).toReal
          / LatticeProb.lowerTail ν (a n)) atTop (𝓝 0) := by
  have hcnn : ∀ z : Sandpile.Site d, 0 ≤ Sandpile.green d 0 z / Sandpile.green d 0 0 := by
    intro z
    rw [greenRatio_eq_hitProb (by omega) z]
    exact LatticeProb.srwHitProb_nonneg z
  exact tendsto_measure_two_large_sites_div_lowerTail ν hp hpα hK hmom hrv
    (fun z => Sandpile.green d 0 z / Sandpile.green d 0 0)
    (fun z => (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p) hcnn
    (fun z => Real.rpow_nonneg (hcnn z) p) (fun z => le_rfl) hsumc s a ha


/-- `\E Pw_n(0)`, the mean of the neighbour average of the odometer killed at the origin. -/
noncomputable def meanOriginAverage (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)

/-- `A_n` of `sandpile.tex:5350-5351`. -/
noncomputable def largeSites (d : ℕ) (ν : Measure ℝ) (K : ℝ) (n : ℕ)
    (ζ : Sandpile.Site d → ℝ) : Finset (Sandpile.Site d) :=
  ((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0).filter fun z =>
    meanOriginAverage d ν n / (K * Real.log (meanOriginAverage d ν n)) <
      -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z)

/-- The conditional deviation estimate of Step 1 (`sandpile.tex:5356-5376`). -/
def SmallAverageConditional (d : ℕ) (ν : Measure ℝ) (K β : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ B : Finset (Sandpile.Site d), B.card ≤ 1 →
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6}
          ∩ {ζ | largeSites d ν K n ζ = B})
      ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) *
        (LatticeProb.iidLaw d ν) {ζ | largeSites d ν K n ζ = B}

/-- **One coordinate of the i.i.d. field is independent of every quantity that does not read
it.**  This is the product structure behind the conditioning of `sandpile.tex:5356-5363`, in
the only form Step 1 uses. -/
theorem measure_inter_site_indep (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (i : Sandpile.Site d) {W : (Sandpile.Site d → ℝ) → ℝ} (hW : Measurable W)
    (hWloc : ∀ (ζ : Sandpile.Site d → ℝ) (z : ℝ), W (Function.update ζ i z) = W ζ)
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (LatticeProb.iidLaw d ν) {ζ | ζ i ∈ A ∧ W ζ ∈ B}
      = ν A * (LatticeProb.iidLaw d ν) {ζ | W ζ ∈ B} := by
  set P := LatticeProb.iidLaw d ν with hP
  set f : ℝ → ℝ → ℝ := fun z w =>
    A.indicator (fun _ => (1 : ℝ)) z * B.indicator (fun _ => (1 : ℝ)) w with hf
  have hiA : Measurable (A.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hiB : Measurable (B.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hB
  have hfm : Measurable fun q : ℝ × ℝ => f q.1 q.2 :=
    (hiA.comp measurable_fst).mul (hiB.comp measurable_snd)
  have hbound : ∀ z w : ℝ, |f z w| ≤ 1 := by
    intro z w
    have h1 : |A.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
      by_cases h : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have h2 : |B.indicator (fun _ => (1 : ℝ)) w| ≤ 1 := by
      by_cases h : w ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    rw [hf, abs_mul]
    nlinarith [abs_nonneg (A.indicator (fun _ => (1 : ℝ)) z),
      abs_nonneg (B.indicator (fun _ => (1 : ℝ)) w)]
  have hint : Integrable (fun q : ℝ × (Sandpile.Site d → ℝ) => f q.1 (W q.2)) (ν.prod P) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((hfm.comp (measurable_fst.prodMk (hW.comp measurable_snd))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun q => ?_)
    simpa using hbound q.1 (W q.2)
  have hsplit := integral_iidLaw_split ν i hfm hW hWloc hint
  have hS : MeasurableSet {ζ : Sandpile.Site d → ℝ | ζ i ∈ A ∧ W ζ ∈ B} :=
    ((measurable_pi_apply i) hA).inter (hW hB)
  have hT : MeasurableSet {ζ : Sandpile.Site d → ℝ | W ζ ∈ B} := hW hB
  have hlhs : ∫ ζ, f (ζ i) (W ζ) ∂P = (P {ζ : Sandpile.Site d → ℝ | ζ i ∈ A ∧ W ζ ∈ B}).toReal := by
    have hcongr : (fun ζ : Sandpile.Site d → ℝ => f (ζ i) (W ζ))
        = Set.indicator {ζ : Sandpile.Site d → ℝ | ζ i ∈ A ∧ W ζ ∈ B} (fun _ => (1 : ℝ)) := by
      funext ζ
      by_cases h1 : ζ i ∈ A <;> by_cases h2 : W ζ ∈ B <;>
        simp [hf, Set.indicator_apply, h1, h2]
    rw [hcongr, MeasureTheory.integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one,
      measureReal_def]
  have hinner : ∀ ζ : Sandpile.Site d → ℝ,
      (∫ z, f z (W ζ) ∂ν) = (ν A).toReal * B.indicator (fun _ => (1 : ℝ)) (W ζ) := by
    intro ζ
    rw [hf]
    simp only
    rw [integral_mul_const, MeasureTheory.integral_indicator_const (1 : ℝ) hA, smul_eq_mul,
      mul_one, measureReal_def]
  have hrhs : ∫ ζ, (∫ z, f z (W ζ) ∂ν) ∂P
      = (ν A).toReal * (P {ζ : Sandpile.Site d → ℝ | W ζ ∈ B}).toReal := by
    have hcongr2 : (fun ζ : Sandpile.Site d → ℝ => B.indicator (fun _ => (1 : ℝ)) (W ζ))
        = Set.indicator {ζ : Sandpile.Site d → ℝ | W ζ ∈ B} (fun _ => (1 : ℝ)) := by
      funext ζ
      by_cases h2 : W ζ ∈ B <;> simp [h2]
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_const_mul, hcongr2,
      MeasureTheory.integral_indicator_const (1 : ℝ) hT, smul_eq_mul, mul_one, measureReal_def]
  rw [hlhs, hrhs] at hsplit
  have hfin1 : P {ζ : Sandpile.Site d → ℝ | ζ i ∈ A ∧ W ζ ∈ B} ≠ ⊤ := measure_ne_top _ _
  have hfin2 : ν A * P {ζ : Sandpile.Site d → ℝ | W ζ ∈ B} ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  refine (ENNReal.toReal_eq_toReal_iff' hfin1 hfin2).mp ?_
  rw [ENNReal.toReal_mul]
  exact hsplit

/-- **Step 1 of case (b) from any bound on the small event with at most one large site.**
The event that the neighbour average falls below a sixth of its mean splits according to
whether at least two sites carry a large contribution; the first alternative is negligible
against the lower tail by `tendsto_measure_two_large_sites_green_div_lowerTail`, and the
second is whatever the bound `e` gives. -/
theorem smallOriginNeighborAverage_of_measure_bound
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K : ℝ} (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p)
    (e : ℕ → ℝ) (hennn : ∀ᶠ n : ℕ in atTop, 0 ≤ e n)
    (he : Tendsto (fun n : ℕ => e n / LatticeProb.lowerTail ν (meanOriginAverage d ν n))
      atTop (𝓝 0))
    (hb : ∀ᶠ n : ℕ in atTop, (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6} ∩
          {ζ | (largeSites d ν K n ζ).card ≤ 1}) ≤ ENNReal.ofReal (e n)) :
    SmallOriginNeighborAverage d ν := by
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmean hvar hvar'
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    LatticeProb.pos_of_antitone_of_eventually_pos (LatticeProb.antitone_lowerTail ν)
      (LatticeProb.eventually_pos_of_regularlyVarying hrv (LatticeProb.lowerTail_nonneg ν))
  have h2 := tendsto_measure_two_large_sites_green_div_lowerTail hd ν hp hpα hK hmom hrv hsumc
      (fun n => (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0)
      (meanOriginAverage d ν) hainf
  have hsum := he.add h2
  rw [add_zero] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards with n
    exact div_nonneg ENNReal.toReal_nonneg (hTpos _).le
  · filter_upwards [hb, hennn, hainf.eventually_gt_atTop 0] with n hn hen hpos
    set G : Set (Sandpile.Site d → ℝ) :=
      {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6} with hG
    set S1 : Set (Sandpile.Site d → ℝ) :=
      {ζ | (((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0).filter fun z =>
        meanOriginAverage d ν n / (K * Real.log (meanOriginAverage d ν n)) <
          -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z)).card ≤ 1} with hS1
    set S2 : Set (Sandpile.Site d → ℝ) :=
      {ζ | 2 ≤ (((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0).filter fun z =>
        meanOriginAverage d ν n / (K * Real.log (meanOriginAverage d ν n)) <
          -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z)).card} with hS2
    have hlow : (LatticeProb.iidLaw d ν) (G ∩ S1) ≤ ENNReal.ofReal (e n) := hn
    have hsplit : G ⊆ (G ∩ S1) ∪ S2 := by
      intro ζ hζ
      by_cases h : ζ ∈ S1
      · exact Or.inl ⟨hζ, h⟩
      · refine Or.inr ?_
        rw [hS2, Set.mem_setOf_eq]
        rw [hS1, Set.mem_setOf_eq] at h
        omega
    have hmle : (LatticeProb.iidLaw d ν) G
        ≤ ENNReal.ofReal (e n) + (LatticeProb.iidLaw d ν) S2 := by
      refine le_trans (measure_mono hsplit) ?_
      refine le_trans (measure_union_le _ _) ?_
      exact add_le_add hlow le_rfl
    have hfin : ENNReal.ofReal (e n) + (LatticeProb.iidLaw d ν) S2 ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩
    have htr : ((LatticeProb.iidLaw d ν) G).toReal
        ≤ e n + ((LatticeProb.iidLaw d ν) S2).toReal := by
      refine le_trans (ENNReal.toReal_mono hfin hmle) (le_of_eq ?_)
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
        ENNReal.toReal_ofReal hen]
    have hTn := hTpos (meanOriginAverage d ν n)
    calc ((LatticeProb.iidLaw d ν) G).toReal /
          LatticeProb.lowerTail ν (meanOriginAverage d ν n)
        ≤ (e n + ((LatticeProb.iidLaw d ν) S2).toReal) /
          LatticeProb.lowerTail ν (meanOriginAverage d ν n) :=
          div_le_div_of_nonneg_right htr hTn.le
      _ = e n / LatticeProb.lowerTail ν (meanOriginAverage d ν n) +
          ((LatticeProb.iidLaw d ν) S2).toReal /
            LatticeProb.lowerTail ν (meanOriginAverage d ν n) := by
          rw [add_div]

/-- **Step 1 of case (b) from its conditional deviation estimate.**
`eq:dgt4-small-origin-neighbor-average` (`sandpile.tex:5344-5346`) follows from
`SmallAverageConditional` alone. -/
theorem smallOriginNeighborAverage_of_conditional
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K β : ℝ} (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K) (hβ : α < β)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p)
    (hcond : SmallAverageConditional d ν K β) :
    SmallOriginNeighborAverage d ν := by
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmean hvar hvar'
  refine smallOriginNeighborAverage_of_measure_bound hGH hd ν hatom hmean hvar hvar'
    hp hpα hK hmom hrv hsumc (fun n => meanOriginAverage d ν n ^ (-β)) ?_
    (tendsto_rpow_neg_div_lowerTail ν hβ hrv (meanOriginAverage d ν) hainf) ?_
  · filter_upwards [hainf.eventually_gt_atTop 0] with n hpos
    exact Real.rpow_nonneg hpos.le _
  · filter_upwards [hcond] with n hn
    have hmeasQ : ∀ z : Sandpile.Site d, MeasurableSet
        {ζ : Sandpile.Site d → ℝ | meanOriginAverage d ν n /
          (K * Real.log (meanOriginAverage d ν n)) <
            -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z)} := by
      intro z
      have hm : Measurable fun ζ : Sandpile.Site d → ℝ =>
          -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z) := by fun_prop
      exact measurableSet_lt measurable_const hm
    exact measure_inter_card_le_one_le (LatticeProb.iidLaw d ν)
      ((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0)
      (fun z ζ => meanOriginAverage d ν n /
        (K * Real.log (meanOriginAverage d ν n)) <
          -((Sandpile.green d 0 z / Sandpile.green d 0 0) * ζ z))
      hmeasQ
      {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6}
      (ENNReal.ofReal (meanOriginAverage d ν n ^ (-β))) hn



/-- Step 1 with `eq:dgt4-green-tail` supplied at an exponent `p\geq2`, where the
square-summability of the influences already gives the `p`-th power sum. -/
theorem smallOriginNeighborAverage_of_conditional_two_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K β : ℝ} (hp2 : 2 ≤ p) (hpα : α < 2 * p) (hK : 0 < K) (hβ : α < β)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hcond : SmallAverageConditional d ν K β) :
    SmallOriginNeighborAverage d ν :=
  smallOriginNeighborAverage_of_conditional hGH hd ν hatom hmean hvar hvar'
    (lt_of_lt_of_le two_pos hp2) hpα hK hβ hmom hrv (summable_greenRatio_rpow hGH hd hp2) hcond

/-- Case (b) of `prop:dgt4-contact-asymptotics` from the conditional deviation estimate of
Step 1 alone. -/
theorem caseThresholdField_linear_of_conditional
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K β : ℝ} (hα : 1 < α) (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K) (hβ : α < β)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p)
    (hcond : SmallAverageConditional d ν K β) :
    CaseThresholdField d ν (1 - 1 / α) :=
  caseThresholdField_linear_of_smallOriginNeighborAverage hGH d hd ν hatom hmean hvar hvar'
    hα hrv
    (smallOriginNeighborAverage_of_conditional hGH hd ν hatom hmean hvar hvar'
      hp hpα hK hβ hmom hrv hsumc hcond)

end Sandpile
