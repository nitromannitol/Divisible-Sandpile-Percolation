/-
"Fix $p\in(\max\{2,\alpha/2\},\alpha)$; regular variation of the lower tail and the upper
bound on the scenery give $\E|\zeta(0)|^p<\infty$" (`sandpile.tex:5352-5353`), the moment
hypothesis with which Step 1 of case (b) of `prop:dgt4-contact-asymptotics` opens.

Both halves of the sentence are used.  The upper bound on the scenery, which the
heavy-tailed branch of the standing hypotheses carries as `\nu(M,\infty)=0`, removes the
upper tail entirely; the lower tail is regularly varying of index `-\alpha`, so Potter's
bound dominates it by `C t^{-\alpha+\delta}` beyond a level, and the layer-cake formula
turns that into a finite `p`-th moment for every `p<\alpha`.  The range that Step 1 needs is
narrower only because `p>\alpha/2` is what makes the second-moment bound on the number of
large contributions beat the tail, and `p\geq2` is what `lem:dgt4-origin-frozen` asks for;
neither plays a role in the finiteness itself.

The module also carries the two other elementary inputs of the opening of Step 1: Markov's
inequality for the lower tail at the exponent `p`, and the bound on the probability that at
least two of finitely many independent events occur.
-/
import LatticeProb.Prob.Karamata

open scoped Classical ENNReal
open MeasureTheory Filter Topology Set

namespace Sandpile

/-- Potter's bound at a fixed base point: an antitone positive regularly varying function of
index `-α` is dominated by a multiple of `s ^ (-α + δ)` beyond a level. -/
theorem exists_le_rpow_of_regularlyVarying {F : ℝ → ℝ} {α : ℝ}
    (hF : LatticeProb.RegularlyVaryingAtTop F (-α)) (hmono : Antitone F)
    (hpos : ∀ r : ℝ, 0 < F r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ 0 ≤ C ∧ ∀ s : ℝ, r₀ ≤ s → F s ≤ C * s ^ (-α + δ) := by
  obtain ⟨r₀, hr₀, h⟩ :=
    LatticeProb.potter_upper hF hmono (Filter.Eventually.of_forall hpos) hδ
  refine ⟨(1 + δ) * F r₀ * r₀ ^ (α - δ), r₀, hr₀,
    mul_nonneg (mul_nonneg (by linarith) (hpos r₀).le) (Real.rpow_nonneg hr₀.le _),
    fun s hs => ?_⟩
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hr₀ hs
  have hkey := h r₀ s le_rfl hs
  rw [div_le_iff₀ (hpos r₀)] at hkey
  refine hkey.trans (le_of_eq ?_)
  rw [Real.div_rpow hs0.le hr₀.le]
  have hcancel : r₀ ^ (-α + δ) * r₀ ^ (α - δ) = 1 := by
    rw [← Real.rpow_add hr₀]
    norm_num
  field_simp
  nlinarith [hcancel, hpos r₀, Real.rpow_pos_of_pos hs0 (-α + δ)]

/-- "regular variation of the lower tail and the upper bound on the scenery give
`\E|\zeta(0)|^p<\infty`" (`sandpile.tex:5347-5348`), for every `p` below the index of
regular variation.  Step 1 of case (b) uses it on the range `(\max\{2,\alpha/2\},\alpha)`,
which lies inside this one because `\alpha>2` there. -/
theorem integrable_abs_rpow_of_lowerTail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {M : ℝ} (hM : ν (Ioi M) = 0) {α p : ℝ} (hp : 0 < p) (hpα : p < α)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α)) :
    Integrable (fun z : ℝ => |z| ^ p) ν := by
  have hpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    LatticeProb.pos_of_antitone_of_eventually_pos (LatticeProb.antitone_lowerTail ν)
      (LatticeProb.eventually_pos_of_regularlyVarying hrv (LatticeProb.lowerTail_nonneg ν))
  have hδ : (0 : ℝ) < (α - p) / 2 := by linarith
  obtain ⟨C, r₀, hr₀, hC, hdom⟩ :=
    exists_le_rpow_of_regularlyVarying hrv (LatticeProb.antitone_lowerTail ν) hpos hδ
  set R : ℝ := max r₀ (max M 1) with hRdef
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_right M 1) (le_max_right r₀ _)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hRr : r₀ ≤ R := le_max_left _ _
  have hRM : M ≤ R := le_trans (le_max_left M 1) (le_max_right r₀ _)
  refine ⟨(Measurable.pow_const measurable_id.abs p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hcong : ∀ z : ℝ, ‖|z| ^ p‖ₑ = ENNReal.ofReal (|z| ^ p) := fun z =>
    Real.enorm_eq_ofReal (Real.rpow_nonneg (abs_nonneg z) p)
  simp_rw [hcong]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (Filter.Eventually.of_forall fun z => abs_nonneg z)
    (measurable_id.abs).aemeasurable hp]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hdisj : Disjoint (Ioc (0 : ℝ) R) (Ioi R) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    exact absurd ht.2 (not_le.mpr ht')
  have hsplit : (∫⁻ t in Ioi (0 : ℝ), ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1)))
      = (∫⁻ t in Ioc (0 : ℝ) R, ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1)))
        + ∫⁻ t in Ioi R, ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1)) := by
    rw [← lintegral_union measurableSet_Ioi hdisj, Set.Ioc_union_Ioi_eq_Ioi hR0.le]
  rw [hsplit]
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · have hle : ∀ t : ℝ, ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal (t ^ (p - 1)) := by
      intro t
      calc ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1))
          ≤ 1 * ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul' prob_le_one le_rfl
        _ = ENNReal.ofReal (t ^ (p - 1)) := one_mul _
    refine lt_of_le_of_lt (lintegral_mono hle) ?_
    have hint : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioc 0 R) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have hfin := hint.2
    rw [hasFiniteIntegral_iff_enorm] at hfin
    exact lt_of_le_of_lt (lintegral_mono fun t => Real.ofReal_le_enorm _) hfin
  · set e : ℝ := -α + (α - p) / 2 + (p - 1) with hedef
    have he : e < -1 := by rw [hedef]; linarith
    have hle : ∀ t ∈ Ioi R, ν {a | t < |a|} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal (C * t ^ e) := by
      intro t ht
      have htR : R < t := ht
      have ht0 : (0 : ℝ) < t := lt_trans hR0 htR
      have hupper : ν (Ioi t) = 0 :=
        measure_mono_null (Set.Ioi_subset_Ioi (le_trans hRM htR.le)) hM
      have hsub : {a : ℝ | t < |a|} ⊆ Iio (-t) ∪ Ioi t := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha
        rcases le_total a 0 with h | h
        · left
          have hta : t < -a := by rwa [abs_of_nonpos h] at ha
          show a < -t
          linarith
        · right
          have hta : t < a := by rwa [abs_of_nonneg h] at ha
          exact hta
      have hmeas : ν {a : ℝ | t < |a|} ≤ ν (Iio (-t)) := by
        refine le_trans (measure_mono hsub) ?_
        refine le_trans (measure_union_le _ _) ?_
        rw [hupper, add_zero]
      have htail : ν (Iio (-t)) = ENNReal.ofReal (LatticeProb.lowerTail ν t) := by
        rw [LatticeProb.lowerTail, ENNReal.ofReal_toReal (measure_ne_top ν _)]
      have hdomt : LatticeProb.lowerTail ν t ≤ C * t ^ (-α + (α - p) / 2) :=
        hdom t (le_trans hRr htR.le)
      have hstep : ν {a : ℝ | t < |a|} ≤ ENNReal.ofReal (C * t ^ (-α + (α - p) / 2)) := by
        rw [htail] at hmeas
        exact le_trans hmeas (ENNReal.ofReal_le_ofReal hdomt)
      calc ν {a : ℝ | t < |a|} * ENNReal.ofReal (t ^ (p - 1))
          ≤ ENNReal.ofReal (C * t ^ (-α + (α - p) / 2)) * ENNReal.ofReal (t ^ (p - 1)) :=
            mul_le_mul' hstep le_rfl
        _ = ENNReal.ofReal (C * t ^ (-α + (α - p) / 2) * t ^ (p - 1)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal (C * t ^ e) := by
            rw [hedef, mul_assoc, ← Real.rpow_add ht0]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hle) ?_
    have hint : IntegrableOn (fun t : ℝ => C * t ^ e) (Ioi R) :=
      (integrableOn_Ioi_rpow_of_lt he hR0).const_mul C
    have hfin := hint.2
    rw [hasFiniteIntegral_iff_enorm] at hfin
    exact lt_of_le_of_lt (lintegral_mono fun t => Real.ofReal_le_enorm _) hfin


/-- Markov's inequality for the lower tail at the exponent `p`: the second ingredient of
"Independence, Markov's inequality, and \eqref{eq:dgt4-green-tail} give ..."
(`sandpile.tex:5352`). -/
theorem lowerTail_le_moment_div (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 0 < p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) {s : ℝ} (hs : 0 < s) :
    LatticeProb.lowerTail ν s ≤ (∫ z, |z| ^ p ∂ν) / s ^ p := by
  have hnn : ∀ z : ℝ, 0 ≤ |z| ^ p := fun z => Real.rpow_nonneg (abs_nonneg z) p
  have h1 := mul_meas_ge_le_integral_of_nonneg (μ := ν) (f := fun z : ℝ => |z| ^ p)
    (Filter.Eventually.of_forall hnn) hmom (s ^ p)
  have hsub : Iio (-s) ⊆ {z : ℝ | s ^ p ≤ |z| ^ p} := by
    intro z hz
    have hz' : z < -s := hz
    have hzneg : z ≤ 0 := by linarith
    have hle : s ≤ |z| := by
      rw [abs_of_nonpos hzneg]
      linarith
    exact Real.rpow_le_rpow hs.le hle hp.le
  have h2 : LatticeProb.lowerTail ν s ≤ (ν {z : ℝ | s ^ p ≤ |z| ^ p}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hs p
  have h3 : 0 ≤ (ν {z : ℝ | s ^ p ≤ |z| ^ p}).toReal := ENNReal.toReal_nonneg
  rw [le_div_iff₀ hsp]
  simp only [measureReal_def] at h1
  nlinarith [h1, h2, h3]

/-- At least two of finitely many pairwise independent events occur with probability at most
the square of the sum of their probabilities.  This is the first half of "Independence,
Markov's inequality, and \eqref{eq:dgt4-green-tail} give
`\P(|A_n|\geq2)\leq\frac12(\sum_{z\ne0}\P(z\in A_n))^2`" (`sandpile.tex:5352-5354`), without
the factor `1/2`, which the constant of that display absorbs.  Measurability of the events is
not needed: the bound is subadditivity of the outer measure followed by the product formula
on each pair. -/
theorem measure_two_le_sq_of_pairwise_indep {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} {iota : Type*} [DecidableEq iota] (s : Finset iota)
    (A : iota → Set Omega)
    (hindep : ∀ i j, i ≠ j → P (A i ∩ A j) = P (A i) * P (A j)) :
    P {ω | 2 ≤ (s.filter fun i => ω ∈ A i).card} ≤ (∑ i ∈ s, P (A i)) ^ 2 := by
  have hsub : {ω | 2 ≤ (s.filter fun i => ω ∈ A i).card} ⊆
      ⋃ i ∈ s, ⋃ j ∈ s.erase i, A i ∩ A j := by
    intro ω hω
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hω
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    refine Set.mem_iUnion₂.mpr ⟨i, hi'.1, Set.mem_iUnion₂.mpr ⟨j, ?_, ⟨hi'.2, hj'.2⟩⟩⟩
    exact Finset.mem_erase.mpr ⟨hij.symm, hj'.1⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le s _) ?_
  have hinner : ∀ i ∈ s, P (⋃ j ∈ s.erase i, A i ∩ A j) ≤ P (A i) * ∑ j ∈ s, P (A j) := by
    intro i _
    refine le_trans (measure_biUnion_finset_le (s.erase i) _) ?_
    have hterm : ∀ j ∈ s.erase i, P (A i ∩ A j) = P (A i) * P (A j) := by
      intro j hj
      exact hindep i j (Finset.mem_erase.mp hj).1.symm
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul, sq]

/-- Markov's inequality for the lower tail of a SCALED scenery value, the form the sum over
sites in `sandpile.tex:5352` takes: `\P(-c\zeta(0)>s)=\P(-\zeta(0)>s/c)` is at most
`\E|\zeta(0)|^p (c/s)^p`. -/
theorem lowerTail_div_le_moment_mul (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp : 0 < p) (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) {c s : ℝ} (hc : 0 < c)
    (hs : 0 < s) :
    LatticeProb.lowerTail ν (s / c) ≤ (∫ z, |z| ^ p ∂ν) * (c / s) ^ p := by
  have hkey := lowerTail_le_moment_div ν hp hmom (s := s / c) (div_pos hs hc)
  refine hkey.trans (le_of_eq ?_)
  rw [Real.div_rpow hs.le hc.le, Real.div_rpow hc.le hs.le]
  have hsp : (0 : ℝ) < s ^ p := Real.rpow_pos_of_pos hs p
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  field_simp

/-- A power of the logarithm is negligible against any negative power. -/
theorem tendsto_log_rpow_mul_rpow_neg_atTop {q δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun x : ℝ => Real.log x ^ q * x ^ (-δ)) atTop (𝓝 0) := by
  have hlo : (fun x : ℝ => Real.log x ^ q) =o[atTop] fun x : ℝ => x ^ δ :=
    _root_.isLittleO_log_rpow_rpow_atTop q hδ
  have hdiv := hlo.tendsto_div_nhds_zero
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- Potter's bound from below at a fixed base point: an antitone positive regularly varying
function of index `-α` dominates a multiple of `s ^ (-α - δ)` beyond a level. -/
theorem exists_rpow_le_of_regularlyVarying {F : ℝ → ℝ} {α : ℝ}
    (hF : LatticeProb.RegularlyVaryingAtTop F (-α)) (hmono : Antitone F)
    (hpos : ∀ r : ℝ, 0 < F r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ 0 < C ∧ ∀ s : ℝ, r₀ ≤ s → C * s ^ (-α - δ) ≤ F s := by
  obtain ⟨r₀, hr₀, h⟩ :=
    LatticeProb.potter_lower hF hmono (Filter.Eventually.of_forall hpos) hδ
  refine ⟨F r₀ / ((1 + δ) * r₀ ^ (-α - δ)), r₀, hr₀, ?_, fun s hs => ?_⟩
  · have h1 : (0 : ℝ) < r₀ ^ (-α - δ) := Real.rpow_pos_of_pos hr₀ _
    have h2 : (0 : ℝ) < (1 + δ) := by linarith
    have h3 := hpos r₀
    positivity
  · have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hr₀ hs
    have hkey := h s r₀ le_rfl hs
    rw [div_le_iff₀ (hpos s)] at hkey
    have hsplit : (r₀ / s) ^ (-α - δ) = r₀ ^ (-α - δ) * s ^ (α + δ) := by
      rw [Real.div_rpow hr₀.le hs0.le, show -α - δ = -(α + δ) by ring,
        Real.rpow_neg hs0.le, Real.rpow_neg hr₀.le]
      field_simp
    rw [hsplit] at hkey
    have hpow : (0 : ℝ) < s ^ (α + δ) := Real.rpow_pos_of_pos hs0 _
    have hcancel : s ^ (-α - δ) * s ^ (α + δ) = 1 := by
      rw [← Real.rpow_add hs0]; norm_num
    have hr0p : (0 : ℝ) < r₀ ^ (-α - δ) := Real.rpow_pos_of_pos hr₀ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < (1 + δ) * r₀ ^ (-α - δ))]
    have hmul := mul_le_mul_of_nonneg_right hkey (Real.rpow_pos_of_pos hs0 (-α - δ)).le
    have heq : (1 + δ) * (r₀ ^ (-α - δ) * s ^ (α + δ)) * F s * s ^ (-α - δ)
        = F s * ((1 + δ) * r₀ ^ (-α - δ)) * (s ^ (-α - δ) * s ^ (α + δ)) := by ring
    rw [heq, hcancel, mul_one] at hmul
    linarith


/-- The comparison behind `\P(|A_n|\geq2)=o(\P(-\zeta(0)>\E Pw_n(0)))`
(`sandpile.tex:5353-5354`): at the level `\eta_n\E Pw_n(0)` with
`\eta_n=1/(K\log\E Pw_n(0))`, the square of the Markov bound at exponent `p` is negligible
against the lower tail whenever `\alpha<2p`.  The logarithm costs nothing because it is
beaten by any power. -/
theorem tendsto_level_pow_div_lowerTail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α p K A : ℝ} (hpα : α < 2 * p) (hK : 0 < K)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ =>
        (A / (a n / (K * Real.log (a n))) ^ p) ^ 2 / LatticeProb.lowerTail ν (a n))
      atTop (𝓝 0) := by
  set δ : ℝ := (2 * p - α) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    LatticeProb.pos_of_antitone_of_eventually_pos (LatticeProb.antitone_lowerTail ν)
      (LatticeProb.eventually_pos_of_regularlyVarying hrv (LatticeProb.lowerTail_nonneg ν))
  obtain ⟨C, r₀, hr₀, hC, hdom⟩ :=
    exists_rpow_le_of_regularlyVarying hrv (LatticeProb.antitone_lowerTail ν) hTpos hδ
  have h2 : ∀ y : ℝ, 0 ≤ y → (y ^ p) ^ (2 : ℕ) = y ^ (2 * p) := by
    intro y hy
    rw [← Real.rpow_natCast (y ^ p) 2, ← Real.rpow_mul hy]
    norm_num [mul_comm]
  have hg : Tendsto (fun n : ℕ =>
      A ^ 2 * K ^ (2 * p) / C * (Real.log (a n) ^ (2 * p) * a n ^ (-δ))) atTop (𝓝 0) := by
    have h0 := (tendsto_log_rpow_mul_rpow_neg_atTop (q := 2 * p) hδ).comp ha
    have h1 := h0.const_mul (A ^ 2 * K ^ (2 * p) / C)
    simpa [Function.comp_def] using h1
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [ha.eventually_ge_atTop 1] with n hn
    have := hTpos (a n)
    positivity
  · filter_upwards [ha.eventually_ge_atTop r₀, ha.eventually_ge_atTop (Real.exp 1)] with n h1 h2'
    have hx0 : (0 : ℝ) < a n := lt_of_lt_of_le (Real.exp_pos 1) h2'
    have hL : (1 : ℝ) ≤ Real.log (a n) := by
      have h := Real.log_le_log (Real.exp_pos 1) h2'
      rwa [Real.log_exp] at h
    have hL0 : (0 : ℝ) < Real.log (a n) := lt_of_lt_of_le one_pos hL
    have hKL : (0 : ℝ) < K * Real.log (a n) := by positivity
    have hpow : (a n / (K * Real.log (a n))) ^ p
        = a n ^ p / (K * Real.log (a n)) ^ p := Real.div_rpow hx0.le hKL.le p
    have hsq : (A / (a n / (K * Real.log (a n))) ^ p) ^ 2
        = A ^ 2 * (K ^ (2 * p) * Real.log (a n) ^ (2 * p)) / a n ^ (2 * p) := by
      rw [hpow, div_div_eq_mul_div, div_pow, mul_pow, h2 _ hKL.le, h2 _ hx0.le,
        Real.mul_rpow hK.le hL0.le]
    have hT : C * a n ^ (-α - δ) ≤ LatticeProb.lowerTail ν (a n) := hdom (a n) h1
    have hDpos : (0 : ℝ) < C * a n ^ (-α - δ) := by
      have := Real.rpow_pos_of_pos hx0 (-α - δ)
      positivity
    have hprod : a n ^ (2 * p) * a n ^ (-α - δ) = a n ^ δ := by
      rw [← Real.rpow_add hx0]
      congr 1
      rw [hδdef]; ring
    have hNnn : (0 : ℝ) ≤ A ^ 2 * (K ^ (2 * p) * Real.log (a n) ^ (2 * p)) / a n ^ (2 * p) := by
      have h3 : (0 : ℝ) < a n ^ (2 * p) := Real.rpow_pos_of_pos hx0 _
      have h4 : (0 : ℝ) < K ^ (2 * p) := Real.rpow_pos_of_pos hK _
      have h5 : (0 : ℝ) < Real.log (a n) ^ (2 * p) := Real.rpow_pos_of_pos hL0 _
      positivity
    rw [hsq]
    have hstep : A ^ 2 * (K ^ (2 * p) * Real.log (a n) ^ (2 * p)) / a n ^ (2 * p) /
        LatticeProb.lowerTail ν (a n)
        ≤ A ^ 2 * (K ^ (2 * p) * Real.log (a n) ^ (2 * p)) / a n ^ (2 * p) /
          (C * a n ^ (-α - δ)) := by
      gcongr
    refine hstep.trans (le_of_eq ?_)
    have hxδ : (0 : ℝ) < a n ^ δ := Real.rpow_pos_of_pos hx0 δ
    have hxp : (0 : ℝ) < a n ^ (2 * p) := Real.rpow_pos_of_pos hx0 _
    have hxm : (0 : ℝ) < a n ^ (-α - δ) := Real.rpow_pos_of_pos hx0 _
    have hneg : a n ^ (-δ) = (a n ^ δ)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
    rw [div_div, hneg]
    rw [show a n ^ (2 * p) * (C * a n ^ (-α - δ)) = C * a n ^ δ by
      rw [← hprod]; ring]
    field_simp

/-- The choice of `K` in `sandpile.tex:5374-5376`: a power of the level below the index of
regular variation is negligible against the lower tail.  The paper asks for `cK>\alpha+1`;
what the comparison needs is only `\alpha<\beta`. -/
theorem tendsto_rpow_neg_div_lowerTail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α β : ℝ} (hβ : α < β)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n : ℕ => a n ^ (-β) / LatticeProb.lowerTail ν (a n)) atTop (𝓝 0) := by
  set δ : ℝ := (β - α) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    LatticeProb.pos_of_antitone_of_eventually_pos (LatticeProb.antitone_lowerTail ν)
      (LatticeProb.eventually_pos_of_regularlyVarying hrv (LatticeProb.lowerTail_nonneg ν))
  obtain ⟨C, r₀, hr₀, hC, hdom⟩ :=
    exists_rpow_le_of_regularlyVarying hrv (LatticeProb.antitone_lowerTail ν) hTpos hδ
  have hg : Tendsto (fun n : ℕ => C⁻¹ * a n ^ (-δ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (-δ)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hδ
    have h1 := (h0.comp ha).const_mul C⁻¹
    simpa [Function.comp_def] using h1
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [ha.eventually_gt_atTop 0] with n hn
    have h2 := hTpos (a n)
    have h3 : (0 : ℝ) < a n ^ (-β) := Real.rpow_pos_of_pos hn _
    positivity
  · filter_upwards [ha.eventually_ge_atTop r₀, ha.eventually_gt_atTop 0] with n h1 h2
    have hT : C * a n ^ (-α - δ) ≤ LatticeProb.lowerTail ν (a n) := hdom (a n) h1
    have hmp : (0 : ℝ) < a n ^ (-α - δ) := Real.rpow_pos_of_pos h2 _
    have hstep : a n ^ (-β) / LatticeProb.lowerTail ν (a n)
        ≤ a n ^ (-β) / (C * a n ^ (-α - δ)) := by
      gcongr
    refine hstep.trans (le_of_eq ?_)
    have hsplit : a n ^ (-β) / a n ^ (-α - δ) = a n ^ (-δ) := by
      rw [← Real.rpow_sub h2]
      congr 1
      rw [hδdef]; ring
    rw [eq_comm, ← hsplit]
    field_simp

/-- The splitting of `sandpile.tex:5376` according to the value of `A_n`: if, for every set
`B` of at most one site, the event `G` has conditional probability at most `\varepsilon` given
`\{A_n=B\}`, then `G` has probability at most `\varepsilon` on `\{|A_n|\leq1\}`.  The sets
`\{A_n=B\}` are disjoint and their union has probability at most one. -/
theorem measure_inter_card_le_one_le {Omega iota : Type*} [MeasurableSpace Omega]
    [DecidableEq iota] (P : Measure Omega) [IsProbabilityMeasure P]
    (s : Finset iota) (Q : iota → Omega → Prop)
    (hQ : ∀ i, MeasurableSet {ω | Q i ω}) (G : Set Omega) (ε : ℝ≥0∞)
    (h : ∀ B : Finset iota, B.card ≤ 1 →
      P (G ∩ {ω | s.filter (fun i => Q i ω) = B}) ≤ ε * P {ω | s.filter (fun i => Q i ω) = B}) :
    P (G ∩ {ω | (s.filter fun i => Q i ω).card ≤ 1}) ≤ ε := by
  classical
  set T : Finset (Finset iota) := s.powerset.filter (fun B => B.card ≤ 1) with hT
  have hTsub : ∀ B ∈ T, B ⊆ s := by
    intro B hB
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hmeasEq : ∀ B : Finset iota, B ⊆ s →
      MeasurableSet {ω | s.filter (fun i => Q i ω) = B} := by
    intro B hBs
    have hchar : {ω | s.filter (fun i => Q i ω) = B}
        = ⋂ i ∈ (s : Set iota), (if i ∈ B then {ω | Q i ω} else {ω | Q i ω}ᶜ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter₂, Finset.mem_coe]
      constructor
      · intro hω i hi
        by_cases hiB : i ∈ B
        · rw [if_pos hiB]
          have hmem : i ∈ s.filter (fun j => Q j ω) := by rw [hω]; exact hiB
          exact (Finset.mem_filter.mp hmem).2
        · rw [if_neg hiB]
          intro hQi
          exact hiB (by rw [← hω]; exact Finset.mem_filter.mpr ⟨hi, hQi⟩)
      · intro hω
        ext i
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨hi, hQi⟩
          by_contra hiB
          have hc := hω i hi
          rw [if_neg hiB] at hc
          exact hc hQi
        · intro hiB
          have hi := hBs hiB
          have hc := hω i hi
          rw [if_pos hiB] at hc
          exact ⟨hi, hc⟩
    rw [hchar]
    refine MeasurableSet.biInter s.countable_toSet fun i _ => ?_
    by_cases hiB : i ∈ B
    · rw [if_pos hiB]; exact hQ i
    · rw [if_neg hiB]; exact (hQ i).compl
  have hsub : G ∩ {ω | (s.filter fun i => Q i ω).card ≤ 1}
      ⊆ ⋃ B ∈ T, (G ∩ {ω | s.filter (fun i => Q i ω) = B}) := by
    intro ω hω
    refine Set.mem_iUnion₂.mpr ⟨s.filter fun i => Q i ω, ?_, ⟨hω.1, rfl⟩⟩
    rw [hT, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hω.2⟩
  have hdisj : (T : Set (Finset iota)).PairwiseDisjoint
      (fun B => {ω | s.filter (fun i => Q i ω) = B}) := by
    intro B hB B' hB' hne
    simp only [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    exact hne (by rw [← hω, ← hω'])
  calc P (G ∩ {ω | (s.filter fun i => Q i ω).card ≤ 1})
      ≤ P (⋃ B ∈ T, (G ∩ {ω | s.filter (fun i => Q i ω) = B})) := measure_mono hsub
    _ ≤ ∑ B ∈ T, P (G ∩ {ω | s.filter (fun i => Q i ω) = B}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ B ∈ T, ε * P {ω | s.filter (fun i => Q i ω) = B} :=
        Finset.sum_le_sum fun B hB => h B (Finset.mem_filter.mp hB).2
    _ = ε * ∑ B ∈ T, P {ω | s.filter (fun i => Q i ω) = B} := by rw [Finset.mul_sum]
    _ = ε * P (⋃ B ∈ T, {ω | s.filter (fun i => Q i ω) = B}) := by
        rw [measure_biUnion_finset hdisj fun B hB => hmeasEq B (hTsub B hB)]
    _ ≤ ε * 1 := by gcongr; exact prob_le_one
    _ = ε := mul_one ε



/-- The same splitting with a separate bound for each value of `A_n`, which is the form the
truncation uses: the empty value and each single site contribute separately. -/
theorem measure_inter_card_le_one_le_add {Omega iota : Type*} [MeasurableSpace Omega]
    [DecidableEq iota] (P : Measure Omega) (s : Finset iota) (Q : iota → Omega → Prop)
    (G : Set Omega) (ε₀ : ℝ≥0∞) (ε : iota → ℝ≥0∞)
    (h0 : P (G ∩ {ω | s.filter (fun i => Q i ω) = ∅}) ≤ ε₀)
    (h1 : ∀ i ∈ s, P (G ∩ {ω | s.filter (fun i' => Q i' ω) = {i}}) ≤ ε i) :
    P (G ∩ {ω | (s.filter fun i => Q i ω).card ≤ 1}) ≤ ε₀ + ∑ i ∈ s, ε i := by
  classical
  have hsub : G ∩ {ω | (s.filter fun i => Q i ω).card ≤ 1}
      ⊆ (G ∩ {ω | s.filter (fun i => Q i ω) = ∅}) ∪
        ⋃ i ∈ s, (G ∩ {ω | s.filter (fun i' => Q i' ω) = {i}}) := by
    intro ω hω
    rcases Nat.eq_zero_or_pos (s.filter fun i => Q i ω).card with hc | hc
    · exact Or.inl ⟨hω.1, Finset.card_eq_zero.mp hc⟩
    · have hc1 : (s.filter fun i => Q i ω).card = 1 := le_antisymm hω.2 hc
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc1
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨i, ?_, ⟨hω.1, hi⟩⟩)
      have : i ∈ s.filter fun j => Q j ω := by rw [hi]; exact Finset.mem_singleton_self i
      exact (Finset.mem_filter.mp this).1
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_union_le _ _) ?_
  exact add_le_add h0 (le_trans (measure_biUnion_finset_le s _) (Finset.sum_le_sum h1))

end Sandpile
