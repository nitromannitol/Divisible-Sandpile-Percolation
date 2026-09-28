import Sandpile.Support.Dgt4OriginProb

/-!
# Step 1 of case (b): the single residual of the heavy-tailed branch

`SmallOriginNeighborAverage` records `eq:dgt4-small-origin-neighbor-average`, that the
neighbour average of the odometer killed at the origin falls below a sixth of its own mean with
probability negligible against the lower tail at that mean, with the neighbour average compared
against its OWN mean rather than a deterministic level. The rest of case (b) consumes the same
estimate at the deterministic level `𝔼 u_n(0)/G(0,0)`; the two forms are interchangeable because
the neighbour-average mean is asymptotic to that deterministic level and the lower tail is
regularly varying, so its values at two asymptotic levels have ratio tending to one
(`tendsto_ratio_one_of_near`, the deterministic form of the monotone squeeze of
`Support/Dgt4CaseBReplace.lean`). The file also collects the summability of the Green-ratio
weights and pairwise independence facts that Step 1's counting argument uses.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- A regularly varying antitone function has ratio tending to one at two asymptotic
levels.  Only the DEFINITION of regular variation at the two fixed ratios `1±η` is used,
together with monotonicity; Potter's bounds are not needed. -/
theorem tendsto_ratio_one_of_near {F : ℝ → ℝ} {ρ : ℝ}
    (hFrv : LatticeProb.RegularlyVaryingAtTop F ρ) (hFanti : Antitone F)
    (hFpos : ∀ r : ℝ, 0 < F r) {a b : ℕ → ℝ}
    (hapos : ∀ᶠ n in atTop, 0 < a n) (ha : Tendsto a atTop atTop)
    (hb : Tendsto (fun n : ℕ => b n / a n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => F (b n) / F (a n)) atTop (𝓝 1) := by
  have habs : Tendsto (fun n : ℕ => |F (b n) / F (a n) - 1|) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun c hc => Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le hc (abs_nonneg _), fun c hc => ?_⟩
    obtain ⟨η, hη0, hη1, hηc⟩ := exists_eta_rpow_close (ρ := ρ) (half_pos hc)
    have h1 : Tendsto (fun n : ℕ => F ((1 - η) * a n) / F (a n)) atTop (𝓝 ((1 - η) ^ ρ)) := by
      simpa [Function.comp_def] using (hFrv (1 - η) (by linarith)).comp ha
    have h2 : Tendsto (fun n : ℕ => F ((1 + η) * a n) / F (a n)) atTop (𝓝 ((1 + η) ^ ρ)) := by
      simpa [Function.comp_def] using (hFrv (1 + η) (by linarith)).comp ha
    have hE : Tendsto (fun n : ℕ =>
        |F ((1 - η) * a n) / F (a n) - 1| + |F ((1 + η) * a n) / F (a n) - 1|) atTop
        (𝓝 (|(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1|)) :=
      ((h1.sub_const 1).abs).add ((h2.sub_const 1).abs)
    have hlt : |(1 - η) ^ ρ - 1| + |(1 + η) ^ ρ - 1| < c := lt_trans hηc (half_lt_self hc)
    have hnear : ∀ᶠ n : ℕ in atTop, |b n / a n - 1| ≤ η := by
      have := hb.eventually (Metric.closedBall_mem_nhds (1 : ℝ) hη0)
      filter_upwards [this] with n hn
      rwa [Real.dist_eq] at hn
    filter_upwards [hE.eventually (gt_mem_nhds hlt), hnear, hapos] with n hn hnr han
    exact lt_of_le_of_lt (abs_ratio_sub_one_le_of_near hFanti hFpos han hnr) hn
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add
    (tendsto_zero_iff_abs_tendsto_zero _ |>.mpr habs)
  simpa using this

/-- `\E Pw_n(0)\to\infty` (`sandpile.tex:5348`), from `eq:dgt4-origin-fixed-mean` and the
divergence of `\E u_n(0)` of Part (i) of `cor:dgt4-mean-lower`. -/
theorem tendsto_meanAvg_originOdometer_atTop
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    Tendsto (fun n : ℕ => ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0
      ∂(LatticeProb.iidLaw d ν)) atTop atTop := by
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hintν : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hintν hmean
      (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have hratio := tendsto_meanAvg_originOdometer_ratio hGreenHigh d hd ν hatom hmean hvar hvar'
  have hhalf : ∀ᶠ n : ℕ in atTop,
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 / 2 ≤
        ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν) := by
    filter_upwards [hratio.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
      hinf.eventually_gt_atTop 0] with n hn han
    rw [lt_div_iff₀ han] at hn
    linarith
  exact tendsto_atTop_mono' atTop hhalf (hinf.atTop_div_const two_pos)

/-- `eq:dgt4-small-origin-neighbor-average` (`sandpile.tex:5344-5346`): the neighbour
average of the odometer killed at the origin falls below a sixth of its own mean with
probability negligible against the lower tail at that mean. -/
def SmallOriginNeighborAverage (d : ℕ) (ν : Measure ℝ) : Prop :=
  Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
      {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤
        (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0
          ∂(LatticeProb.iidLaw d ν)) / 6}).toReal /
      LatticeProb.lowerTail ν
        (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)))
    atTop (𝓝 0)

/-- Case (b) of `prop:dgt4-contact-asymptotics` from Step 1, in the paper's own form.
`eq:dgt4-small-origin-neighbor-average` is the ONLY remaining input of the heavy-tailed
branch: everything else in `sandpile.tex:5301-5412` is proved.  The passage between the
paper's centring `\E Pw_n(0)` and the deterministic level `\E u_n(0)/G(0,0)` uses only
`eq:dgt4-origin-fixed-mean` and the regular variation of the lower tail. -/
theorem caseThresholdField_linear_of_smallOriginNeighborAverage
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    (hsmall : SmallOriginNeighborAverage d ν) :
    CaseThresholdField d ν (1 - 1 / α) := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hintν : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hintν hmean
      (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have hratio := tendsto_meanAvg_originOdometer_ratio hGreenHigh d hd ν hatom hmean hvar hvar'
  have hTanti : Antitone (LatticeProb.lowerTail ν) := LatticeProb.antitone_lowerTail ν
  have hTpos : ∀ r : ℝ, 0 < LatticeProb.lowerTail ν r :=
    lowerTail_pos_of_regularlyVarying ν hrv
  have hTratio : Tendsto (fun n : ℕ =>
      LatticeProb.lowerTail ν
          (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) /
        LatticeProb.lowerTail ν
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0))
      atTop (𝓝 1) :=
    tendsto_ratio_one_of_near (F := LatticeProb.lowerTail ν) (ρ := -α) hrv hTanti hTpos
      (hinf.eventually_gt_atTop 0) hinf hratio
  refine caseThresholdField_linear_of_step1_only hGreenHigh d hd ν hatom hmean hvar hvar' hα hrv
    (θ := 1 / 12) (by norm_num) (by norm_num) ?_
  have hprod : Tendsto (fun n : ℕ =>
      (((LatticeProb.iidLaw d ν)
          {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤
            (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0
              ∂(LatticeProb.iidLaw d ν)) / 6}).toReal /
        LatticeProb.lowerTail ν
          (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν))) *
      (LatticeProb.lowerTail ν
          (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) /
        LatticeProb.lowerTail ν
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)))
      atTop (𝓝 0) := by
    have := hsmall.mul hTratio
    rwa [zero_mul] at this
  have hhalf : ∀ᶠ n : ℕ in atTop,
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0 / 2 ≤
        ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν) := by
    filter_upwards [hratio.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
      hinf.eventually_gt_atTop 0] with n hn han
    rw [lt_div_iff₀ han] at hn
    linarith
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ?_) ?_ hprod
  · exact div_nonneg ENNReal.toReal_nonneg (hTpos _).le
  · filter_upwards [hhalf, hinf.eventually_gt_atTop 0] with n hn han
    have hTb := hTpos (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0
      ∂(LatticeProb.iidLaw d ν))
    have hTa := hTpos (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
      Sandpile.green d 0 0)
    have hrw : ∀ x : ℝ, x / LatticeProb.lowerTail ν
          (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) *
        (LatticeProb.lowerTail ν
            (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) /
          LatticeProb.lowerTail ν (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)) =
        x / LatticeProb.lowerTail ν (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0) := by
      intro x
      field_simp
    rw [hrw]
    refine div_le_div_of_nonneg_right ?_ hTa.le
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ζ hζ => ?_)
    have hζ' : Sandpile.avg (Sandpile.originOdometer ζ n) 0 <
      1 / 12 * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
        Sandpile.green d 0 0) := hζ
    show Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤
      (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) / 6
    linarith

/-- The influence of a site on the neighbour average is at most one: it is the probability
that a walk from that site hits the origin. -/
theorem originInfluence_le_one (hd : 1 ≤ d) (z : Sandpile.Site d) :
    Sandpile.originInfluence z ≤ 1 :=
  Sandpile.originInfluence_le_sup zero_le_one
    (fun w _ => LatticeProb.srwHitProb_le_one (by omega) w) z

/-- `eq:dgt4-green-tail` at the exponents Step 1 uses: `\sum_{z\ne0}(G(0,z)/G(0,0))^p` is
finite for every `p\geq2` in `d\geq5`.  The square case is the concentration estimate
already in the repository; the rest is that the influences lie in `[0,1]`, so a larger
exponent only decreases them. -/
theorem summable_originInfluence_rpow (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {p : ℝ} (hp : 2 ≤ p) :
    Summable fun z : Sandpile.Site d => Sandpile.originInfluence z ^ p := by
  refine Summable.of_nonneg_of_le
    (fun z => Real.rpow_nonneg (Sandpile.originInfluence_nonneg z) p) (fun z => ?_)
    (Sandpile.summable_originInfluence_sq hGH hd)
  rcases eq_or_lt_of_le (Sandpile.originInfluence_nonneg z) with h | h
  · rw [← h, Real.zero_rpow (by linarith)]
    positivity
  · have h1 : Sandpile.originInfluence z ≤ 1 := originInfluence_le_one (by omega) z
    have h2 : Sandpile.originInfluence z ^ p ≤ Sandpile.originInfluence z ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h h1 hp
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h2

/-- Two distinct coordinates of the i.i.d. field are independent: the "Independence" of
`sandpile.tex:5352`, in the pairwise form that the bound on `\P(|A_n|\geq2)` consumes.  The
proof is the measure-preserving projection of the field onto the two sites, where the law is
a product. -/
theorem iidLaw_two_site (ν : Measure ℝ) [IsProbabilityMeasure ν] {z₁ z₂ : Sandpile.Site d}
    (hz : z₁ ≠ z₂) {B₁ B₂ : Set ℝ} (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    (LatticeProb.iidLaw d ν) {ζ | ζ z₁ ∈ B₁ ∧ ζ z₂ ∈ B₂} = ν B₁ * ν B₂ := by
  have he : Function.Injective (![z₁, z₂] : Fin 2 → Sandpile.Site d) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hmp := LatticeProb.measurePreserving_pick _ ν (![z₁, z₂] : Fin 2 → Sandpile.Site d) he
  have hB : ∀ i : Fin 2, MeasurableSet ((![B₁, B₂] : Fin 2 → Set ℝ) i) := by
    intro i
    fin_cases i
    · simpa using h₁
    · simpa using h₂
  have hset : {ζ : Sandpile.Site d → ℝ | ζ z₁ ∈ B₁ ∧ ζ z₂ ∈ B₂}
      = (fun ζ : Sandpile.Site d → ℝ => fun i => ζ ((![z₁, z₂] : Fin 2 → Sandpile.Site d) i)) ⁻¹'
        (Set.pi Set.univ (![B₁, B₂] : Fin 2 → Set ℝ)) := by
    ext ζ
    constructor
    · rintro ⟨ha, hb⟩ i -
      fin_cases i
      · simpa using ha
      · simpa using hb
    · intro h
      exact ⟨by simpa using h 0 (Set.mem_univ _), by simpa using h 1 (Set.mem_univ _)⟩
  rw [hset, ← Measure.map_apply hmp.measurable (MeasurableSet.univ_pi hB), hmp.map_eq,
    Measure.pi_pi]
  simp [Fin.prod_univ_two]

/-- `G(0,z)/G(0,0)` is the probability that the walk from `z` hits the origin, so it lies in
`[0,1]` for every site, the origin included. -/
theorem greenRatio_eq_hitProb (hd : 3 ≤ d) (z : Sandpile.Site d) :
    Sandpile.green d 0 z / Sandpile.green d 0 0 = LatticeProb.srwHitProb d z := by
  rw [Sandpile.green_origin_eq_srwGreenInf, Sandpile.green_origin_eq_srwGreenInf,
    LatticeProb.srwHitProb_eq_green_ratio hd]

/-- `eq:dgt4-green-tail` at the exponents Step 1 uses, in the weights of `A_n` themselves:
`\sum_z (G(0,z)/G(0,0))^p` is finite for every `p\geq2` in `d\geq5`. -/
theorem summable_greenRatio_rpow (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {p : ℝ} (hp : 2 ≤ p) :
    Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p := by
  have hnn : ∀ z : Sandpile.Site d, 0 ≤ Sandpile.green d 0 z / Sandpile.green d 0 0 := by
    intro z
    rw [greenRatio_eq_hitProb (by omega) z]
    exact LatticeProb.srwHitProb_nonneg z
  have hle1 : ∀ z : Sandpile.Site d, Sandpile.green d 0 z / Sandpile.green d 0 0 ≤ 1 := by
    intro z
    rw [greenRatio_eq_hitProb (by omega) z]
    exact LatticeProb.srwHitProb_le_one (by omega) z
  have hsq : Summable fun z : Sandpile.Site d =>
      (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ 2 := by
    have hg := ((hGH d hd).2.1).div_const (Sandpile.green d 0 0 ^ 2)
    simpa only [div_pow] using hg
  refine Summable.of_nonneg_of_le (fun z => Real.rpow_nonneg (hnn z) p) (fun z => ?_) hsq
  rcases eq_or_lt_of_le (hnn z) with h | h
  · rw [← h, Real.zero_rpow (by linarith)]
    positivity
  · have h2 : (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ p ≤
        (Sandpile.green d 0 z / Sandpile.green d 0 0) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h (hle1 z) hp
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h2

end Sandpile
