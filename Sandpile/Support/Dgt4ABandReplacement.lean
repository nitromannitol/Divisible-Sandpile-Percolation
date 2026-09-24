/-
The scenery side of the increment replacement and the contact error of Step 2 of
`thm:dgt4-many-limits` (`eq:dgt4-band-increment-replacement` and
`eq:dgt4-band-contact-error`, `sandpile.tex:6171-6195`).

Both estimates compare the threshold at the random level `W_n = Pw_n(0)` with the
threshold at the deterministic level `b_n = E u_n(0)/G(0,0)`.  Conditionally on
`W_n`, which is independent of `ζ(0)`, each comparison is between two
DETERMINISTIC levels, and that is what is proved here:

* the mean overshoot is `1`-Lipschitz in the level and does not move at all
  below the lower of the two levels (`abs_integral_posPart_sub_le`), which is the
  paper's sentence "the `1`-Lipschitz dependence of `(ξ-w)_+` on `w`";
* the two threshold events differ by a set whose mass the band density bound
  `eq:dgt4-band-density` controls, once both levels are above `ℓ_1 a_k`
  (`measure_symmDiff_threshold_le`);
* the mass above `ℓ_1 a_k` is `(1+η)ω_k` by the band profile at `r = 1`
  (`measure_gt_band_bottom_le`), which is where the factor `ω_k` in the second
  term of `eq:dgt4-band-increment-replacement` comes from.

The levels below `ℓ_1 a_k`, where these bounds do not apply, are the ones the
origin-fixed lower tail `eq:dgt4-band-origin-fixed-lower-tail` excludes.
-/
import Sandpile.Support.Dgt4ABandLaw
import Sandpile.Support.Dgt4ABandWeights

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

/-- The threshold event at the level `c` is the lower tail of the law. -/
theorem thresholdSet_eq_Iio (c : ℝ) : {z : ℝ | -(z) > c} = Iio (-c) := by
  ext z
  simp only [mem_setOf_eq, mem_Iio, gt_iff_lt]
  constructor <;> intro h <;> linarith

theorem measurableSet_thresholdSet (c : ℝ) : MeasurableSet {z : ℝ | -(z) > c} := by
  rw [thresholdSet_eq_Iio]
  exact measurableSet_Iio

/-- The symmetric difference of two threshold events is the band between the two
levels. -/
theorem symmDiff_thresholdSet (s t : ℝ) :
    symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t}
      = {z : ℝ | min s t < -(z) ∧ -(z) ≤ max s t} := by
  ext z
  simp only [Set.mem_symmDiff, mem_setOf_eq, gt_iff_lt, not_lt]
  rcases le_total s t with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact absurd h1 (not_lt.mpr (by linarith))
    · rintro ⟨h1, h2⟩
      exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_right h, max_eq_left h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h1 (not_lt.mpr (by linarith))
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, h2⟩

/-- The mean overshoot above a level is `1`-Lipschitz in the level. -/
theorem abs_posPart_sub_le (z s t : ℝ) :
    |max (-z - s) 0 - max (-z - t) 0| ≤ |s - t| := by
  have h0 : s - t ≤ |s - t| := le_abs_self _
  have h1 : t - s ≤ |s - t| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  have hA : max (-z - s) 0 ≤ max (-z - t) 0 + |s - t| := by
    refine max_le ?_ ?_
    · have h2 : -z - t ≤ max (-z - t) 0 := le_max_left _ _
      linarith
    · have h2 : (0 : ℝ) ≤ max (-z - t) 0 := le_max_right _ _
      have h3 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
      linarith
  have hB : max (-z - t) 0 ≤ max (-z - s) 0 + |s - t| := by
    refine max_le ?_ ?_
    · have h2 : -z - s ≤ max (-z - s) 0 := le_max_left _ _
      linarith
    · have h2 : (0 : ℝ) ≤ max (-z - s) 0 := le_max_right _ _
      have h3 : (0 : ℝ) ≤ |s - t| := abs_nonneg _
      linarith
  rw [abs_le]
  constructor <;> linarith

/-- Below both levels the mean overshoot does not move at all. -/
theorem posPart_sub_eq_zero {z s t : ℝ} (hz : -z ≤ min s t) :
    max (-z - s) 0 - max (-z - t) 0 = 0 := by
  have h1 : max (-z - s) 0 = 0 := max_eq_right (by have := min_le_left s t; linarith)
  have h2 : max (-z - t) 0 = 0 := max_eq_right (by have := min_le_right s t; linarith)
  rw [h1, h2, sub_zero]

/-- **The mean overshoot is `1`-Lipschitz in the level and moves only above the
lower of the two levels.** -/
theorem abs_integral_posPart_sub_le (ν : Measure ℝ) [IsFiniteMeasure ν] {s t : ℝ}
    (hs : Integrable (fun z : ℝ => max (-z - s) 0) ν)
    (ht : Integrable (fun z : ℝ => max (-z - t) 0) ν) :
    |(∫ z, max (-z - s) 0 ∂ν) - ∫ z, max (-z - t) 0 ∂ν|
      ≤ |s - t| * (ν {z : ℝ | -(z) > min s t}).toReal := by
  have hmeas : MeasurableSet {z : ℝ | -(z) > min s t} := measurableSet_thresholdSet _
  have hptw : ∀ z : ℝ, ‖max (-z - s) 0 - max (-z - t) 0‖
      ≤ |s - t| * Set.indicator {z : ℝ | -(z) > min s t} (fun _ => (1 : ℝ)) z := by
    intro z
    rw [Real.norm_eq_abs]
    by_cases hz : z ∈ {z : ℝ | -(z) > min s t}
    · rw [Set.indicator_of_mem hz, mul_one]
      exact abs_posPart_sub_le z s t
    · have hle : -z ≤ min s t := not_lt.mp hz
      rw [posPart_sub_eq_zero hle, abs_zero]
      exact mul_nonneg (abs_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) z)
  have hdom : Integrable
      (fun z : ℝ => |s - t| * Set.indicator {z : ℝ | -(z) > min s t} (fun _ => (1 : ℝ)) z) ν :=
    ((integrable_const (1 : ℝ)).indicator hmeas).const_mul _
  have hmono : ∫ z, ‖max (-z - s) 0 - max (-z - t) 0‖ ∂ν
      ≤ ∫ z, |s - t| * Set.indicator {z : ℝ | -(z) > min s t} (fun _ => (1 : ℝ)) z ∂ν :=
    integral_mono (hs.sub ht).norm hdom hptw
  have hval : ∫ z, |s - t| * Set.indicator {z : ℝ | -(z) > min s t} (fun _ => (1 : ℝ)) z ∂ν
      = |s - t| * (ν {z : ℝ | -(z) > min s t}).toReal := by
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one,
      measureReal_def]
  rw [← integral_sub hs ht, ← Real.norm_eq_abs]
  calc ‖∫ z, (max (-z - s) 0 - max (-z - t) 0) ∂ν‖
      ≤ ∫ z, ‖max (-z - s) 0 - max (-z - t) 0‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z, |s - t| * Set.indicator {z : ℝ | -(z) > min s t} (fun _ => (1 : ℝ)) z ∂ν := hmono
    _ = |s - t| * (ν {z : ℝ | -(z) > min s t}).toReal := hval

/-- **The two threshold events differ by little when both levels lie in the
band.**  The band density bound `eq:dgt4-band-density` controls the part of the
difference inside the band, and the mass above the band controls the rest. -/
theorem measure_symmDiff_threshold_le (P : BandParameters) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {s t : ℝ} (hs : P.l1 * P.level k < s) (ht : P.l1 * P.level k < t) :
    (ν (symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t})).toReal
      ≤ C * P.weight k / P.level k * |s - t| + (ν {z : ℝ | -(z) > P.level k}).toReal := by
  set p : ℝ := min s t with hp
  set q : ℝ := max s t with hq
  set m : ℝ := min q (P.level k) with hm
  have hplow : P.l1 * P.level k < p := lt_min hs ht
  have hpqabs : q - p = |s - t| := by
    rcases le_total s t with h | h
    · rw [hp, hq, min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith : s - t ≤ 0)]
      ring
    · rw [hp, hq, min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)]
  have hCw : 0 ≤ C * P.weight k / P.level k :=
    div_nonneg (mul_nonneg hC.le (P.weight_pos k).le) (P.level_pos k).le
  -- the symmetric difference is covered by the part inside the band and the part above it
  have hsub : symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t}
      ⊆ Ico (-m) (-p) ∪ {z : ℝ | -(z) > P.level k} := by
    rw [symmDiff_thresholdSet]
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    by_cases hzk : -(z) > P.level k
    · exact Or.inr hzk
    · refine Or.inl ⟨?_, ?_⟩
      · have hzm : -(z) ≤ m := le_min h2 (le_of_not_gt hzk)
        linarith
      · linarith
  have hadd : (ν (symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t})).toReal
      ≤ (ν (Ico (-m) (-p))).toReal + (ν {z : ℝ | -(z) > P.level k}).toReal := by
    have h1 : ν (symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t})
        ≤ ν (Ico (-m) (-p)) + ν {z : ℝ | -(z) > P.level k} :=
      le_trans (measure_mono hsub) (measure_union_le _ _)
    have hfin : ν (Ico (-m) (-p)) + ν {z : ℝ | -(z) > P.level k} ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, measure_ne_top ν _⟩
    refine (ENNReal.toReal_mono hfin h1).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
  refine hadd.trans ?_
  have hband : (ν (Ico (-m) (-p))).toReal ≤ C * P.weight k / P.level k * |s - t| := by
    rcases le_or_gt m p with hcase | hcase
    · have hempty : Ico (-m) (-p) = (∅ : Set ℝ) :=
        Ico_eq_empty (by simpa using hcase)
      rw [hempty, measure_empty, ENNReal.toReal_zero]
      exact mul_nonneg hCw (abs_nonneg _)
    · have hεpos : 0 < m - p := by linarith
      have hpk : p ≤ P.level k := le_of_lt (lt_of_lt_of_le hcase (min_le_right q (P.level k)))
      have hsubIcc : Ico (-m) (-p) ⊆ Icc (-(p + (m - p))) (-p) := by
        intro z hz
        exact ⟨by have := hz.1; linarith, le_of_lt hz.2⟩
      have hmono := ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono hsubIcc)
      refine hmono.trans ?_
      have hb := hdens p hplow hpk (m - p) hεpos
      rw [div_le_iff₀ hεpos] at hb
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCw
      have hmq : m ≤ q := min_le_left q (P.level k)
      rw [← hpqabs]
      linarith
  linarith

/-- **The contact-error estimate of `eq:dgt4-band-contact-error` at
deterministic levels**, packaged from the band density bound. -/
theorem eventually_measure_symmDiff_threshold_le (P : BandParameters) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (hdens : BandDensity P ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ s t : ℝ,
      P.l1 * P.level k < s → P.l1 * P.level k < t →
        (ν (symmDiff {z : ℝ | -(z) > s} {z : ℝ | -(z) > t})).toReal
          ≤ C * P.weight k / P.level k * |s - t| + (ν {z : ℝ | -(z) > P.level k}).toReal := by
  obtain ⟨C, hC, hk⟩ := hdens
  exact ⟨C, hC, hk.mono fun k hk' s t hs ht =>
    measure_symmDiff_threshold_le P ν k hC hk' hs ht⟩

/-- **The mass above the bottom of the band is `(1+η)ω_k`**, by the band profile
at `r = 1`. -/
theorem measure_gt_band_bottom_le (P : BandParameters) (ν : Measure ℝ)
    (hprof : BandProfile P ν) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal ≤ (1 + η) * P.weight k := by
  filter_upwards [hprof η hη] with k hk
  have h1 := hk 1 ⟨zero_le_one, le_rfl⟩
  rw [Real.one_rpow] at h1
  have hlevel : P.level k - (1 - P.l1) * P.level k * 1 = P.l1 * P.level k := by ring
  rw [hlevel] at h1
  have hwk : 0 < P.weight k := P.weight_pos k
  have h2 : (ν {z : ℝ | -(z) > P.l1 * P.level k}).toReal / P.weight k ≤ 1 + η := by
    have := (abs_le.mp h1).2
    linarith
  rw [div_le_iff₀ hwk] at h2
  linarith

/-- **The band density bound on a half-open band interval.**  The band
`{p < -z ≤ q}` inside `[ℓ_1a_k, a_k]` has mass at most `Cω_k(q-p)/a_k`, including
when `p` is the bottom of the band itself, where the density bound is not
available: the interval is an increasing union of closed ones that are. -/
theorem measure_band_le (P : BandParameters) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {p q : ℝ} (hp : P.l1 * P.level k ≤ p) (hq : q ≤ P.level k) :
    (ν (Ico (-q) (-p))).toReal ≤ C * P.weight k / P.level k * max (q - p) 0 := by
  have hCw : 0 ≤ C * P.weight k / P.level k :=
    div_nonneg (mul_nonneg hC.le (P.weight_pos k).le) (P.level_pos k).le
  have hMnn : 0 ≤ C * P.weight k / P.level k * max (q - p) 0 :=
    mul_nonneg hCw (le_max_right _ _)
  rcases le_or_gt q p with hle | hlt
  · have hempty : Ico (-q) (-p) = (∅ : Set ℝ) := Ico_eq_empty (by simpa using hle)
    rw [hempty, measure_empty, ENNReal.toReal_zero]
    exact hMnn
  · set d : ℕ → ℝ := fun j => (q - p) / ((j : ℝ) + 2) with hd
    have hdpos : ∀ j, 0 < d j := by
      intro j
      rw [hd]
      have : (0 : ℝ) < (j : ℝ) + 2 := by positivity
      exact div_pos (by linarith) this
    have hdlt : ∀ j, d j < q - p := by
      intro j
      rw [hd]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 2)]
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    set s : ℕ → Set ℝ := fun j => Icc (-q) (-(p + d j)) with hs
    have hmono : Monotone s := by
      intro i j hij
      refine Icc_subset_Icc le_rfl ?_
      have hdle : d j ≤ d i := by
        rw [hd]
        refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
        have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
        linarith
      linarith
    have hunion : (⋃ j, s j) = Ico (-q) (-p) := by
      ext z
      simp only [Set.mem_iUnion, hs, mem_Icc, mem_Ico]
      constructor
      · rintro ⟨j, h1, h2⟩
        exact ⟨h1, by have := hdpos j; linarith⟩
      · rintro ⟨h1, h2⟩
        have hzp : 0 < -(z + p) := by linarith
        have hto : Tendsto d atTop (𝓝 0) := by
          rw [hd]
          have h3 : Tendsto (fun j : ℕ => ((j : ℝ) + 2)) atTop atTop :=
            tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
          exact h3.const_div_atTop (q - p)
        obtain ⟨j, hj⟩ := (hto.eventually_lt_const hzp).exists
        exact ⟨j, h1, by linarith⟩
    have hbd : ∀ j, ν (s j) ≤ ENNReal.ofReal (C * P.weight k / P.level k * max (q - p) 0) := by
      intro j
      have hlow : P.l1 * P.level k < p + d j := by have := hdpos j; linarith
      have hhigh : p + d j ≤ P.level k := by have := hdlt j; linarith
      have hε : 0 < q - (p + d j) := by have := hdlt j; linarith
      have hb := hdens (p + d j) hlow hhigh (q - (p + d j)) hε
      rw [div_le_iff₀ hε] at hb
      have heq : p + d j + (q - (p + d j)) = q := by ring
      rw [heq] at hb
      refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν _) hMnn).mpr ?_
      refine hb.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCw
      have := hdpos j
      have h4 : q - p ≤ max (q - p) 0 := le_max_left _ _
      linarith
    have hlim := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rw [hunion] at hlim
    have hle := le_of_tendsto hlim (Filter.Eventually.of_forall hbd)
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top ν _) hMnn).mp hle

/-- **The contact error at a deterministic level in the band and an arbitrary
second level.**  Splitting the scenery according to `{ξ ≤ ℓ_1a_k}`,
`{ℓ_1a_k < ξ ≤ a_k}` and `{ξ > a_k}`, as the paper does at
`sandpile.tex:6166-6175`: below the band the difference is carried by
`{w < ξ ≤ ℓ_1a_k}`, inside the band by the density bound, and above it by the
upper isolation. -/
theorem measure_symmDiff_threshold_split (P : BandParameters) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (k : ℕ) {C : ℝ} (hC : 0 < C)
    (hdens : ∀ t : ℝ, P.l1 * P.level k < t → t ≤ P.level k → ∀ ε : ℝ, 0 < ε →
      (ν (Icc (-(t + ε)) (-t))).toReal / ε ≤ C * P.weight k / P.level k)
    {w b : ℝ} (hb : P.l1 * P.level k ≤ b) :
    (ν (symmDiff {z : ℝ | -(z) > w} {z : ℝ | -(z) > b})).toReal
      ≤ (ν {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k}).toReal
        + C * P.weight k / P.level k * |w - b|
        + (ν {z : ℝ | -(z) > P.level k}).toReal := by
  set p : ℝ := min w b with hpdef
  set q : ℝ := max w b with hqdef
  set p' : ℝ := max p (P.l1 * P.level k) with hp'
  set q' : ℝ := min q (P.level k) with hq'
  have hpq : q - p = |w - b| := by
    rcases le_total w b with h | h
    · rw [hpdef, hqdef, min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith : w - b ≤ 0)]
      ring
    · rw [hpdef, hqdef, min_eq_right h, max_eq_left h,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - b)]
  have hmeasLow : MeasurableSet {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k} := by
    have : {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k}
        = Ico (-(P.l1 * P.level k)) (-w) := by
      ext z
      simp only [mem_setOf_eq, mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩; constructor <;> linarith
      · rintro ⟨h1, h2⟩; constructor <;> linarith
    rw [this]
    exact measurableSet_Ico
  -- the covering
  have hsub : symmDiff {z : ℝ | -(z) > w} {z : ℝ | -(z) > b}
      ⊆ {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k} ∪ Ico (-q') (-p')
        ∪ {z : ℝ | -(z) > P.level k} := by
    rw [symmDiff_thresholdSet]
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    rcases le_or_gt (-(z)) (P.l1 * P.level k) with hlow | hlow
    · refine Or.inl (Or.inl ⟨?_, hlow⟩)
      have hpb : p < b := by
        have : p < -(z) := h1
        linarith
      have hpw : p = w := by
        rw [hpdef]
        rcases le_total w b with h | h
        · exact min_eq_left h
        · exact absurd hpb (by rw [hpdef, min_eq_right h]; exact lt_irrefl b)
      rw [← hpw]
      exact h1
    · rcases le_or_gt (-(z)) (P.level k) with hhigh | hhigh
      · refine Or.inl (Or.inr ⟨?_, ?_⟩)
        · have : -(z) ≤ q' := le_min h2 hhigh
          linarith
        · have : p' < -(z) := max_lt h1 hlow
          linarith
      · exact Or.inr hhigh
  have hmiddle : (ν (Ico (-q') (-p'))).toReal
      ≤ C * P.weight k / P.level k * |w - b| := by
    have hle := measure_band_le P ν k hC hdens (p := p') (q := q')
      (le_max_right _ _) (min_le_right _ _)
    refine hle.trans ?_
    have hCw : 0 ≤ C * P.weight k / P.level k :=
      div_nonneg (mul_nonneg hC.le (P.weight_pos k).le) (P.level_pos k).le
    refine mul_le_mul_of_nonneg_left ?_ hCw
    refine max_le ?_ (by rw [← hpq]; linarith [min_le_max (a := w) (b := b)])
    rw [← hpq]
    have h1 : q' ≤ q := min_le_left _ _
    have h2 : p ≤ p' := le_max_left _ _
    linarith
  have hfin : ν ({z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k} ∪ Ico (-q') (-p'))
      + ν {z : ℝ | -(z) > P.level k} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, measure_ne_top ν _⟩
  have hstep : (ν (symmDiff {z : ℝ | -(z) > w} {z : ℝ | -(z) > b})).toReal
      ≤ (ν {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k}).toReal
        + (ν (Ico (-q') (-p'))).toReal + (ν {z : ℝ | -(z) > P.level k}).toReal := by
    have h1 : ν (symmDiff {z : ℝ | -(z) > w} {z : ℝ | -(z) > b})
        ≤ ν {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k} + ν (Ico (-q') (-p'))
          + ν {z : ℝ | -(z) > P.level k} := by
      refine le_trans (measure_mono hsub) ?_
      exact le_trans (measure_union_le _ _)
        (add_le_add (measure_union_le _ _) le_rfl)
    have hfin2 : ν {z : ℝ | w < -(z) ∧ -(z) ≤ P.l1 * P.level k} + ν (Ico (-q') (-p'))
        + ν {z : ℝ | -(z) > P.level k} ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, measure_ne_top ν _⟩, measure_ne_top ν _⟩
    refine (ENNReal.toReal_mono hfin2 h1).trans (le_of_eq ?_)
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top ν _, measure_ne_top ν _⟩) (measure_ne_top ν _),
      ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
  linarith

end Sandpile.Support
