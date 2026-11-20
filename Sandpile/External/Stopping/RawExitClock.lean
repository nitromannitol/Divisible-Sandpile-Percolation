import Sandpile.Continuum.Stopping
import LatticeProb.Prob.BrownianOpenExitStopping

/-!
# Raw exit clocks for almost surely continuous paths

For a process indexed by `ℝ≥0` whose paths are all continuous, the first exit
time from an open set is a stopping time of the raw natural filtration
(`LatticeProb.isStoppingTime_openExitTime`).  When only almost every path is
continuous this argument breaks down on the exceptional paths.  This file builds,
for an arbitrary process, an open set `U` and a horizon `T`, a stopping time of
the raw natural filtration which is bounded by `T` and agrees with the exit time
truncated at `T` on every continuous path.

The clock observes the path only at rational times.  The gap
`rationalExitGap B U ω t` is the infimum, over rational times `q < t`, of the
extended distance from the path to `Uᶜ` (negative rationals are read as time
`0`).  It is antitone in `t`, it is measurable with respect to the natural
filtration at time `t`, and on a continuous path it vanishes exactly from the
exit time on.  The clock `rawExitClock B U T` is the first zero of the gap when
that infimum is attained before `T`, and `T` otherwise.  Its stopping events are
described by countably many conditions on the gap at rational times, using that
the gap at a positive time is the infimum of the gaps at earlier rational times.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

variable {Ω : Type*} {d : ℕ}

/-- The infimum, over rational times `q < t`, of the extended distance from the
path to the complement of `U`; negative rationals are read as time `0`. -/
noncomputable def rationalExitGap (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (ω : Ω) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ q : {q : ℚ // (q : ℝ) < t}, Metric.infEDist (B (Real.toNNReal q) ω) Uᶜ

/-- The infimum of the times at which the rational exit gap vanishes. -/
noncomputable def rationalExitStart (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (ω : Ω) : ℝ≥0 :=
  sInf {t : ℝ≥0 | rationalExitGap B U ω t = 0}

open scoped Classical in
/-- The raw exit clock: the first zero of the rational exit gap when it is
attained no later than `T`, and `T` otherwise. -/
noncomputable def rawExitClock (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if rationalExitGap B U ω (rationalExitStart B U ω) = 0 ∧ rationalExitStart B U ω ≤ T then
    rationalExitStart B U ω
  else T

/-- The rational exit gap at `t` is at most the distance observed at any
rational time before `t`. -/
theorem rationalExitGap_le (B : ℝ≥0 → Ω → Continuum.Space d) (U : Set (Continuum.Space d))
    (ω : Ω) {t : ℝ≥0} {q : ℚ} (hq : (q : ℝ) < t) :
    rationalExitGap B U ω t ≤ Metric.infEDist (B (Real.toNNReal q) ω) Uᶜ :=
  iInf_le (fun q : {q : ℚ // (q : ℝ) < t} =>
    Metric.infEDist (B (Real.toNNReal q) ω) Uᶜ) ⟨q, hq⟩

/-- The rational exit gap is antitone in time. -/
theorem rationalExitGap_antitone (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (ω : Ω) : Antitone (rationalExitGap B U ω) := by
  intro s t hst
  refine le_iInf fun q => rationalExitGap_le B U ω (lt_of_lt_of_le q.2 ?_)
  exact_mod_cast hst

/-- The rational exit gap at time `s ≤ t` is measurable for the natural
filtration at time `t`. -/
theorem measurable_rationalExitGap (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[Continuum.brownianFiltration B t] (fun ω => rationalExitGap B U ω s) := by
  unfold rationalExitGap
  refine Measurable.iInf fun q => ?_
  have hq : Real.toNNReal (q : ℝ) ≤ t := by
    rw [Real.toNNReal_le_iff_le_coe]
    exact q.2.le.trans (by exact_mod_cast hst)
  exact Metric.continuous_infEDist.measurable.comp
    (Continuum.measurable_brownianFiltration B _ t hq)

/-- On a continuous path and for an open set, the rational exit gap vanishes at
`t` exactly when the path has left the set by time `t`. -/
theorem rationalExitGap_eq_zero_iff {B : ℝ≥0 → Ω → Continuum.Space d}
    {U : Set (Continuum.Space d)} (hU : IsOpen U) {ω : Ω}
    (hc : Continuous fun s => B s ω) (t : ℝ≥0) :
    rationalExitGap B U ω t = 0 ↔ LatticeProb.openExitTime B U ω ≤ t := by
  constructor
  · intro h0
    by_contra hlt
    rw [not_le] at hlt
    have hin : ∀ s ≤ t, B s ω ∈ U := fun s hs =>
      LatticeProb.mem_of_lt_openExitTime (lt_of_le_of_lt (by exact_mod_cast hs) hlt)
    have hfc : ContinuousOn (fun s => Metric.infEDist (B s ω) Uᶜ) (Icc 0 t) :=
      (Metric.continuous_infEDist.comp hc).continuousOn
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.2 zero_le⟩ hfc
    have hpos : 0 < Metric.infEDist (B s₀ ω) Uᶜ := by
      rw [pos_iff_ne_zero]
      intro h
      have hmem := Metric.mem_closure_iff_infEDist_zero.2 h
      rw [hU.isClosed_compl.closure_eq] at hmem
      exact hmem (hin s₀ hs₀.2)
    have hle : Metric.infEDist (B s₀ ω) Uᶜ ≤ rationalExitGap B U ω t := by
      refine le_iInf fun q => ?_
      have hqt : Real.toNNReal (q : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.2 q.2.le
      exact isMinOn_iff.1 hmin _ ⟨zero_le, hqt⟩
    rw [h0] at hle
    exact absurd hle (not_le.2 hpos)
  · intro hle
    obtain ⟨s, hs, hout⟩ : ∃ s ≤ t, B s ω ∉ U := by
      have h := (LatticeProb.openExitTime_le_iff_not_mapsTo hU hc t).1 hle
      by_contra hno
      apply h
      intro s hs
      by_contra hout
      exact hno ⟨s, hs.2, hout⟩
    by_contra hne
    have hpos : 0 < rationalExitGap B U ω t := pos_iff_ne_zero.2 hne
    have hf : Continuous fun y : ℝ => Metric.infEDist (B (Real.toNNReal y) ω) Uᶜ :=
      Metric.continuous_infEDist.comp (hc.comp continuous_real_toNNReal)
    have hW : IsOpen {y : ℝ | Metric.infEDist (B (Real.toNNReal y) ω) Uᶜ <
        rationalExitGap B U ω t} :=
      isOpen_lt hf continuous_const
    have hsW : (s : ℝ) ∈ {y : ℝ | Metric.infEDist (B (Real.toNNReal y) ω) Uᶜ <
        rationalExitGap B U ω t} := by
      simp only [mem_ofPred_eq, Real.toNNReal_coe,
        Metric.infEDist_zero_of_mem (show B s ω ∈ Uᶜ from hout)]
      exact hpos
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW _ hsW
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) - ε < s by linarith)
    have hqW : Metric.infEDist (B (Real.toNNReal q) ω) Uᶜ < rationalExitGap B U ω t :=
      hball (show (q : ℝ) ∈ Metric.ball (s : ℝ) ε by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith)
    have hqt : (q : ℝ) < t := lt_of_lt_of_le hq2 (by exact_mod_cast hs)
    exact absurd (rationalExitGap_le B U ω hqt) (not_le.2 hqW)

/-- The gap at a positive time is at least any common lower bound of the gaps at
earlier nonnegative rational times. -/
theorem le_rationalExitGap_of_forall_rat (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (ω : Ω) {a : ℝ≥0} (ha : 0 < a) {c : ℝ≥0∞}
    (h : ∀ r : ℚ, (0 : ℝ) ≤ r → (r : ℝ) < a → c ≤ rationalExitGap B U ω (Real.toNNReal r)) :
    c ≤ rationalExitGap B U ω a := by
  refine le_iInf fun q => ?_
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt q.2 ha')
  have hr0 : (0 : ℝ) ≤ r := (le_max_right _ _).trans hr1.le
  have hqr : (q : ℝ) < (Real.toNNReal r : ℝ) := by
    rw [Real.coe_toNNReal _ hr0]
    exact lt_of_le_of_lt (le_max_left _ _) hr1
  exact (h r hr0 hr2).trans (rationalExitGap_le B U ω hqr)

/-- A vanishing gap bounds the start of the zero set. -/
theorem rationalExitStart_le {B : ℝ≥0 → Ω → Continuum.Space d}
    {U : Set (Continuum.Space d)} {ω : Ω} {t : ℝ≥0} (h : rationalExitGap B U ω t = 0) :
    rationalExitStart B U ω ≤ t :=
  csInf_le (OrderBot.bddBelow _) h

/-- Past the start of a nonempty zero set, the gap vanishes. -/
theorem rationalExitGap_eq_zero_of_start_lt {B : ℝ≥0 → Ω → Continuum.Space d}
    {U : Set (Continuum.Space d)} {ω : Ω} {s t : ℝ≥0} (hs : rationalExitGap B U ω s = 0)
    (ht : rationalExitStart B U ω < t) : rationalExitGap B U ω t = 0 := by
  obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt ⟨s, hs⟩ ht
  have hu0 : rationalExitGap B U ω u = 0 := hu
  exact le_antisymm ((rationalExitGap_antitone B U ω hut.le).trans (le_of_eq hu0)) zero_le

/-- The raw exit clock never exceeds the horizon. -/
theorem rawExitClock_le (B : ℝ≥0 → Ω → Continuum.Space d) (U : Set (Continuum.Space d))
    (T : ℝ≥0) (ω : Ω) : rawExitClock B U T ω ≤ T := by
  unfold rawExitClock
  split_ifs with h
  · exact h.2
  · exact le_rfl

/-- The event that the gap vanishes at `t` although its zero set starts with a
positive gap, detected through a positive lower bound `c` at rational times. -/
def rawExitDefect (B : ℝ≥0 → Ω → Continuum.Space d) (U : Set (Continuum.Space d))
    (t : ℝ≥0) (c : ℝ≥0∞) : Set Ω :=
  {ω | rationalExitGap B U ω t = 0 ∧ c ≤ rationalExitGap B U ω 0 ∧
    ∀ r : ℚ, (0 : ℝ) ≤ r → (r : ℝ) < t →
      rationalExitGap B U ω (Real.toNNReal r) = 0 ∨ c ≤ rationalExitGap B U ω (Real.toNNReal r)}

/-- The defect events are measurable for the natural filtration at time `t`. -/
theorem measurableSet_rawExitDefect (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (t : ℝ≥0) (c : ℝ≥0∞) :
    MeasurableSet[Continuum.brownianFiltration B t] (rawExitDefect B U t c) := by
  have hg : ∀ s ≤ t, Measurable[Continuum.brownianFiltration B t]
      (fun ω => rationalExitGap B U ω s) := fun s hs => measurable_rationalExitGap B U hs
  have hzero : ∀ s ≤ t, MeasurableSet[Continuum.brownianFiltration B t]
      {ω | rationalExitGap B U ω s = 0} := fun s hs => hg s hs (measurableSet_singleton 0)
  have hlow : ∀ s ≤ t, MeasurableSet[Continuum.brownianFiltration B t]
      {ω | c ≤ rationalExitGap B U ω s} := fun s hs => measurableSet_le measurable_const (hg s hs)
  have heq : rawExitDefect B U t c = {ω | rationalExitGap B U ω t = 0} ∩
      {ω | c ≤ rationalExitGap B U ω 0} ∩
      ⋂ r : {r : ℚ // (0 : ℝ) ≤ r ∧ (r : ℝ) < t},
        ({ω | rationalExitGap B U ω (Real.toNNReal ((r : ℚ) : ℝ)) = 0} ∪
          {ω | c ≤ rationalExitGap B U ω (Real.toNNReal ((r : ℚ) : ℝ))}) := by
    ext ω
    simp only [rawExitDefect, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, Subtype.forall,
      and_imp, and_assoc]
  rw [heq]
  refine ((hzero t le_rfl).inter (hlow 0 zero_le)).inter (MeasurableSet.iInter fun r => ?_)
  have hr : Real.toNNReal ((r : ℚ) : ℝ) ≤ t := Real.toNNReal_le_iff_le_coe.2 r.2.2.le
  exact (hzero _ hr).union (hlow _ hr)

/-- A defect event with a positive bound forces a positive gap at the start of
the zero set. -/
theorem rationalExitGap_start_ne_zero_of_mem_rawExitDefect
    {B : ℝ≥0 → Ω → Continuum.Space d} {U : Set (Continuum.Space d)} {t : ℝ≥0} {c : ℝ≥0∞}
    (hc : 0 < c) {ω : Ω} (hω : ω ∈ rawExitDefect B U t c) :
    rationalExitGap B U ω (rationalExitStart B U ω) ≠ 0 := by
  rw [rawExitDefect, mem_ofPred_eq] at hω
  obtain ⟨ht, h0, hr⟩ := hω
  have hat : rationalExitStart B U ω ≤ t := rationalExitStart_le ht
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ rationalExitStart B U ω) with ha | ha
  · rw [← ha]
    exact (lt_of_lt_of_le hc h0).ne'
  · refine (lt_of_lt_of_le hc (le_rationalExitGap_of_forall_rat B U ω ha ?_)).ne'
    intro r hr0 hra
    have hrt : (r : ℝ) < t := lt_of_lt_of_le hra (by exact_mod_cast hat)
    rcases hr r hr0 hrt with hz | hcr
    · have hle := rationalExitStart_le hz
      have hlt : Real.toNNReal (r : ℝ) < rationalExitStart B U ω := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
        exact hra
      exact absurd hle (not_le.2 hlt)
    · exact hcr

/-- A positive gap at the start of a nonempty zero set is detected by a defect
event with bound `1 / n`. -/
theorem exists_mem_rawExitDefect {B : ℝ≥0 → Ω → Continuum.Space d}
    {U : Set (Continuum.Space d)} {t : ℝ≥0} {ω : Ω} (ht : rationalExitGap B U ω t = 0)
    (ha : rationalExitGap B U ω (rationalExitStart B U ω) ≠ 0) :
    ∃ n : ℕ, ω ∈ rawExitDefect B U t ((n : ℝ≥0∞)⁻¹) := by
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt ha
  refine ⟨n, ?_⟩
  rw [rawExitDefect, mem_ofPred_eq]
  refine ⟨ht, hn.le.trans (rationalExitGap_antitone B U ω zero_le), ?_⟩
  intro r _ _
  rcases le_or_gt (Real.toNNReal (r : ℝ)) (rationalExitStart B U ω) with hra | hra
  · exact Or.inr (hn.le.trans (rationalExitGap_antitone B U ω hra))
  · exact Or.inl (rationalExitGap_eq_zero_of_start_lt ht hra)

/-- Before the horizon, the stopping events of the raw exit clock are the
vanishing of the gap with every defect excluded. -/
theorem setOf_rawExitClock_le (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) {T t : ℝ≥0} (htT : t < T) :
    {ω | rawExitClock B U T ω ≤ t} =
      {ω | rationalExitGap B U ω t = 0} \ ⋃ n : ℕ, rawExitDefect B U t ((n : ℝ≥0∞)⁻¹) := by
  ext ω
  simp only [mem_ofPred_eq, mem_sdiff, mem_iUnion, not_exists]
  constructor
  · intro hκ
    unfold rawExitClock at hκ
    split_ifs at hκ with h
    · have ht : rationalExitGap B U ω t = 0 :=
        le_antisymm ((rationalExitGap_antitone B U ω hκ).trans (le_of_eq h.1)) zero_le
      refine ⟨ht, fun n hn => ?_⟩
      exact rationalExitGap_start_ne_zero_of_mem_rawExitDefect
        (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)) hn h.1
    · exact absurd hκ (not_le.2 htT)
  · rintro ⟨ht, hdef⟩
    have hat := rationalExitStart_le ht
    have hz : rationalExitGap B U ω (rationalExitStart B U ω) = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := exists_mem_rawExitDefect ht hne
      exact hdef n hn
    unfold rawExitClock
    rw [ite_eq_left ⟨hz, hat.trans htT.le⟩]
    exact hat

/-- **The raw exit clock is a stopping time of the raw natural filtration.** -/
theorem isBrownianStopping_rawExitClock (B : ℝ≥0 → Ω → Continuum.Space d)
    (U : Set (Continuum.Space d)) (T : ℝ≥0) :
    Continuum.IsBrownianStopping B (rawExitClock B U T) := by
  intro t
  change MeasurableSet[Continuum.brownianFiltration B t]
    {ω | ((rawExitClock B U T ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
  have hset : {ω | ((rawExitClock B U T ω : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
      {ω | rawExitClock B U T ω ≤ t} := by
    ext ω
    exact ENNReal.coe_le_coe
  rw [hset]
  by_cases hT : T ≤ t
  · have huniv : {ω | rawExitClock B U T ω ≤ t} = univ :=
      eq_univ_of_forall fun ω => (rawExitClock_le B U T ω).trans hT
    rw [huniv]
    exact MeasurableSet.univ
  · rw [setOf_rawExitClock_le B U (not_le.1 hT)]
    exact (measurable_rationalExitGap B U (le_refl t) (measurableSet_singleton 0)).diff
      (MeasurableSet.iUnion fun n => measurableSet_rawExitDefect B U t _)

/-- On a continuous path, the raw exit clock is the exit time from the open set
truncated at the horizon. -/
theorem rawExitClock_eq_of_continuous {B : ℝ≥0 → Ω → Continuum.Space d}
    {U : Set (Continuum.Space d)} (hU : IsOpen U) (T : ℝ≥0) {ω : Ω}
    (hc : Continuous fun s => B s ω) :
    rawExitClock B U T ω = (min (LatticeProb.openExitTime B U ω) (T : ℝ≥0∞)).toNNReal := by
  have hZ := rationalExitGap_eq_zero_iff hU hc
  unfold rawExitClock
  rcases eq_or_ne (LatticeProb.openExitTime B U ω) ⊤ with he | he
  · have hne : rationalExitGap B U ω (rationalExitStart B U ω) ≠ 0 := by
      rw [Ne, hZ, he, top_le_iff]
      exact ENNReal.coe_ne_top
    rw [ite_eq_right (fun h => hne h.1), he, min_eq_right le_top, ENNReal.toNNReal_coe]
  · obtain ⟨e, hee⟩ : ∃ e : ℝ≥0, LatticeProb.openExitTime B U ω = (e : ℝ≥0∞) :=
      ⟨_, (ENNReal.coe_toNNReal he).symm⟩
    have hzero : {t : ℝ≥0 | rationalExitGap B U ω t = 0} = Ici e := by
      ext t
      rw [mem_ofPred_eq, hZ, hee, ENNReal.coe_le_coe, mem_Ici]
    have hstart : rationalExitStart B U ω = e := by
      rw [rationalExitStart, hzero, csInf_Ici]
    have hge : rationalExitGap B U ω e = 0 := by
      rw [hZ, hee]
    rw [hstart, hee, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
    by_cases heT : e ≤ T
    · rw [ite_eq_left ⟨hge, heT⟩, min_eq_left heT]
    · rw [ite_eq_right (fun h => heT h.2), min_eq_right (not_le.1 heT).le]

end Sandpile.External.Stopping
