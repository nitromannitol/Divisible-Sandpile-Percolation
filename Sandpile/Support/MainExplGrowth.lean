import Sandpile.Support.MainExplKolmogorovTail

/-!
# Deterministic growth bounds from almost sure growth

From the almost sure polynomial growth of the limit field to ONE growth bound that holds
outside an event of prescribed probability. The binder `hZgrow` of `thm:main-explosion`(i)(b)
chooses the amplitude and the degree after the sample point, as the repository's consumers
take them. The cutoff radius of the proof of that theorem cannot be chosen after the sample
point: it is fixed before the scale, and the discrete and the Brownian halves of the cutoff
error must use the same one. What the proof needs is therefore a deterministic amplitude and
degree valid off an event of probability at most the accuracy asked for, and that is what the
almost sure binder gives: the events `E_n` on which the field exceeds `n(1+|y|)^n` somewhere
on the strip decrease with `n` (`exists_deterministic_growth`) and their intersection is
contained in the null event where no amplitude and degree exist at all, so their
probabilities tend to zero. The events are measurable because the field is continuous on the
strip and the level is continuous there too, so the supremum over the strip is a supremum
over a countable dense subset of it, obtained by clamping the time coordinate with
`stripClamp` (`measurableSet_exists_strip_lt`). `exists_deterministic_growth_ae` extends this
to the case where the field is continuous on the strip only almost surely, as the Gaussian
heat potential comes.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {d : ℕ}

/-- The retraction of `ℝ × ℝ^d` onto the strip `[0,T] × ℝ^d`, which clamps the time. -/
noncomputable def stripClamp (T : ℝ) (q : ℝ × Sandpile.Continuum.Space d) :
    ℝ × Sandpile.Continuum.Space d := (max 0 (min T q.1), q.2)

/-- `stripClamp T` is continuous, being built from `max`, `min` and the two coordinate
projections, each of which is continuous. -/
theorem continuous_stripClamp (T : ℝ) : Continuous (stripClamp (d := d) T) := by
  apply Continuous.prodMk
  · exact (continuous_const.max (continuous_const.min continuous_fst))
  · exact continuous_snd

/-- For `T ≥ 0`, `stripClamp T q` always lands in the strip `[0, T] × Space d`, since clamping
the time coordinate with `max 0 (min T ·)` forces it into `[0, T]`. -/
theorem stripClamp_mem {T : ℝ} (hT : 0 ≤ T) (q : ℝ × Sandpile.Continuum.Space d) :
    stripClamp T q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) := by
  refine ⟨⟨le_max_left _ _, ?_⟩, Set.mem_univ _⟩
  exact max_le hT (min_le_left _ _)

/-- `stripClamp T` fixes every point already in the strip `[0, T] × Space d`, since the `min`
and `max` in its definition are then both no-ops. -/
theorem stripClamp_eq {T : ℝ} {q : ℝ × Sandpile.Continuum.Space d}
    (hq : q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :
    stripClamp T q = q := by
  obtain ⟨⟨h0, hT⟩, -⟩ := hq
  simp only [stripClamp]
  rw [min_eq_right hT, max_eq_right h0]

/-- **The event that a field exceeds a continuous level somewhere on the strip is
measurable.**  The field is continuous on the strip for every sample point, so the event is
the countable union over a dense subset of the strip. -/
theorem measurableSet_exists_strip_lt {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hmeas : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      Measurable (Z q.1 q.2))
    (hcont : ∀ ω, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (L : ℝ × Sandpile.Continuum.Space d → ℝ) (hL : Continuous L) :
    MeasurableSet {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      L q < |Z q.1 q.2 ω|} := by
  classical
  obtain ⟨D, hDc, hDd⟩ :=
    TopologicalSpace.exists_countable_dense (ℝ × Sandpile.Continuum.Space d)
  set E : Set (ℝ × Sandpile.Continuum.Space d) := stripClamp T '' D with hE
  have hEc : E.Countable := hDc.image _
  have hEsub : E ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) := by
    rintro _ ⟨x, -, rfl⟩; exact stripClamp_mem hT x
  have hEdense : Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))
      ⊆ closure E := by
    intro q hq
    have h2 : stripClamp T '' closure D ⊆ closure E :=
      image_closure_subset_closure_image (continuous_stripClamp T)
    rw [hDd.closure_eq] at h2
    have h3 : stripClamp T q ∈ closure E := h2 ⟨q, Set.mem_univ q, rfl⟩
    rwa [stripClamp_eq hq] at h3
  have hset : {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      L q < |Z q.1 q.2 ω|} = ⋃ q ∈ E, {ω | L q < |Z q.1 q.2 ω|} := by
    ext ω
    constructor
    · rintro ⟨q, hq, hlt⟩
      have hcw : ContinuousWithinAt
          (fun v : ℝ × Sandpile.Continuum.Space d => |Z v.1 v.2 ω| - L v)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) q :=
        ((hcont ω).abs.sub hL.continuousOn) q hq
      have hpos : 0 < |Z q.1 q.2 ω| - L q := by linarith
      have hev : ∀ᶠ v in nhdsWithin q
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))),
          0 < |Z v.1 v.2 ω| - L v := hcw.eventually (eventually_gt_nhds hpos)
      have hle : nhdsWithin q E ≤ nhdsWithin q
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :=
        nhdsWithin_mono q hEsub
      haveI hne : (nhdsWithin q E).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (hEdense hq)
      have h1 : ∀ᶠ v in nhdsWithin q E, 0 < |Z v.1 v.2 ω| - L v := hev.filter_mono hle
      have h2 : ∀ᶠ v in nhdsWithin q E, v ∈ E := self_mem_nhdsWithin
      obtain ⟨v, hv⟩ := (h1.and h2).exists
      refine Set.mem_iUnion₂.mpr ⟨v, hv.2, ?_⟩
      show L v < |Z v.1 v.2 ω|
      linarith [hv.1]
    · intro h
      obtain ⟨q, hq, hlt⟩ := Set.mem_iUnion₂.mp h
      exact ⟨q, hEsub hq, hlt⟩
  rw [hset]
  exact MeasurableSet.biUnion hEc
    (fun q hq => measurableSet_lt measurable_const (hmeas q (hEsub hq)).abs)

/-- **One amplitude and one degree serve every sample point outside an event of prescribed
probability.**  The almost sure growth binder of `thm:main-explosion`(i)(b) chooses them after
the sample point; the cutoff radius of the proof cannot be chosen after it, and this is what
supplies the deterministic pair the proof needs. -/
theorem exists_deterministic_growth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hmeas : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      Measurable (Z q.1 q.2))
    (hcont : ∀ ω, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, MeasurableSet {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ
          (Set.univ : Set (Sandpile.Continuum.Space d)),
        (m : ℝ) * (1 + ‖q.2‖) ^ m < |Z q.1 q.2 ω|} ∧
      P {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
          (m : ℝ) * (1 + ‖q.2‖) ^ m < |Z q.1 q.2 ω|} ≤ ENNReal.ofReal δ := by
  classical
  set Ev : ℕ → Set Ω := fun n =>
    {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      (n : ℝ) * (1 + ‖q.2‖) ^ n < |Z q.1 q.2 ω|} with hEv
  have hlevel : ∀ n : ℕ, Continuous
      (fun q : ℝ × Sandpile.Continuum.Space d => (n : ℝ) * (1 + ‖q.2‖) ^ n) := by
    intro n
    exact continuous_const.mul ((continuous_const.add continuous_snd.norm).pow n)
  have hEvm : ∀ n, MeasurableSet (Ev n) := fun n =>
    measurableSet_exists_strip_lt Z T hT hmeas hcont _ (hlevel n)
  have hanti : Antitone Ev := by
    intro n m hnm ω hω
    obtain ⟨q, hq, hlt⟩ := hω
    refine ⟨q, hq, lt_of_le_of_lt ?_ hlt⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
    have h2 : (1 + ‖q.2‖) ^ n ≤ (1 + ‖q.2‖) ^ m := pow_le_pow_right₀ h1 hnm
    have h3 : ((n : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hnm
    have h4 : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ n := by positivity
    nlinarith [pow_nonneg (le_trans zero_le_one h1) m]
  have hnull : P (⋂ n, Ev n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hgrow)
    intro ω hω
    simp only [Set.mem_iInter, hEv, Set.mem_setOf_eq] at hω
    intro hgood
    obtain ⟨C, k, hCk⟩ := hgood
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (max k 1))
    obtain ⟨q, hq, hlt⟩ := hω n
    have hC : C ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
    have hk : k ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
    have hrp : (1 + ‖q.2‖) ^ k ≤ (1 + ‖q.2‖) ^ ((n : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 hk
    have hnat : (1 + ‖q.2‖) ^ ((n : ℕ) : ℝ) = (1 + ‖q.2‖) ^ (n : ℕ) :=
      Real.rpow_natCast _ _
    have hb := hCk q hq
    have hpos : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ (n : ℕ) := by positivity
    have hCn : C * (1 + ‖q.2‖) ^ k ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := by
      rw [hnat] at hrp
      have hC0 : (0 : ℝ) ≤ C ∨ C < 0 := le_or_gt 0 C
      rcases hC0 with hC0 | hC0
      · calc C * (1 + ‖q.2‖) ^ k ≤ C * (1 + ‖q.2‖) ^ (n : ℕ) :=
              mul_le_mul_of_nonneg_left hrp hC0
          _ ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := mul_le_mul_of_nonneg_right hC hpos
      · have hrk : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ k := Real.rpow_nonneg (by positivity) k
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
    linarith
  have hten : Filter.Tendsto (fun n => P (Ev n)) Filter.atTop (nhds (P (⋂ n, Ev n))) :=
    tendsto_measure_iInter_atTop (fun n => (hEvm n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top P _⟩
  rw [hnull] at hten
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨m, hm⟩ := (hten.eventually_lt_const hpos).exists
  exact ⟨m, hEvm m, hm.le⟩

/-- **The deterministic growth bound when the field is continuous on the strip only almost
surely**, which is how the Gaussian heat potential comes.  The field is changed to zero on a
measurable null superset of the set where continuity fails; that changes nothing off a null
set, and the changed field is continuous on the strip at EVERY sample point, so the events of
the previous theorem are measurable for it. -/
theorem exists_deterministic_growth_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hmeas : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      Measurable (Z q.1 q.2))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (N : Set Ω), P N ≤ ENNReal.ofReal δ ∧
      ∀ ω ∉ N, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d,
        |Z s y ω| ≤ (m : ℝ) * (1 + ‖y‖) ^ m := by
  classical
  set Bad : Set Ω := {ω | ¬ ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))} with hBad
  have hBad0 : P Bad = 0 := ae_iff.mp hcont
  set N₀ : Set Ω := toMeasurable P Bad with hN₀
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable P Bad
  have hN₀0 : P N₀ = 0 := by rw [hN₀, measure_toMeasurable]; exact hBad0
  have hsubN : Bad ⊆ N₀ := subset_toMeasurable P Bad
  set Z' : ℝ → Sandpile.Continuum.Space d → Ω → ℝ :=
    fun s y ω => if ω ∈ N₀ then 0 else Z s y ω with hZ'
  have hmeas' : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      Measurable (Z' q.1 q.2) := by
    intro q hq
    exact Measurable.ite hN₀m measurable_const (hmeas q hq)
  have hcont' : ∀ ω, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z' q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := by
    intro ω
    by_cases hω : ω ∈ N₀
    · simpa only [hZ', hω, if_pos] using (continuousOn_const :
        ContinuousOn (fun _ : ℝ × Sandpile.Continuum.Space d => (0 : ℝ)) _)
    · have hc : ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :=
        not_not.mp (fun h => hω (hsubN h))
      simpa only [hZ', hω, if_neg, not_false_iff] using hc
  have hgrow' : ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z' q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k := by
    filter_upwards [hgrow] with ω hω
    by_cases hN : ω ∈ N₀
    · refine ⟨0, 0, fun q _ => ?_⟩
      simp only [hZ', hN, if_pos, abs_zero, zero_mul, le_refl]
    · obtain ⟨C, k, hCk⟩ := hω
      refine ⟨C, k, fun q hq => ?_⟩
      simpa only [hZ', hN, if_neg, not_false_iff] using hCk q hq
  obtain ⟨m, hEm, hE⟩ := exists_deterministic_growth P Z' T hT hmeas' hcont' hgrow' δ hδ
  refine ⟨m, {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ
      (Set.univ : Set (Sandpile.Continuum.Space d)),
      (m : ℝ) * (1 + ‖q.2‖) ^ m < |Z' q.1 q.2 ω|} ∪ N₀, ?_, ?_⟩
  · refine le_trans (measure_union_le _ _) ?_
    rw [hN₀0, add_zero]
    exact hE
  · intro ω hω s hs y
    have h1 : ω ∉ N₀ := fun h => hω (Or.inr h)
    have h2 : ¬ ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ
        (Set.univ : Set (Sandpile.Continuum.Space d)),
        (m : ℝ) * (1 + ‖q.2‖) ^ m < |Z' q.1 q.2 ω| := fun h => hω (Or.inl h)
    have h3 : ¬ ((m : ℝ) * (1 + ‖y‖) ^ m < |Z' s y ω|) :=
      fun h => h2 ⟨(s, y), ⟨hs, Set.mem_univ y⟩, h⟩
    have h4 : Z' s y ω = Z s y ω := by
      simp only [hZ', h1, if_neg, not_false_iff]
    rw [← h4]
    exact not_lt.mp h3


end Sandpile.Support
