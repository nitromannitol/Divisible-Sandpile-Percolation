import Sandpile.Support.TranslatedBrownianValueContinuity
import Sandpile.Support.BrownianValueLaw
import Mathlib.Topology.Sequences

/-!
# Continuity of Brownian stopping values

Brownian path-law invariance and uniform control of clipped rewards yield joint
continuity of the finite-horizon value in remaining time and starting point.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian stopping value is jointly continuous in remaining horizon and
starting point for continuous rewards of polynomial growth. -/
theorem Sandpile.Support.continuousOn_brownian_snellValue
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ContinuousOn (fun p : ℝ≥0 × Sandpile.Continuum.Space d =>
      Sandpile.External.Snell.snellValue (B p.2) P G ((T : ℝ) - p.1))
      (Set.Icc 0 T ×ˢ Set.univ) := by
  let U := Set.Icc (0 : ℝ≥0) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))
  let W := B 0
  have hEq : ∀ s ≤ T, ∀ y : Sandpile.Continuum.Space d,
      Sandpile.External.Snell.snellValue (B y) P G ((T : ℝ) - s) =
        Sandpile.External.Snell.snellValue (fun t ω => y + W t ω) P G (T - s : ℝ≥0) := by
    intro s hs y
    have hshift : Sandpile.Continuum.IsBrownian d y (fun t ω => y + W t ω) P :=
      Sandpile.Support.isBrownian_add_const d P W (hB 0) y
    have hshiftm : ∀ t, StronglyMeasurable (fun ω => y + W t ω) := fun t =>
      (measurable_const.add (hBm 0 t).measurable).stronglyMeasurable
    have hshiftc : ∀ ω, Continuous fun t => y + W t ω := fun ω =>
      continuous_const.add (hBc 0 ω)
    have hle : ((T - s : ℝ≥0) : ℝ) ≤ (T : ℝ) := by exact_mod_cast (tsub_le_self : T - s ≤ T)
    have hGs : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 ((T - s : ℝ≥0) : ℝ) ×ˢ Set.univ) := hG.mono (by
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans hle⟩, hp.2⟩)
    have hgs : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) ((T - s : ℝ≥0) : ℝ),
        ∀ z, |G t z| ≤ C * (1 + ‖z‖) ^ k := by
      obtain ⟨C, k, hk⟩ := hgrow
      exact ⟨C, k, fun t ht z => hk t ⟨ht.1, ht.2.trans hle⟩ z⟩
    rw [← NNReal.coe_sub hs]
    exact Sandpile.Support.snellValue_eq_of_isBrownian y P P (B y) (fun t ω => y + W t ω)
      (hB y) hshift (hBm y) hshiftm (hBc y) hshiftc (T - s) G hGs hgs
  change ContinuousOn _ U
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_seqContinuous]
  intro seq p hseq
  let ys : ℕ → Sandpile.Continuum.Space d := fun n => (seq n).1.2
  let z : Sandpile.Continuum.Space d := p.1.2
  let us : ℕ → ℝ≥0 := fun n => T - (seq n).1.1
  let v : ℝ≥0 := T - p.1.1
  have hys : Tendsto ys atTop (𝓝 z) :=
    ((continuous_snd.comp continuous_subtype_val).tendsto p).comp hseq
  have hus : Tendsto us atTop (𝓝 v) :=
    (tendsto_const_nhds.sub (((continuous_fst.comp continuous_subtype_val).tendsto p).comp hseq))
  have hbounded : Bornology.IsBounded (Set.range ys ∪ {z}) :=
    (Metric.isBounded_range_of_tendsto ys hys).union Bornology.isBounded_singleton
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbounded
  let R' : ℝ := max R 0
  let K : Set (Sandpile.Continuum.Space d) := Metric.closedBall 0 R'
  have hK : IsCompact K := isCompact_closedBall 0 R'
  have hR' : 0 ≤ R' := le_max_right _ _
  have hKR : ∀ y ∈ K, ‖y‖ ≤ R' := by
    intro y hy
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hy
  have hy : ∀ n, ys n ∈ K := by
    intro n
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact (hR (ys n) (Or.inl ⟨n, rfl⟩)).trans (le_max_left _ _)
  have hz : z ∈ K := by
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact (hR z (Or.inr rfl)).trans (le_max_left _ _)
  have hu : ∀ n, us n ≤ T := fun n => tsub_le_self
  have hv : v ≤ T := tsub_le_self
  have hlim := Sandpile.Support.tendsto_snellValue_translated P W (hB 0) (hBm 0) (hBc 0)
    T G hG hgrow K hK R' hR' hKR us v hu hv ys z hy hz hus hys
  have hEqseq : ∀ n, Sandpile.External.Snell.snellValue (B (ys n)) P G
      ((T : ℝ) - (seq n).1.1) =
      Sandpile.External.Snell.snellValue (fun t ω => ys n + W t ω) P G (us n) :=
    fun n => hEq _ (seq n).2.1.2 _
  have hEqp : Sandpile.External.Snell.snellValue (B z) P G ((T : ℝ) - p.1.1) =
      Sandpile.External.Snell.snellValue (fun t ω => z + W t ω) P G v := hEq _ p.2.1.2 _
  change Tendsto (fun n => Sandpile.External.Snell.snellValue (B (ys n)) P G
    ((T : ℝ) - (seq n).1.1)) atTop
    (𝓝 (Sandpile.External.Snell.snellValue (B z) P G ((T : ℝ) - p.1.1)))
  simp_rw [hEqseq, hEqp]
  exact hlim
