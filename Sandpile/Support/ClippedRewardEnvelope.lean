import Sandpile.Support.ClippedRewardUniform
import Sandpile.Support.BrownianPolynomialReward
import LatticeProb.Prob.GaussSupTailField

/-!
# Integrable envelopes for clipped reward differences

Uniform continuity along paths and an integrable reward bound yield integrable
uniform discrepancies that converge to zero in expectation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Clipped reward differences for converging horizons and starting points
have integrable uniform envelopes whose expectations converge to zero. -/
theorem Sandpile.Support.exists_integrable_clipped_reward_envelopes
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (u : ℕ → ℝ≥0) (v : ℝ≥0) (hu : ∀ n, u n ≤ T) (hv : v ≤ T)
    (y : ℕ → Sandpile.Continuum.Space d) (z : Sandpile.Continuum.Space d)
    (hy : ∀ n, y n ∈ K) (hz : z ∈ K)
    (huv : Tendsto u atTop (𝓝 v)) (hyz : Tendsto y atTop (𝓝 z))
    (bound : Ω → ℝ) (hint : Integrable bound P)
    (hbound : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ q ∈ K,
      ∀ s ≤ T, ‖G r (q + B s ω)‖ ≤ bound ω) :
    ∃ D : ℕ → Ω → ℝ, (∀ n, Integrable (D n) P) ∧
      (∀ᵐ ω ∂P, ∀ n s, s ≤ T →
        |G ((u n : ℝ) - min s (u n)) (y n + B (min s (u n)) ω) -
          G ((v : ℝ) - min s v) (z + B (min s v) ω)| ≤ D n ω) ∧
      Tendsto (fun n => ∫ ω, D n ω ∂P) atTop (𝓝 0) := by
  classical
  let I := Set.Icc (0 : ℝ≥0) T
  have : Nonempty I := ⟨⟨0, ⟨le_rfl, zero_le⟩⟩⟩
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let R : ℕ → I → Ω → ℝ := fun n s ω =>
    G ((u n : ℝ) - min s.1 (u n)) (y n + B (min s.1 (u n)) ω) -
    G ((v : ℝ) - min s.1 v) (z + B (min s.1 v) ω)
  have hRc : ∀ n ω, Continuous fun s => |R n s ω| := by
    intro n ω
    have h1 : Continuous (fun s : I =>
        G ((u n : ℝ) - min s.1 (u n)) (y n + B (min s.1 (u n)) ω)) := by
      change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
        fun s : I => ((u n : ℝ) - min s.1 (u n), y n + B (min s.1 (u n)) ω))
      apply hG.comp_continuous
      · fun_prop
      · intro s
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · exact sub_nonneg.mpr (by exact_mod_cast min_le_right s.1 (u n))
        · exact (sub_le_self _ (min s.1 (u n)).coe_nonneg).trans (by exact_mod_cast hu n)
    have h2 : Continuous (fun s : I =>
        G ((v : ℝ) - min s.1 v) (z + B (min s.1 v) ω)) := by
      change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
        fun s : I => ((v : ℝ) - min s.1 v, z + B (min s.1 v) ω))
      apply hG.comp_continuous
      · fun_prop
      · intro s
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · exact sub_nonneg.mpr (by exact_mod_cast min_le_right s.1 v)
        · exact (sub_le_self _ (min s.1 v).coe_nonneg).trans (by exact_mod_cast hv)
    exact (h1.sub h2).abs
  have hRbdd : ∀ n ω, BddAbove (Set.range fun s : I => |R n s ω|) := fun n ω =>
    (isCompact_range (hRc n ω)).bddAbove
  let D : ℕ → Ω → ℝ := fun n ω => ⨆ s : I, |R n s ω|
  have hDnonneg : ∀ n ω, 0 ≤ D n ω := fun n ω =>
    (abs_nonneg _).trans (le_ciSup (hRbdd n ω) (Classical.choice inferInstance))
  have hDmajor : ∀ n ω s (hs : s ≤ T), |R n ⟨s, zero_le, hs⟩ ω| ≤ D n ω := by
    intro n ω s hs
    exact le_ciSup (hRbdd n ω) ⟨s, zero_le, hs⟩
  have hGslice : ∀ r ∈ Set.Icc (0 : ℝ) (T : ℝ), Continuous (G r) := by
    intro r hr
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘ fun y => (r, y))
    exact hG.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hr, Set.mem_univ _⟩)
  have hDm : ∀ n, Measurable (D n) := by
    intro n
    have heq : D n = fun ω => ⨆ k, |R n (TopologicalSpace.denseSeq I k) ω| := by
      funext ω
      exact LatticeProb.GaussConc.SupTail.iSup_eq_iSup_denseSeq (hRc n ω)
        (TopologicalSpace.denseRange_denseSeq I) (hRbdd n ω)
    rw [heq]
    apply Measurable.iSup
    intro k
    let s : ℝ≥0 := (TopologicalSpace.denseSeq I k).1
    have h1 : (u n : ℝ) - min s (u n) ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right s (u n)),
        (sub_le_self _ (min s (u n)).coe_nonneg).trans (by exact_mod_cast hu n)⟩
    have h2 : (v : ℝ) - min s v ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right s v),
        (sub_le_self _ (min s v).coe_nonneg).trans (by exact_mod_cast hv)⟩
    exact (((hGslice _ h1).measurable.comp ((hBm _).measurable.const_add _)).sub
      ((hGslice _ h2).measurable.comp ((hBm _).measurable.const_add _))).abs
  have hDdom : ∀ n, ∀ᵐ ω ∂P, ‖D n ω‖ ≤ 2 * bound ω := by
    intro n
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnonneg n ω)]
    apply ciSup_le
    intro s
    have hs1 : min s.1 (u n) ≤ T := (min_le_left _ _).trans s.property.2
    have hs2 : min s.1 v ≤ T := (min_le_left _ _).trans s.property.2
    have hr1 : (u n : ℝ) - min s.1 (u n) ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right s.1 (u n)),
        (sub_le_self _ (min s.1 (u n)).coe_nonneg).trans (by exact_mod_cast hu n)⟩
    have hr2 : (v : ℝ) - min s.1 v ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast min_le_right s.1 v),
        (sub_le_self _ (min s.1 v).coe_nonneg).trans (by exact_mod_cast hv)⟩
    have h1 := hω _ hr1 _ (hy n) _ hs1
    have h2 := hω _ hr2 _ hz _ hs2
    dsimp only [R]
    rw [Real.norm_eq_abs] at h1 h2
    linarith [abs_sub (G ((u n : ℝ) - min s.1 (u n)) (y n + B (min s.1 (u n)) ω))
      (G ((v : ℝ) - min s.1 v) (z + B (min s.1 v) ω))]
  have hDlim : ∀ ω, Tendsto (fun n => D n ω) atTop (𝓝 0) := by
    intro ω
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδprop⟩ := Sandpile.Support.uniform_clipped_reward_continuity
      T G hG (fun t => B t ω) (hBc ω) K hK (ε / 2) (half_pos hε)
    filter_upwards [(Metric.tendsto_nhds.mp huv) δ hδ, (Metric.tendsto_nhds.mp hyz) δ hδ] with n hnu hny
    have hle : D n ω ≤ ε / 2 := by
      apply ciSup_le
      intro s
      exact (hδprop (u n) (hu n) v hv (y n) (hy n) z hz hnu hny s.1 s.property.2).le
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hDnonneg n ω)]
    exact lt_of_le_of_lt hle (half_lt_self hε)
  have hDi : ∀ n, Integrable (D n) P := fun n =>
    (hint.const_mul 2).mono' (hDm n).aestronglyMeasurable (hDdom n)
  refine ⟨D, hDi, ?_, ?_⟩
  · exact ae_of_all _ fun ω n s hs => hDmajor n ω s hs
  · simpa only [integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun ω => 2 * bound ω)
        (fun n => (hDm n).aestronglyMeasurable) (hint.const_mul 2) hDdom (ae_of_all _ hDlim))
