/-
Regularity of the cube value in its starting point.

The coupling lemma `eventually_measure_bad_d23_block_lt_of_fdd` demands two things
of the Brownian cube value that nothing in the repository supplies: measurability
in the sample point at each starting point, in the strong form rather than almost
everywhere, and continuity in the starting point.  The ball value has both in
some form; the cube value has neither.

Both come from the same place.  A Brownian motion started at `y` is the motion
started at the origin shifted by `y`, so the stopping classes at the two starting
points correspond, and the value differs by the shift.  Continuity is then the
Lipschitz estimate already proved for the discounted cube reward, and
measurability follows from an everywhere-continuous, everywhere-measurable
version of the driving field.
-/
import Sandpile.Support.D23NormalizedTransfer
import Sandpile.Support.LimWhiteNoiseInstance

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The motion shifted by its starting point -/

/-- A Brownian motion started at the origin, shifted by `y`, is a Brownian motion started at
`y`. -/
theorem isBrownian_add_const {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ) (PB : Measure ΩB)
    (B : ℝ≥0 → ΩB → Space d) (hB : IsBrownian d 0 B PB) (y : Space d) :
    IsBrownian d y (fun t ω => y + B t ω) PB where
  start := by
    filter_upwards [hB.start] with ω hω
    simp [hω]
  coord := fun i => by
    have heq : (fun (t : ℝ≥0) (ω : ΩB) => Real.sqrt d * ((y + B t ω) i - y i))
        = fun t ω => Real.sqrt d * (B t ω i - (0 : Space d) i) := by
      funext t ω
      simp
    rw [heq]
    exact hB.coord i
  indep := by
    have hg : ∀ i : Fin d, Measurable (fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 => y i + p s) := fun i =>
      measurable_pi_lambda _ fun s =>
        ((measurable_pi_apply s : Measurable fun p : ℝ≥0 → ℝ => p s).const_add (y i))
    have h := hB.indep.comp (fun i : Fin d => fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 => y i + p s) hg
    have heq : (fun (i : Fin d) (ω : ΩB) => fun t : ℝ≥0 => (y + B t ω) i)
        = fun (i : Fin d) => (fun p : ℝ≥0 → ℝ => fun s : ℝ≥0 => y i + p s) ∘
            (fun (ω : ΩB) => fun t : ℝ≥0 => B t ω i) := by
      funext i ω
      funext s
      simp
    rw [heq]
    exact h

/-- Shifting the motion by a constant does not change its natural stopping class. -/
theorem isBrownianStopping_add_const {ΩB : Type*} {d : ℕ} (y : Space d)
    (B : ℝ≥0 → ΩB → Space d) (τ : ΩB → ℝ≥0) :
    IsBrownianStopping (fun t ω => y + B t ω) τ ↔ IsBrownianStopping B τ := by
  have key : ∀ (y : Space d) (B : ℝ≥0 → ΩB → Space d) (τ : ΩB → ℝ≥0),
      IsBrownianStopping B τ → IsBrownianStopping (fun t ω => y + B t ω) τ := by
    intro y B τ hτ t
    have hle : brownianFiltration B t ≤ brownianFiltration (fun t ω => y + B t ω) t := by
      refine brownianFiltration_le B t _ fun s hs => ?_
      have hm := (measurable_brownianFiltration (fun t ω => y + B t ω) s t hs).sub_const y
      convert hm using 1
      funext ω
      simp
    exact hle _ (hτ t)
  refine ⟨fun h => ?_, key y B τ⟩
  simpa using key (-y) _ τ h

/-- The cube payoffs of the shifted motion, about the starting point, are the cube payoffs of
the unshifted motion, about the origin, for the shifted reward. -/
theorem cubeStoppingPayoffs_add_const {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (P : Measure ΩB)
    (B : ℝ≥0 → ΩB → Space d) (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) :
    cubeStoppingPayoffs (fun t ω => u + B t ω) P h T L u =
      cubeStoppingPayoffs B P (fun t y => h t (u + y)) T L 0 := by
  ext a
  simp only [cubeStoppingPayoffs, Set.mem_setOf_eq, isBrownianStopping_add_const,
    PiLp.add_apply, add_sub_cancel_left, PiLp.zero_apply, sub_zero]

theorem brownianValueCube_add_const {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (P : Measure ΩB)
    (B : ℝ≥0 → ΩB → Space d) (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) :
    brownianValueCube (fun t ω => u + B t ω) P h T L u =
      h T u + brownianDiscountCube B P (fun t y => h t (u + y)) T L 0 := by
  rw [brownianValueCube_eq, brownianDiscountCube_eq_sSup, brownianDiscountCube_eq_sSup,
    cubeStoppingPayoffs_add_const]

/-! ### The killing cube is compact -/

/-- The closed cube of half-width `L` about `c` is compact. -/
theorem isCompact_cube (d : ℕ) (c : Space d) (L : ℝ) :
    IsCompact {y : Space d | ∀ i, |y i - c i| ≤ L} := by
  have h : {y : Space d | ∀ i, |y i - c i| ≤ L} =
      (EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' Set.pi Set.univ (fun i => Set.Icc (c i - L) (c i + L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, abs_le]
    refine forall_congr' fun i => ?_
    rw [show (EuclideanSpace.equiv (Fin d) ℝ) y i = y i from rfl]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [h]
  exact (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph.isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The time strip over the killing cube is compact. -/
theorem isCompact_strip_cube (d : ℕ) (c : Space d) (T L : ℝ) :
    IsCompact (Set.Icc (0 : ℝ) T ×ˢ {y : Space d | ∀ i, |y i - c i| ≤ L}) :=
  isCompact_Icc.prod (isCompact_cube d c L)

/-- The cube discount of the motion from the origin is continuous in the shift of the reward:
the discounted cube reward is 1-Lipschitz in the reward, uniformly over the compact strip over
the cube, on which a continuous reward is uniformly continuous in the shift. -/
theorem continuous_brownianDiscountCube_shift
    {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Space d) (hB : IsBrownian d 0 B PB)
    (Z : ℝ → Space d → ℝ) (hZ : Continuous fun q : ℝ × Space d => Z q.1 q.2)
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    Continuous fun u : Space d => brownianDiscountCube B PB (fun t y => Z t (u + y)) T L 0 := by
  rw [continuous_iff_continuousAt]
  intro u0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hK := isCompact_strip_cube d (0 : Space d) T L
  have hcont : ∀ u : Space d, Continuous fun q : ℝ × Space d => Z q.1 (u + q.2) := fun u =>
    hZ.comp (continuous_fst.prodMk (continuous_const.add continuous_snd))
  have hjoint : Continuous (Function.uncurry
      fun (u : Space d) (q : ℝ × Space d) => Z q.1 (u + q.2)) :=
    hZ.comp (continuous_snd.fst.prodMk (continuous_fst.add continuous_snd.snd))
  obtain ⟨v, hv, hvε⟩ := hK.mem_uniformity_of_prod
    (f := fun (u : Space d) (q : ℝ × Space d) => Z q.1 (u + q.2)) (s := Set.univ) (q := u0)
    (u := {p : ℝ × ℝ | dist p.1 p.2 < ε / 2}) hjoint.continuousOn (Set.mem_univ _)
    (Metric.dist_mem_uniformity (half_pos hε))
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with u hu
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont u).continuousOn
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn (hcont u0).continuousOn
  have hlip := abs_brownianDiscountCube_sub_le_of_continuousOn hB
    (fun t y => Z t (u + y)) (fun t y => Z t (u0 + y)) T L M N (ε / 2) hT hL
    (hcont u).continuousOn (hcont u0).continuousOn
    (fun s hs y hy => by
      simpa only [Real.norm_eq_abs] using hM (s, y) ⟨hs, hy⟩)
    (fun s hs y hy => by
      simpa only [Real.norm_eq_abs] using hN (s, y) ⟨hs, hy⟩)
    (fun s hs y hy => by
      have h := hvε u hu (s, y) ⟨hs, hy⟩
      simpa only [Set.mem_setOf_eq, Real.dist_eq] using h.le)
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hlip (half_lt_self hε)

/-- The cube discount is measurable in the sample point of the driving field, for a continuous
field measurable at each time and place.  The discount is 1-Lipschitz for the sup norm of the
reward over the compact strip over the cube, so it is the infimum over a countable dense set of
rewards of a constant plus the sup-norm distance to that reward; and the sup-norm distance to a
fixed reward is a countable supremum over a dense set of the strip. -/
theorem measurable_brownianDiscountCube_sample
    {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Space d) (u : Space d) (hB : IsBrownian d u B PB)
    {ΩW : Type*} [MeasurableSpace ΩW]
    (Z : ΩW → ℝ → Space d → ℝ) (hZm : ∀ t x, Measurable fun ω => Z ω t x)
    (hZ : ∀ ω, Continuous fun q : ℝ × Space d => Z ω q.1 q.2)
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L) :
    Measurable fun ω => brownianDiscountCube B PB (Z ω) T L u := by
  classical
  let K : Set (ℝ × Space d) := Set.Icc 0 T ×ˢ {y : Space d | ∀ i, |y i - u i| ≤ L}
  have hKc : IsCompact K := isCompact_strip_cube d u T L
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let r : ΩW → C(K, ℝ) := fun ω => ⟨fun q => Z ω q.1.1 q.1.2, (hZ ω).comp continuous_subtype_val⟩
  let D : ΩW → ℝ := fun ω => brownianDiscountCube B PB (Z ω) T L u
  have hr : ∀ ω (q : K), r ω q = Z ω q.1.1 q.1.2 := fun _ _ => rfl
  have hlip : ∀ ω ω', |D ω - D ω'| ≤ ‖r ω - r ω'‖ := by
    intro ω ω'
    refine abs_brownianDiscountCube_sub_le_of_continuousOn hB (Z ω) (Z ω') T L ‖r ω‖ ‖r ω'‖
      ‖r ω - r ω'‖ hT hL (hZ ω).continuousOn (hZ ω').continuousOn ?_ ?_ ?_
    · intro s hs y hy
      simpa only [hr, Real.norm_eq_abs] using (r ω).norm_coe_le_norm ⟨(s, y), ⟨hs, hy⟩⟩
    · intro s hs y hy
      simpa only [hr, Real.norm_eq_abs] using (r ω').norm_coe_le_norm ⟨(s, y), ⟨hs, hy⟩⟩
    · intro s hs y hy
      simpa only [ContinuousMap.sub_apply, hr, Real.norm_eq_abs] using
        (r ω - r ω').norm_coe_le_norm ⟨(s, y), ⟨hs, hy⟩⟩
  show Measurable D
  rcases isEmpty_or_nonempty ΩW with hΩ | hΩ
  · intro s _
    rw [Set.eq_empty_of_isEmpty (D ⁻¹' s)]
    exact MeasurableSet.empty
  have hKne : Nonempty K := ⟨⟨(0, u), ⟨left_mem_Icc.2 hT, fun i => by simpa using hL⟩⟩⟩
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq K
  have hnormF : ∀ F : C(K, ℝ), ‖F‖ = ⨆ n, ‖F (q n)‖ := by
    intro F
    have hbdd : BddAbove (Set.range fun n => ‖F (q n)‖) :=
      ⟨‖F‖, by rintro _ ⟨n, rfl⟩; exact F.norm_coe_le_norm _⟩
    refine le_antisymm ?_ (ciSup_le fun n => F.norm_coe_le_norm _)
    rw [ContinuousMap.norm_le _ (Real.iSup_nonneg fun _ => norm_nonneg _)]
    intro x
    exact hq.induction_on x (isClosed_le F.continuous.norm continuous_const)
      (fun n => le_ciSup hbdd n)
  have hnorm : ∀ g : C(K, ℝ), Measurable fun ω => ‖r ω - g‖ := by
    intro g
    have h : (fun ω => ‖r ω - g‖) = fun ω => ⨆ n, ‖Z ω (q n).1.1 (q n).1.2 - g (q n)‖ := by
      funext ω
      rw [hnormF]
      simp only [ContinuousMap.sub_apply, hr]
    rw [h]
    exact Measurable.iSup fun n => ((hZm _ _).sub_const _).norm
  obtain ⟨t, hts, htc, hdense⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace (Set.range r)).exists_countable_dense_subset
  haveI : Countable t := htc.to_subtype
  obtain ⟨ω₀⟩ := hΩ
  haveI : Nonempty t := by
    obtain ⟨g, hg, -⟩ := Metric.mem_closure_iff.1 (hdense ⟨ω₀, rfl⟩) 1 one_pos
    exact ⟨⟨g, hg⟩⟩
  choose ω' hω' using fun g : t => hts g.2
  have hform : ∀ ω, D ω = ⨅ g : t, (D (ω' g) + ‖r ω - g.1‖) := by
    intro ω
    have hlow : ∀ g : t, D ω ≤ D (ω' g) + ‖r ω - g.1‖ := by
      intro g
      have h := hlip ω (ω' g)
      rw [hω' g] at h
      linarith [(abs_le.1 h).2]
    have hb : BddBelow (Set.range fun g : t => D (ω' g) + ‖r ω - g.1‖) :=
      ⟨D ω, by rintro _ ⟨g, rfl⟩; exact hlow g⟩
    refine le_antisymm (le_ciInf hlow) (le_of_forall_pos_le_add fun ε hε => ?_)
    obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.1 (hdense ⟨ω, rfl⟩) (ε / 2) (half_pos hε)
    have h1 := hlip ω (ω' ⟨g, hg⟩)
    have hω'g : r (ω' ⟨g, hg⟩) = g := hω' ⟨g, hg⟩
    rw [hω'g] at h1
    have h2 : ‖r ω - g‖ < ε / 2 := by rwa [dist_eq_norm] at hd
    have h3 := (abs_le.1 h1).1
    calc ⨅ g : t, (D (ω' g) + ‖r ω - g.1‖) ≤ D (ω' ⟨g, hg⟩) + ‖r ω - g‖ := ciInf_le hb ⟨g, hg⟩
      _ ≤ D ω + ε := by linarith
  have hD : D = fun ω => ⨅ g : t, (D (ω' g) + ‖r ω - g.1‖) := funext hform
  rw [hD]
  exact Measurable.iInf fun g => (hnorm g.1).const_add _

/-! ### A cube of negative half-width -/

/-- With no coordinate the cube condition is vacuous, so every half-width gives the same
attainable set. -/
theorem cubeStoppingPayoffs_of_dim_zero {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (hd : d = 0)
    (P : Measure ΩB) (B : ℝ≥0 → ΩB → Space d) (h : ℝ → Space d → ℝ) (T L L' : ℝ)
    (c : Space d) :
    cubeStoppingPayoffs B P h T L c = cubeStoppingPayoffs B P h T L' c := by
  subst hd
  ext a
  simp only [cubeStoppingPayoffs, Set.mem_setOf_eq, IsEmpty.forall_iff, implies_true]

/-- A cube of negative half-width is empty, so only `τ = 0` is admissible and the discount is
`-h(T, x)` for a motion started at `x`. -/
theorem brownianDiscountCube_of_neg {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    (P : Measure ΩB) [IsProbabilityMeasure P] (B : ℝ≥0 → ΩB → Space d) (h : ℝ → Space d → ℝ)
    (T L : ℝ) (hT : 0 ≤ T) (hL : L < 0) (c x : Space d) (hstart : ∀ᵐ ω ∂P, B 0 ω = x) :
    brownianDiscountCube B P h T L c = -h T x := by
  have hint : (∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P) = -h T x := by
    have hcongr : (∫ ω, -h (T - ((0 : ℝ≥0) : ℝ)) (B 0 ω) ∂P) = ∫ _ω : ΩB, -h T x ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hstart] with ω hω
      rw [hω]
      norm_num
    rw [hcongr, integral_const]
    simp
  have hset : cubeStoppingPayoffs B P h T L c = {-h T x} := by
    ext a
    constructor
    · rintro ⟨τ, -, -, hcube, rfl⟩
      have hτ0 : ∀ᵐ ω ∂P, τ ω = 0 := by
        filter_upwards [hcube] with ω hω
        by_contra hne
        have h1 := hω 0 (pos_iff_ne_zero.2 hne) ⟨0, hd⟩
        have h2 := abs_nonneg (B 0 ω ⟨0, hd⟩ - c ⟨0, hd⟩)
        linarith
      have hcongr : (∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P) = ∫ _ω : ΩB, -h T x ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hτ0, hstart] with ω h0 hs
        rw [h0, hs]
        norm_num
      rw [hcongr, integral_const]
      simp
    · intro ha
      rw [Set.mem_singleton_iff] at ha
      exact ⟨fun _ => 0, isBrownianStopping_const B 0, fun ω => by simpa using hT,
        Filter.Eventually.of_forall (fun ω s hs => absurd hs (by simp)), by rw [ha, hint]⟩
  rw [brownianDiscountCube_eq_sSup, hset, csSup_singleton]

/-- **The first statement above is false.**  For the constant motion on a one-point space, `d = 1`,
`Z t x = t`, `T = L = 1`, the cube value is `1` while the centre `u` is within the cube about the
frozen position `0`, and `0` as soon as `|u| > 1`: no stopping time may run once the frozen
position has left the cube, so only `τ = 0` is admissible.  With `B` unrelated to `u`, the cube
value of an arbitrary motion is discontinuous in the centre. -/
theorem not_continuous_brownianValueCube_startingPoint :
    ¬ ∀ (d : ℕ) {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d) (Z : ℝ → Sandpile.Continuum.Space d → ℝ),
        (Continuous fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2) → ∀ (T L : ℝ), 0 < T →
        Continuous fun u : Sandpile.Continuum.Space d =>
          Sandpile.Continuum.brownianValueCube B PB Z T L u := by
  intro H
  let B : ℝ≥0 → Unit → Space 1 := fun _ _ => 0
  let PB : Measure Unit := Measure.dirac ()
  let Z : ℝ → Space 1 → ℝ := fun t _ => t
  have hc : Continuous fun u : Space 1 => brownianValueCube B PB Z 1 1 u :=
    @H 1 Unit inferInstance PB inferInstance B Z continuous_fst 1 1 one_pos
  let v : ℝ → Space 1 := fun s => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => s)
  have hv : Continuous v :=
    (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.comp (continuous_pi fun _ => continuous_id)
  have hvs : ∀ s (i : Fin 1), v s i = s := fun _ _ => rfl
  have hval1 : ∀ s : ℝ, |s| ≤ 1 → brownianValueCube B PB Z 1 1 (v s) = 1 := by
    intro s hs
    rw [brownianValueCube_eq, brownianDiscountCube_eq_sSup]
    have h0 : sSup (cubeStoppingPayoffs B PB Z 1 1 (v s)) = 0 := by
      refine IsGreatest.csSup_eq ⟨?_, ?_⟩
      · refine ⟨fun _ => 1, isBrownianStopping_const _ 1, fun _ => by simp, ?_, ?_⟩
        · exact Filter.Eventually.of_forall fun ω t ht i => by simpa [B, hvs] using hs
        · simp [PB, Z]
      · rintro a ⟨τ, -, hτ, -, rfl⟩
        have h1 := hτ ()
        simp only [PB, Z, integral_dirac]
        linarith
    rw [h0]
    simp [Z]
  have hval0 : ∀ s : ℝ, 1 < |s| → brownianValueCube B PB Z 1 1 (v s) = 0 := by
    intro s hs
    rw [brownianValueCube_eq, brownianDiscountCube_eq_sSup]
    have hset : cubeStoppingPayoffs B PB Z 1 1 (v s) = {-1} := by
      ext a
      constructor
      · rintro ⟨τ, -, hτ, hcube, rfl⟩
        have hτ0 : τ () = 0 := by
          by_contra hne
          simp only [PB, ae_dirac_eq, Filter.eventually_pure] at hcube
          have h1 := hcube 0 (pos_iff_ne_zero.2 hne) 0
          simp only [B, hvs, PiLp.zero_apply, zero_sub, abs_neg] at h1
          linarith
        simp only [PB, Z, integral_dirac, hτ0]
        simp
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        refine ⟨fun _ => 0, isBrownianStopping_const _ 0, fun _ => by simp,
          Filter.Eventually.of_forall fun ω t ht => absurd ht (by simp), ?_⟩
        rw [ha]
        simp [PB, Z]
    rw [hset, csSup_singleton]
    simp [Z]
  have hg : Continuous fun s : ℝ => brownianValueCube B PB Z 1 1 (v s) := hc.comp hv
  have h0 : brownianValueCube B PB Z 1 1 (v 0) = 1 := hval1 0 (by simp)
  have h2 : brownianValueCube B PB Z 1 1 (v 2) = 0 := hval0 2 (by norm_num)
  obtain ⟨s, hs⟩ := intermediate_value_univ 2 0 hg
    (show (1 / 2 : ℝ) ∈ Set.Icc (brownianValueCube B PB Z 1 1 (v 2))
      (brownianValueCube B PB Z 1 1 (v 0)) by rw [h0, h2]; constructor <;> norm_num)
  have hs' : brownianValueCube B PB Z 1 1 (v s) = 1 / 2 := hs
  by_cases hs1 : |s| ≤ 1
  · rw [hval1 s hs1] at hs'
    norm_num at hs'
  · rw [hval0 s (not_le.1 hs1)] at hs'
    norm_num at hs'

/-- **The cube value is continuous in its starting point.**  Here the starting point moves the
motion together with the cube: the motion started at `u` is the motion started at the origin,
shifted by `u`. -/
theorem continuous_brownianValueCube_shifted_startingPoint
    (d : ℕ) {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : IsBrownian d 0 B PB)
    (Z : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hZ : Continuous fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2)
    (T L : ℝ) (hT : 0 < T) :
    Continuous fun u : Sandpile.Continuum.Space d =>
      Sandpile.Continuum.brownianValueCube (fun t ω => u + B t ω) PB Z T L u := by
  have main : ∀ L' : ℝ, 0 ≤ L' → Continuous fun u : Space d =>
      brownianValueCube (fun t ω => u + B t ω) PB Z T L' u := by
    intro L' hL'
    have h : (fun u : Space d => brownianValueCube (fun t ω => u + B t ω) PB Z T L' u) =
        fun u => Z T u + brownianDiscountCube B PB (fun t y => Z t (u + y)) T L' 0 :=
      funext fun u => brownianValueCube_add_const PB B Z T L' u
    rw [h]
    exact (hZ.comp (continuous_const.prodMk continuous_id)).add
      (continuous_brownianDiscountCube_shift PB B hB Z hZ T L' hT.le hL')
  by_cases hL : 0 ≤ L
  · exact main L hL
  replace hL := not_le.1 hL
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have h0 : ∀ u : Space d, brownianValueCube (fun t ω => u + B t ω) PB Z T L u =
        brownianValueCube (fun t ω => u + B t ω) PB Z T 0 u := fun u => by
      rw [brownianValueCube_eq, brownianValueCube_eq, brownianDiscountCube_eq_sSup,
        brownianDiscountCube_eq_sSup, cubeStoppingPayoffs_of_dim_zero hd PB _ Z T L 0 u]
    simp_rw [h0]
    exact main 0 le_rfl
  · have h0 : ∀ u : Space d, brownianValueCube (fun t ω => u + B t ω) PB Z T L u = 0 :=
      fun u => by
        rw [brownianValueCube_eq, brownianDiscountCube_of_neg hd PB _ Z T L hT.le hL u u
          (by filter_upwards [hB.start] with ω hω; simp [hω])]
        ring
    simp_rw [h0]
    exact continuous_const

/-- The family form of `continuous_brownianValueCube_shifted_startingPoint`, in the shape
`u ↦ brownianValueCube (B u) PB Z T L u` in which the coupling lemma consumes it: a family of
motions in which the motion started at `y` is the motion started at the origin shifted by `y`.
Such a family is Brownian at every starting point by `isBrownian_add_const`. -/
theorem continuous_brownianValueCube_family
    (d : ℕ) {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : IsBrownian d 0 (B 0) PB) (hshift : ∀ y t ω, B y t ω = y + B 0 t ω)
    (Z : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hZ : Continuous fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2)
    (T L : ℝ) (hT : 0 < T) :
    Continuous fun u : Sandpile.Continuum.Space d =>
      Sandpile.Continuum.brownianValueCube (B u) PB Z T L u := by
  have h : (fun u : Space d => brownianValueCube (B u) PB Z T L u) =
      fun u => brownianValueCube (fun t ω => u + B 0 t ω) PB Z T L u := funext fun u => by
    rw [show B u = fun t ω => u + B 0 t ω from
      funext fun t => funext fun ω => hshift u t ω]
  rw [h]
  exact continuous_brownianValueCube_shifted_startingPoint d PB (B 0) hB Z hZ T L hT

/-- **The cube value is measurable in the sample point.**  The motion is a Brownian motion
started at the centre `u` of the cube, as in the coupling lemma. -/
theorem measurable_brownianValueCube_sample_of_isBrownian
    (d : ℕ) {ΩB : Type} [MeasurableSpace ΩB] (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    {ΩW : Type} [MeasurableSpace ΩW]
    (Z : ΩW → ℝ → Sandpile.Continuum.Space d → ℝ)
    (hZm : ∀ t x, Measurable fun ω => Z ω t x)
    (hZ : ∀ ω, Continuous fun q : ℝ × Sandpile.Continuum.Space d => Z ω q.1 q.2)
    (T L : ℝ) (hT : 0 < T) (u : Sandpile.Continuum.Space d)
    (hB : IsBrownian d u B PB) :
    Measurable fun ω => Sandpile.Continuum.brownianValueCube B PB (Z ω) T L u := by
  have hdisc : ∀ L' : ℝ, 0 ≤ L' →
      Measurable fun ω => brownianDiscountCube B PB (Z ω) T L' u := fun L' hL' =>
    measurable_brownianDiscountCube_sample PB B u hB Z hZm hZ T L' hT.le hL'
  by_cases hL : 0 ≤ L
  · exact (hZm T u).add (hdisc L hL)
  replace hL := not_le.1 hL
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have h0 : ∀ ω, brownianValueCube B PB (Z ω) T L u =
        brownianValueCube B PB (Z ω) T 0 u := fun ω => by
      rw [brownianValueCube_eq, brownianValueCube_eq, brownianDiscountCube_eq_sSup,
        brownianDiscountCube_eq_sSup, cubeStoppingPayoffs_of_dim_zero hd PB B _ T L 0 u]
    simp_rw [h0]
    exact (hZm T u).add (hdisc 0 le_rfl)
  · have h0 : ∀ ω, brownianValueCube B PB (Z ω) T L u = 0 := fun ω => by
      rw [brownianValueCube_eq, brownianDiscountCube_of_neg hd PB B _ T L hT.le hL u u hB.start]
      ring
    simp_rw [h0]
    exact measurable_const

end Sandpile.Support
