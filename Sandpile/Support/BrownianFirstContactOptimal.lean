import Sandpile.Support.BrownianApproxContactOptimality
import Sandpile.Support.ContinuousApproxContact
import Sandpile.Support.StoppedProcessConvergence

/-!
# Optimality of Brownian first contact

Approximate contacts preserve the expected value, and continuity with an
integrable envelope passes this equality to the first exact contact.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The first raw contact of the Brownian value process with the reward is
optimal. -/
theorem Sandpile.Support.brownian_first_contact_optimal
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMad : StronglyAdapted (LatticeProb.natFiltration (B x) (hBm x)) M)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (hMdom : ∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω)
    (τ : Ω → ℝ≥0)
    (hfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
      M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) :
    (∫ ω, G ((T : ℝ) - τ ω) (B x (τ ω) ω) ∂P) =
      Sandpile.External.Snell.snellValue (B x) P G T := by
  let 𝓕 := LatticeProb.natFiltration (B x) (hBm x)
  let R : ℝ≥0 → Ω → ℝ := fun s ω => G ((T : ℝ) - min s T) (B x (min s T) ω)
  have hRad : StronglyAdapted 𝓕 R := by
    intro s
    let r := min s T
    have hrT : r ≤ T := min_le_right _ _
    have hrs : r ≤ s := min_le_left _ _
    have hslice : Continuous (G ((T : ℝ) - r)) := by
      change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
        fun y => ((T : ℝ) - r, y))
      apply hG.comp_continuous
      · exact continuous_const.prodMk continuous_id
      · intro y
        exact ⟨⟨sub_nonneg.mpr (by exact_mod_cast hrT), sub_le_self _ r.coe_nonneg⟩, Set.mem_univ y⟩
    have hBad : StronglyMeasurable[𝓕 r] (B x r) :=
      (Sandpile.Continuum.measurable_brownianFiltration (B x) r r le_rfl).stronglyMeasurable
    exact (hslice.comp_stronglyMeasurable hBad).mono (𝓕.mono hrs)
  have hRc : ∀ ω, Continuous fun s => R s ω := by
    intro ω
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun s : ℝ≥0 => ((T : ℝ) - min s T, B x (min s T) ω))
    apply hG.comp_continuous
    · exact ((continuous_const.sub (continuous_subtype_val.comp (continuous_id.min continuous_const))).prodMk
        ((hBc x ω).comp (continuous_id.min continuous_const)))
    · intro s
      exact ⟨⟨sub_nonneg.mpr (by exact_mod_cast min_le_right s T),
        sub_le_self _ (min s T).coe_nonneg⟩, Set.mem_univ _⟩
  have hRT : ∀ ω, M T ω = R T ω := by
    intro ω
    rw [hMval T le_rfl ω]
    simp only [R, min_self, sub_self]
    exact Sandpile.External.Snell.snellValue_zero P (B (B x T ω)) (B x T ω)
      (hB (B x T ω)).start G
  have hdom : ∀ ω s, s ≤ T → R s ω ≤ M s ω := by
    intro ω s hs
    simpa only [R, min_eq_left hs] using hMdom s hs ω
  let X : ℝ≥0 → Ω → ℝ := fun s ω => M s ω - R s ω
  have hXad : StronglyAdapted 𝓕 X := hMad.sub hRad
  have hXc : ∀ ω, Continuous fun s => X s ω := fun ω => (hMc ω).sub (hRc ω)
  have hXnonneg : ∀ ω s, s ≤ T → 0 ≤ X s ω := fun ω s hs => sub_nonneg.mpr (hdom ω s hs)
  have hXT : ∀ ω, X T ω = 0 := fun ω => sub_eq_zero.mpr (hRT ω)
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hεmono : Antitone ε := by
    apply antitone_nat_of_succ_le
    intro n
    dsimp [ε]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    push_cast
    linarith
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨τ', σ, hτfirst, hτstop, hσfirst, hσstop, _, _, hσlim⟩ :=
    Sandpile.Support.exists_first_le_stoppingTime_tendsto X hXad hXc T hXnonneg hXT
      ε (fun n => (hεpos n).le) hεmono hεlim
  have hτ'eq : ∀ ω, τ' ω = τ ω := by
    intro ω
    have he : {s : ℝ≥0 | s ≤ T ∧ X s ω = 0} =
        {s : ℝ≥0 | s ≤ T ∧ M s ω = G ((T : ℝ) - s) (B x s ω)} := by
      ext s
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro hs
      simp only [X, R, min_eq_left hs, sub_eq_zero]
    exact (he ▸ hτfirst ω).unique (hfirst ω)
  have hσeq : ∀ n, (∫ ω, M (σ n ω) ω ∂P) =
      Sandpile.External.Snell.snellValue (B x) P G T := by
    intro n
    apply Sandpile.Support.brownian_value_integral_eq_at_approx_contact
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval hMdom (σ n) (hσstop n) (ε n) (hεpos n)
    intro ω
    have he : {s : ℝ≥0 | s ≤ T ∧ X s ω ≤ ε n} =
        {s : ℝ≥0 | s ≤ T ∧ M s ω - G ((T : ℝ) - s) (B x s ω) ≤ ε n} := by
      ext s
      simp only [Set.mem_ofPred_eq, and_congr_right_iff]
      intro hs
      simp only [X, R, min_eq_left hs]
    exact he ▸ hσfirst n ω
  have hτm : Measurable τ' := LatticeProb.measurable_of_isStoppingTime hτstop
  have hσm : ∀ n, Measurable (σ n) := fun n => LatticeProb.measurable_of_isStoppingTime (hσstop n)
  obtain ⟨D, hDi, hD, _⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  have hτT : ∀ ω, τ' ω ≤ T := fun ω => (hτfirst ω).1.1
  have hσT : ∀ n ω, σ n ω ≤ T := fun n ω => (hσfirst n ω).1.1
  have hlim := (Sandpile.Support.tendsto_integral_stopped_process P M
    (fun s => (hMm s).stronglyMeasurable) hMc T D hDi hD σ τ' hσm hτm hσT hτT
    (ae_of_all P hσlim)).2
  have hvalue : (∫ ω, M (τ' ω) ω ∂P) = Sandpile.External.Snell.snellValue (B x) P G T := by
    apply tendsto_nhds_unique hlim
    simpa only [hσeq] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => Sandpile.External.Snell.snellValue (B x) P G T) atTop
      (𝓝 (Sandpile.External.Snell.snellValue (B x) P G T)))
  calc
    _ = ∫ ω, M (τ' ω) ω ∂P := by
      apply integral_congr_ae
      exact ae_of_all P fun ω => by
        change G ((T : ℝ) - τ ω) (B x (τ ω) ω) = M (τ' ω) ω
        rw [hτ'eq ω]
        exact (hfirst ω).1.2.symm
    _ = _ := hvalue
