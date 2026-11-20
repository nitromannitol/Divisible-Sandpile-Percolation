import Sandpile.Support.MeasurableNearOptimalRules
import Sandpile.Support.BrownianContinuationAtStopping
import Sandpile.Support.BrownianSelectedRestart
import Sandpile.Support.BrownianRestartIntegrability
import Sandpile.Support.BrownianValueProcessBound

/-!
# Near-optimal continuation on a compact event

A countably valued Brownian stopping time can be followed by a bounded raw
continuation whose expected reward approximates the value on any compact set
of stopped positions.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- On a compact stopped-position event, a countably valued stopping time
admits a bounded continuation whose expected payoff approximates the value. -/
theorem Sandpile.Support.exists_compact_near_optimal_continuation
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
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞)))
    (hcount : (Set.range τ).Countable) (hτT : ∀ ω, τ ω ≤ T)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) ρ ∧
      (∀ ω, τ ω ≤ ρ ω ∧ ρ ω ≤ T) ∧
      (∫ ω in {ω | B x (τ ω) ω ∈ K}, M (τ ω) ω ∂P) ≤
        (∫ ω in {ω | B x (τ ω) ω ∈ K},
          G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) ∂P) +
        P.real {ω | B x (τ ω) ω ∈ K} * ε := by
  classical
  let I := Set.range τ
  let : Countable I := hcount.to_subtype
  let W := B 0
  let H : I → ℝ≥0 := fun r => T - r.1
  have hrT : ∀ r : I, r.1 ≤ T := by
    rintro ⟨r, ω, rfl⟩
    exact hτT ω
  have hHT : ∀ r, H r ≤ T := fun r => tsub_le_self
  have hGH : ∀ r, ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (H r : ℝ) ×ˢ Set.univ) := fun r => hG.mono (by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (by exact_mod_cast hHT r)⟩, hp.2⟩)
  have hgrowH : ∀ r, ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (H r : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k := by
    intro r
    obtain ⟨C, k, hk⟩ := hgrow
    exact ⟨C, k, fun t ht y => hk t ⟨ht.1, ht.2.trans (by exact_mod_cast hHT r)⟩ y⟩
  have hex : ∀ r : I, ∃ (N : ℕ) (c : ℕ → Sandpile.Continuum.Space d)
      (k : Sandpile.Continuum.Space d → ℕ)
      (θ : ℕ → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0),
      Measurable k ∧ (∀ y, k y ≤ N) ∧
      (∀ n, IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable))
        (fun p => (θ n p : ℝ≥0∞))) ∧
      (∀ n p, θ n p ≤ H r) ∧
      ∀ y ∈ K,
        Sandpile.External.Snell.snellValue (fun t ω => y + W t ω) P G (H r) - ε <
          ∫ ω, G ((H r : ℝ) - θ (k y) (fun t => c (k y) + W t ω))
            (y + W (θ (k y) (fun t => c (k y) + W t ω)) ω) ∂P := fun r =>
    Sandpile.Support.exists_measurable_near_optimal_path_rules
      P W (hB 0) (hBm 0) (hBc 0) (H r) G (hGH r) (hgrowH r) K hK ε hε
  choose N c k θ hkm hkN hθ hθH hnear using hex
  let Y₀ : Ω → Sandpile.Continuum.Space d := fun ω => B x (τ ω) ω
  have hY₀ : Measurable[hτ.measurableSpace] Y₀ :=
    Sandpile.Support.measurable_brownian_stopped_position (B x) (hBm x) (hBc x) τ hτ
  let j : Ω → ℕ := fun ω => k ⟨τ ω, ⟨ω, rfl⟩⟩ (Y₀ ω)
  let label : Ω → I × ℕ := fun ω => (⟨τ ω, ⟨ω, rfl⟩⟩, j ω)
  have hlabel : Measurable[hτ.measurableSpace] label :=
    Sandpile.Support.measurable_stoppingTime_value_and_label
      (LatticeProb.natFiltration (B x) (hBm x)) τ hτ hcount Y₀ hY₀ k hkm
  have hj : Measurable[hτ.measurableSpace] j := measurable_snd.comp hlabel
  let H' : I × ℕ → ℝ≥0 := fun p => H p.1
  let z' : I × ℕ → Sandpile.Continuum.Space d := fun p => c p.1 p.2
  let θ' : I × ℕ → (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0 := fun p => θ p.1 p.2
  let η : Ω → ℝ≥0 := fun ω => θ' (label ω)
    (fun t => z' (label ω) + (B x (τ ω + t) ω - B x (τ ω) ω))
  let ρ : Ω → ℝ≥0 := fun ω => τ ω + η ω
  have hρ := Sandpile.Support.isBrownianStopping_continuation_of_countable_stop
    (B x) (hBm x) T τ hτ hcount hτT j hj c θ hθ hθH
  have hρstop : Sandpile.Continuum.IsBrownianStopping (B x) ρ := hρ.1
  have hρbounds : ∀ ω, τ ω ≤ ρ ω ∧ ρ ω ≤ T := hρ.2
  let E : Set Ω := {ω | Y₀ ω ∈ K}
  have hE : MeasurableSet[hτ.measurableSpace] E := hY₀ hK.isClosed.measurableSet
  have hEm : MeasurableSet E := hτ.measurableSpace_le _ hE
  have hτm : Measurable τ := LatticeProb.measurable_of_isStoppingTime hτ
  obtain ⟨_, _, _, hMint⟩ := Sandpile.Support.exists_integrable_brownian_value_process_bound
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  have hZi : Integrable (fun ω => M (τ ω) ω) (P.restrict E) :=
    (hMint τ hτm hτT).integrableOn
  have hRi : Integrable (fun ω => G ((T : ℝ) - ρ ω) (B x (ρ ω) ω)) P :=
    (Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
      x P (B x) (hB x) (hBm x) (hBc x) T G hG hgrow).1 ρ hρstop (fun ω => (hρbounds ω).2)
  let F : (Sandpile.Continuum.Space d × (I × ℕ)) × LatticeProb.BrownianPath d → ℝ := fun q =>
    G ((H' q.1.2 : ℝ) - θ' q.1.2 (fun t => z' q.1.2 + q.2 t))
      (q.1.1 + q.2 (θ' q.1.2 (fun t => z' q.1.2 + q.2 t)))
  have hF : Measurable F := Sandpile.Support.measurable_selected_continuation_payoff
    T H' (fun p => hHT p.1) G hG z' θ' (fun p => hθ p.1 p.2) (fun p => hθH p.1 p.2)
  let Y : Ω → Sandpile.Continuum.Space d × (I × ℕ) := fun ω => (Y₀ ω, label ω)
  have hY : Measurable[hτ.measurableSpace] Y := hY₀.prodMk hlabel
  have heq : (fun ω => F (Y ω, LatticeProb.restartPath (B x) (hBc x) τ ω)) =
      fun ω => G ((T : ℝ) - ρ ω) (B x (ρ ω) ω) := by
    funext ω
    have htime : (H' (label ω) : ℝ) - η ω = (T : ℝ) - ρ ω := by
      change ((T - τ ω : ℝ≥0) : ℝ) - η ω = (T : ℝ) - (τ ω + η ω : ℝ≥0)
      rw [NNReal.coe_sub (hτT ω), NNReal.coe_add]
      ring
    change G ((H' (label ω) : ℝ) - η ω)
      (B x (τ ω) ω + (B x (τ ω + η ω) ω - B x (τ ω) ω)) = _
    rw [htime]
    congr 1
    dsimp only [ρ]
    abel
  have hFi : Integrable (fun ω => F (Y ω, LatticeProb.restartPath (B x) (hBc x) τ ω))
      (P.restrict E) := by
    rw [heq]
    exact hRi.integrableOn
  have hnear' : ∀ᵐ ω ∂P.restrict E, M (τ ω) ω ≤
      (∫ ω', F (Y ω, (⟨fun t => W t ω', hBc 0 ω'⟩ : LatticeProb.BrownianPath d)) ∂P) + ε := by
    filter_upwards [ae_restrict_mem hEm] with ω hω
    let r : I := ⟨τ ω, ⟨ω, rfl⟩⟩
    let y := Y₀ ω
    have hWshift : Sandpile.Continuum.IsBrownian d y (fun t ω => y + W t ω) P :=
      Sandpile.Support.isBrownian_add_const d P W (hB 0) y
    have hWm : ∀ t, StronglyMeasurable (fun ω => y + W t ω) := fun t =>
      (measurable_const.add (hBm 0 t).measurable).stronglyMeasurable
    have hWc : ∀ ω, Continuous fun t => y + W t ω := fun ω => continuous_const.add (hBc 0 ω)
    have hval := Sandpile.Support.snellValue_eq_of_isBrownian y P P (B y)
      (fun t ω => y + W t ω) (hB y) hWshift (hBm y) hWm (hBc y) hWc
      (H r) G (hGH r) (hgrowH r)
    have hM := hMval (τ ω) (hτT ω) ω
    have htime : ((T : ℝ) - τ ω) = (H r : ℝ) := (NNReal.coe_sub (hτT ω)).symm
    rw [htime, hval] at hM
    have hn := hnear r y hω
    change Sandpile.External.Snell.snellValue (fun t ω => y + W t ω) P G (H r) - ε <
      (∫ ω', F (Y ω, (⟨fun t => W t ω', hBc 0 ω'⟩ : LatticeProb.BrownianPath d)) ∂P) at hn
    linarith
  have hcomp := Sandpile.Support.setIntegral_le_brownian_restart_add
    P P x (B x) W (hB x) (hB 0) (hBm x) (hBm 0) (hBc x) (hBc 0)
    τ hτ E hE Y hY F hF hFi (fun ω => M (τ ω) ω) hZi ε hnear'
  rw [heq] at hcomp
  exact ⟨ρ, hρstop, hρbounds, hcomp⟩
