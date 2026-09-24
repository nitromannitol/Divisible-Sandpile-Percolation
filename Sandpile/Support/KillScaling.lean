/-
The cube-killed scaling limit for centered scenery in dimensions at most three.
Finite-dimensional convergence and equicontinuity couple the heat potentials on
a compact cylinder. A finite family of cutoff rewards gives a uniform stopping
stability threshold, and both killed cutoff errors vanish. The remaining mesh
and stopping errors yield uniform convergence in probability on compact sets.
-/
import Sandpile.Support.KillFieldCoupling
import Sandpile.Support.KillValueStability
import Sandpile.Support.KillMeshApproximation
import Sandpile.Support.KillAssembly
import Sandpile.Support.KillRadius
import Sandpile.Support.ExplRewardFamily
import Sandpile.Frozen.HeatPotentialInvariance

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile Sandpile.Continuum

theorem Sandpile.dlt4_killed_scaling_of_inputs
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (hZcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d =>
      Sandpile.Continuum.gaussianPotential d (variance id ν) W q.1 q.2 ω)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.localizedOdometer (Sandpile.supBox (fun i => ⌊R * u i⌋) R)
                    (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValueCube (B u) PB
                    (fun t y => Sandpile.Continuum.gaussianPotential d (variance id ν) W t y p.2)
                    T 1 u|}
          ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨hfdd, htight⟩ := Sandpile.Frozen.heat_potential_invariance hLocalCLT d (by omega) hd3
    ν hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T hT
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hKn : ∀ u ∈ K, ‖u‖ ≤ ρ := fun u hu => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKρ hu
  let A : ℝ := ρ + 3 * Real.sqrt d + 1
  have hA : 0 < A := by dsimp [A]; positivity
  let C := rewardBox d T A
  have hCc : IsCompact C := isCompact_rewardBox d T A
  have hCs : C ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  let η : ℝ := ε / 16
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨M₀, hM₀⟩ := (htight C hCc hCs).1 (δ / 3) hδ3
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨a, ha, hosc⟩ := (htight C hCc hCs).2 (δ / 3) η hδ3 hη
  obtain ⟨N, G, hGc, hGM, hnear⟩ := exists_cutoff_reward_family d A T hA M η a hM hη ha
  obtain ⟨Rs, hRs, hstab⟩ := Sandpile.killed_stability_gap_of_two_rewards hStab d hd ΩB PB B hB
    T hT K hK N (fun i s y => -G i s y) (fun i => (hGc i).neg) (M + η)
    (fun i s y => by simpa only [abs_neg] using hGM i s y)
    (ε / 4) (2 * η) (3 * η) (by positivity)
  obtain ⟨Rm, hRm, hmesh⟩ := Sandpile.exists_parabolic_mesh_threshold d a ha
  obtain ⟨Rc, hRc, hcoup⟩ := Sandpile.Continuum.heat_field_coupling d hd ν ΩW PW W hW T hT
    hZcont hfdd htight C hCc hCs η (δ / 3) hη hδ3
  refine ⟨max 1 (max Rs (max Rm Rc)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRrest : max Rs (max Rm Rc) ≤ R := (le_max_right _ _).trans hR
  have hRsm : Rs ≤ R := (le_max_left _ _).trans hRrest
  have hRmm : Rm ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hRrest)
  have hRcm : Rc ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hRrest)
  obtain ⟨P, hP, hPf, hPs, hPgap⟩ := hcoup R hRcm
  let v : (Site d → ℝ) → ℝ → Space d → ℝ := fun σ s y =>
    Frozen.HeatPotentialInvariance.linInterp d R (scenery d σ) s y
  let z : ΩW → ℝ → Space d → ℝ := fun ω s y => gaussianPotential d (variance id ν) W s y ω
  let badM : Set (Site d → ℝ) := {σ | ∃ p ∈ C, M < |v σ p.1 p.2|}
  let badO : Set (Site d → ℝ) := {σ | ∃ p ∈ C, ∃ q ∈ C,
    dist p q < a ∧ η < |v σ p.1 p.2 - v σ q.1 q.2|}
  let badG : Set ((Site d → ℝ) × ΩW) := {p | ∃ q ∈ C, η < |v p.1 q.1 q.2 - z p.2 q.1 q.2|}
  let badC : Set ΩW := {ω | ¬ Continuous fun q : ℝ × Space d => z ω q.1 q.2}
  have hbadM : centeredMassLaw d ν badM ≤ ENNReal.ofReal (δ / 3) := by
    apply le_trans (measure_mono ?_) (hM₀ R hR1)
    rintro σ ⟨q, hq, hv⟩
    exact ⟨q, hq, (le_max_left M₀ 0).trans_lt hv⟩
  have hbadO : centeredMassLaw d ν badO ≤ ENNReal.ofReal (δ / 3) := hosc R hR1
  have hbadC : PW badC = 0 := ae_iff.mp hZcont
  refine ⟨P, hP, hPf, hPs, ?_⟩
  have hsub : {p : (Site d → ℝ) × ΩW | ∃ u ∈ K,
      ε < |R ^ (-(2 - (d : ℝ) / 2)) *
        localizedOdometer (supBox (fun i => ⌊R * u i⌋) R) (scenery d p.1) ⌊T * R ^ 2⌋₊
          (fun i => ⌊R * u i⌋) - brownianValueCube (B u) PB (z p.2) T 1 u|} ⊆
      (Prod.fst ⁻¹' (badM ∪ badO)) ∪ badG ∪ (Prod.snd ⁻¹' badC) := by
    intro p hp
    by_cases hm : p.1 ∈ badM ∪ badO
    · exact Or.inl (Or.inl hm)
    by_cases hg : p ∈ badG
    · exact Or.inl (Or.inr hg)
    by_cases hc : p.2 ∈ badC
    · exact Or.inr hc
    have hvc : Continuous fun q : ℝ × Space d => z p.2 q.1 q.2 := of_not_not hc
    have hmb : ¬ ∃ q ∈ C, M < |v p.1 q.1 q.2| := fun h => hm (Or.inl h)
    have hob : ¬ ∃ q ∈ C, ∃ r ∈ C, dist q r < a ∧ η < |v p.1 q.1 q.2 - v p.1 r.1 r.2| :=
      fun h => hm (Or.inr h)
    obtain ⟨i, hi⟩ := hnear (v p.1) hmb hob
    obtain ⟨u, hu, huerr⟩ := hp
    have hcu : (T, u) ∈ C := by
      refine ⟨⟨hT.le, le_rfl⟩, ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      dsimp [A]
      nlinarith [hKn u hu, Real.sqrt_nonneg (d : ℝ)]
    have hcutgap : ∀ s ∈ Set.Icc 0 T, ∀ y,
        |cutoff A y * z p.2 s y - cutoff A y * v p.1 s y| ≤ η := by
      intro s hs y
      by_cases hy : 2 * A ≤ ‖y‖
      · rw [cutoff_eq_zero_of_norm_ge A hA y hy]
        simpa only [zero_mul, sub_self, abs_zero] using hη.le
      have hyC : (s, y) ∈ C := ⟨hs, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hy)⟩
      have he : |v p.1 s y - z p.2 s y| ≤ η := le_of_not_gt (fun h => hg ⟨(s, y), hyC, h⟩)
      rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A y), abs_sub_comm]
      nlinarith [cutoff_nonneg A y, cutoff_le_one A y, abs_nonneg (v p.1 s y - z p.2 s y)]
    have hf : ∀ s ∈ Set.Icc 0 T, ∀ y,
        |-(cutoff A y * v p.1 s y) - -G i s y| ≤ 2 * η := by
      intro s hs y
      simpa only [neg_sub_neg, abs_sub_comm] using hi s hs y
    have hh : ∀ s ∈ Set.Icc 0 T, ∀ y,
        |-(cutoff A y * z p.2 s y) - -G i s y| ≤ 3 * η := by
      intro s hs y
      have ht := abs_sub_le (cutoff A y * z p.2 s y) (cutoff A y * v p.1 s y) (G i s y)
      have he : |cutoff A y * z p.2 s y - G i s y| ≤ 3 * η := by
        linarith [hcutgap s hs y, hi s hs y]
      simpa only [neg_sub_neg, abs_sub_comm] using he
    have hs := hstab R hRsm u hu (fun s y => -(cutoff A y * v p.1 s y))
      (fun s y => -(cutoff A y * z p.2 s y)) i
      ((((continuous_cutoff A).comp continuous_snd).mul hvc).neg.continuousOn) hf hh
    have hflR : (0 : ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hRp.le
    have hcutw : ∀ y : Site d, (∀ j, |y j - ⌊R * u j⌋| ≤ ⌊R⌋ + 1) →
        cutoff A (External.Lclt.scaledSite R y) = 1 := by
      intro y hy
      exact cutoff_one_of_killed_site hd hR1 u (hKn u hu) (by dsimp [A]; linarith) y hy
    have hcutb : ∀ y : Space d, (∀ j, |y j - u j| ≤ 1) → cutoff A y = 1 := by
      intro y hy
      apply cutoff_eq_one_of_norm_le A hA
      have hn := norm_le_of_cube zero_le_one hy
      dsimp [A]
      nlinarith [hKn u hu, Real.sqrt_nonneg (d : ℝ)]
    dsimp only [v] at hs
    rw [killedStoppingSup_meshReward_eq hd R hRp.ne' A _ R hflR _ _ hcutw] at hs
    simp only [neg_neg] at hs
    rw [brownianDiscountCube_cutoff_eq (B u) PB (z p.2) T 1 A zero_le_one u
      (ae_continuous_of_isBrownian hd (hB u)) (hB u).start hcutb] at hs
    let n : ℕ := ⌊R ^ 2 * T⌋₊
    let y : Site d := fun j => ⌊R * u j⌋
    let q : ℝ × Space d := ((n : ℝ) / R ^ 2, Support.meshPoint R u)
    have hq : q ∈ C := by
      refine ⟨⟨div_nonneg (Nat.cast_nonneg n) (sq_nonneg R), ?_⟩, ?_⟩
      · apply (div_le_iff₀ (sq_pos_of_pos hRp)).2
        have hn := Nat.floor_le (show 0 ≤ R ^ 2 * T by positivity)
        dsimp [n]
        nlinarith
      · simp only [Metric.mem_closedBall, dist_zero_right]
        have hn : ‖Support.meshPoint R u‖ ≤ ‖Support.meshPoint R u - u‖ + ‖u‖ := by
          simpa only [sub_add_cancel] using norm_add_le (Support.meshPoint R u - u) u
        have hr : Real.sqrt d / R ≤ Real.sqrt d := div_le_self (Real.sqrt_nonneg _) hR1
        have hm := Support.norm_meshPoint_sub_le hRp u
        dsimp [A]
        nlinarith [hKn u hu, Real.sqrt_nonneg (d : ℝ)]
    have hmo : |v p.1 q.1 q.2 - v p.1 T u| ≤ η :=
      le_of_not_gt (fun h => hob ⟨q, hq, (T, u), hcu, hmesh R hRmm T hT.le u, h⟩)
    have hcou : |v p.1 T u - z p.2 T u| ≤ η :=
      le_of_not_gt (fun h => hg ⟨(T, u), hcu, h⟩)
    have hqval : v p.1 q.1 q.2 = Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n y := by
      simpa only [v, q, y, Nat.cast_zero, sub_zero, Nat.sub_zero,
        Support.scaledSite_floor_eq_meshPoint] using
        linInterp_scaledSite R hRp.ne' (scenery d p.1) n 0 (Nat.zero_le n) y
    have hfield : |Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n y - z p.2 T u| ≤ 2 * η := by
      rw [← hqval]
      have ht := abs_sub_le (v p.1 q.1 q.2) (v p.1 T u) (z p.2 T u)
      linarith
    have hy : y ∈ supBox y R := by
      intro j
      simpa only [sub_self, abs_zero] using hflR
    have hb := abs_rescaled_localizedOdometer_sub_brownianValueCube_le hd R hRp (supBox y R)
      (scenery d p.1) n y hy (B u) PB (z p.2) T 1 u (2 * η) (ε / 4 + 2 * η + 3 * η) hfield hs
    have hn : ⌊T * R ^ 2⌋₊ = n := by dsimp [n]; rw [mul_comm]
    have he : -(2 - (d : ℝ) / 2) = (d : ℝ) / 2 - 2 := by ring
    rw [hn, he] at huerr
    dsimp [y] at hb
    dsimp [η] at hb
    exfalso
    linarith
  calc
    P _ ≤ centeredMassLaw d ν (badM ∪ badO) + P badG + PW badC :=
      measure_error_le_of_marginals (centeredMassLaw d ν) PW P hPf hPs (badM ∪ badO) badC badG _ hsub
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) + 0 := by
      rw [hbadC]
      exact add_le_add (add_le_add ((measure_union_le _ _).trans (add_le_add hbadM hbadO)) hPgap) le_rfl
    _ = ENNReal.ofReal δ := by
      rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
