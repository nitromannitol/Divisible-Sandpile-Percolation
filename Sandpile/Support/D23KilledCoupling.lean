/-
The cube-killed scaling argument along varying scenery laws with a common
exponential bound (`sandpile.tex:1950-1955,2640-2647`). The only heat-potential
limit input is finite-dimensional convergence along the same sequence.
-/
import Sandpile.Support.D23HeatCoupling
import Sandpile.Support.KillValueStability
import Sandpile.Support.KillMeshApproximation
import Sandpile.Support.KillAssembly
import Sandpile.Support.KillRadius
import Sandpile.Support.ExplRewardFamily

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal
open Sandpile Sandpile.Continuum

/-- Uniform moments and finite-dimensional convergence transfer to a compact
coupling of the cube-killed odometers and their limiting stopping value. -/
theorem Sandpile.dlt4_killed_scaling_seq_of_fdd
    (hStab : Sandpile.External.CubeStoppingStability)
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (ν n))
    (hK₀ : ∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(ν n) ≤ K₀)
    (Rseq : ℕ → ℝ) (hRseq : Tendsto Rseq atTop atTop)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (Z : ΩW → ℝ → Space d → ℝ)
    (hZcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Space d => Z ω q.1 q.2)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Space d → ℝ≥0 → ΩB → Space d) (hB : ∀ y, IsBrownian d y (B y) PB)
    (K : Set (Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun n (σ : Site d → ℝ) (i : Fin m) =>
          Frozen.HeatPotentialInvariance.linInterp d (Rseq n) (scenery d σ) (r i) (w i))
        atTop (fun ω i => Z ω (r i) (w i))
        (fun n => centeredMassLaw d (ν n)) PW)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∃ P : Measure ((Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
      P.map Prod.fst = centeredMassLaw d (ν n) ∧ P.map Prod.snd = PW ∧
      P {p | ∃ u ∈ K,
          ε < |(Rseq n) ^ (-(2 - (d : ℝ) / 2)) *
                localizedOdometer (supBox (fun i => ⌊Rseq n * u i⌋) (Rseq n))
                  (scenery d p.1) ⌊T * (Rseq n) ^ 2⌋₊ (fun i => ⌊Rseq n * u i⌋)
              - brownianValueCube (B u) PB (Z p.2) T 1 u|} ≤ ENNReal.ofReal δ := by
  classical
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
  have htight := Support.heat_potential_tightness_uniform_of_exp_bound
    hd hd3 θ₀ K₀ hθ₀ T hT C hCc hCs
  obtain ⟨M₀, hM₀⟩ := htight.1 (δ / 3) hδ3
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨a, ha, hosc⟩ := htight.2 (δ / 3) η hδ3 hη
  obtain ⟨N, G, hGc, hGM, hnear⟩ := exists_cutoff_reward_family d A T hA M η a hM hη ha
  obtain ⟨Rs, hRs, hstab⟩ := Sandpile.killed_stability_gap_of_two_rewards hStab d hd ΩB PB B hB
    T hT K hK N (fun i s y => -G i s y) (fun i => (hGc i).neg) (M + η)
    (fun i s y => by simpa only [abs_neg] using hGM i s y)
    (ε / 4) (2 * η) (3 * η) (by positivity)
  obtain ⟨Rm, hRm, hmesh⟩ := Sandpile.exists_parabolic_mesh_threshold d a ha
  have hcoup := Continuum.heat_field_coupling_seq_of_fdd hd hd3 θ₀ K₀ hθ₀
    ν hmean hexp hK₀ Rseq hRseq PW Z hZcont T hT hfdd C hCc hCs η (δ / 3) hη hδ3
  filter_upwards [hcoup, hRseq.eventually (eventually_ge_atTop (max 1 (max Rs Rm)))]
    with j hj hR
  let R := Rseq j
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRsm : Rs ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRmm : Rm ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  obtain ⟨P, hP, hPf, hPs, hPgap⟩ := hj
  let v : (Site d → ℝ) → ℝ → Space d → ℝ := fun σ s y =>
    Frozen.HeatPotentialInvariance.linInterp d R (scenery d σ) s y
  let z : ΩW → ℝ → Space d → ℝ := Z
  let badM : Set (Site d → ℝ) := {σ | ∃ p ∈ C, M < |v σ p.1 p.2|}
  let badO : Set (Site d → ℝ) := {σ | ∃ p ∈ C, ∃ q ∈ C,
    dist p q < a ∧ η < |v σ p.1 p.2 - v σ q.1 q.2|}
  let badG : Set ((Site d → ℝ) × ΩW) := {p | ∃ q ∈ C, η < |v p.1 q.1 q.2 - z p.2 q.1 q.2|}
  let badC : Set ΩW := {ω | ¬ Continuous fun q : ℝ × Space d => z ω q.1 q.2}
  have hbadM : centeredMassLaw d (ν j) badM ≤ ENNReal.ofReal (δ / 3) := by
    apply le_trans (measure_mono ?_) (hM₀ (ν j) inferInstance (hmean j) (hexp j) (hK₀ j) R hR1)
    rintro σ ⟨q, hq, hv⟩
    exact ⟨q, hq, (le_max_left M₀ 0).trans_lt hv⟩
  have hbadO : centeredMassLaw d (ν j) badO ≤ ENNReal.ofReal (δ / 3) := hosc (ν j) inferInstance (hmean j) (hexp j) (hK₀ j) R hR1
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
    P _ ≤ centeredMassLaw d (ν j) (badM ∪ badO) + P badG + PW badC :=
      measure_error_le_of_marginals (centeredMassLaw d (ν j)) PW P hPf hPs (badM ∪ badO) badC badG _ hsub
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) + 0 := by
      rw [hbadC]
      exact add_le_add (add_le_add ((measure_union_le _ _).trans (add_le_add hbadM hbadO)) hPgap) le_rfl
    _ = ENNReal.ofReal δ := by
      rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
