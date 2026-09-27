/-
The parabolic scaling limit of `thm:main-explosion`(i)(b) at a CONTINUOUS
VERSION of the Gaussian heat potential, assembled from its inputs: the
version-bearing analogue of `Sandpile.dlt4_scaling_of_inputs`.

The four errors of `Sandpile.abs_rescaled_odometer_sub_brownianValue_le` are
supplied by the field coupling and the mesh approximation, by the walk half of
the cutoff error at the dyadic-annulus bound of the interpolated field, by the
stability gap at the two cut-off rewards, and by the Brownian half of the cutoff
error at the polynomial envelope of the limit field.  What the cube-killed route
got for free from the confinement of the walk in the cube, the unkilled route
gets from those two annulus estimates.

The field `Z` is only almost surely equal to the Gaussian potential at each
point (`hZmod`), continuous on each time strip almost surely (`hZcont`) and of
polynomial growth there (`hZgrow`); the coupling and the deterministic growth
bound are taken at `Z` itself through
`Sandpile.Continuum.heat_field_coupling_of_version` and
`Sandpile.Support.exists_deterministic_growth_of_version`, and the value on the
Brownian side is evaluated at `Z`, never at the Gaussian potential.
-/
import Sandpile.Support.MainExplStability
import Sandpile.Support.MainExplBrownCutoff
import Sandpile.Support.MainExplAnnulus
import Sandpile.Support.MainExplVersion
import Sandpile.Support.KillMeshApproximation
import Sandpile.Support.ExplRewardFamily
import Sandpile.Support.ExplBallBound
import Sandpile.Support.ExplBallReward
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.Frozen.HeatPotentialInvariance

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

universe u v
open Sandpile Sandpile.Continuum

set_option maxHeartbeats 3200000 in
theorem Sandpile.dlt4_scaling_of_version
    (_hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (ΩW : Type v) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d =>
        Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.odometerOf (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊
                    (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValue (B u) PB
                    (fun t y => Z t y p.2)
                    T u|}
          ≤ ENNReal.ofReal δ := by
  classical
  have hBmM : ∀ (y : Space d) (t : ℝ≥0), Measurable (B y t) :=
    fun y t => (hBm y t).measurable
  obtain ⟨hfdd, htight⟩ := Sandpile.Frozen.heat_potential_invariance d (by omega) hd3
    ν hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T hT
  obtain ⟨ρ, hρ, hKρ⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : Space d)
  have hKn : ∀ u ∈ K, ‖u‖ ≤ ρ := fun u hu => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hKρ hu
  set η : ℝ := ε / 32 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  have hδ5 : 0 < δ / 5 := by positivity
  obtain ⟨Kw, hKw, hwenv⟩ := Sandpile.Support.exists_mesh_annulus_bound
    Sandpile.External.heatKernelBounds hd hd3 (θ := 1/2) (by norm_num) (by norm_num)
    ν hmean hθ₀ hexp T hT.le (δ / 5) hδ5
  have hmeasZ : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
      AEMeasurable (Z q.1 q.2) PW := by
    intro q hq
    exact (measurable_const.mul (hW.meas _
      (Sandpile.Support.memLp_greenTimeBM hd hd3 hq.1.1 q.2))).aemeasurable.congr
      (hZmod q.1 q.2).symm
  obtain ⟨mz, Nz, hNzm, hNz, hzenv⟩ := Sandpile.Support.exists_deterministic_growth_of_version
    PW Z T hT.le hmeasZ hZcont hZgrow (δ / 5) hδ5
  obtain ⟨A₁, hA₁4, hA₁⟩ := Sandpile.exists_walk_cutoff_stoppingSup_gap d hd 1
    (K := Kw) (T := T) (ε := ε / 8) hKw hT (by positivity)
  obtain ⟨A₂, hA₂4, hA₂⟩ := Sandpile.Continuum.exists_brownianDiscount_cutoff_gap_of_growth
    d mz (K := (mz : ℝ)) (T := T) (ε := ε / 8) (Nat.cast_nonneg mz) hT (by positivity)
  set ρ' : ℝ := ρ + Real.sqrt d + 1 with hρ'def
  have hρ'0 : 0 ≤ ρ' := by rw [hρ'def]; positivity
  set A : ℝ := max (max A₁ A₂) (max (2 * ρ' + 1) (ρ' + 3 * Real.sqrt d + 4)) with hAdef
  have hAA₁ : A₁ ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hAA₂ : A₂ ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₁4 hAA₁
  have hA0 : (0 : ℝ) < A := by linarith
  have hAρ' : 2 * ρ' + 1 ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAbox : ρ' + 3 * Real.sqrt d + 4 ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  set C : Set (ℝ × Space d) := rewardBox d T A with hCdef
  have hCc : IsCompact C := isCompact_rewardBox d T A
  have hCs : C ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  obtain ⟨M₀, hM₀⟩ := (htight C hCc hCs).1 (δ / 5) hδ5
  set M : ℝ := max M₀ 0 with hMdef
  have hM : (0 : ℝ) ≤ M := le_max_right _ _
  obtain ⟨a, ha, hosc⟩ := (htight C hCc hCs).2 (δ / 5) η hδ5 hη
  obtain ⟨N, G, hGc, hGM, hnear⟩ := exists_cutoff_reward_family d A T hA0 M η a hM hη ha
  obtain ⟨Rs, hRs, hstab⟩ := Sandpile.stability_gap_of_two_rewards hStab d hd ΩB PB B hB T hT
    K hK N (fun i s y => -G i s y) (fun i => (hGc i).neg) (M + η)
    (fun i s y => by simpa only [abs_neg] using hGM i s y) (ε / 8) (2 * η) (3 * η)
    (by positivity)
  obtain ⟨Rm, hRm, hmesh⟩ := Sandpile.exists_parabolic_mesh_threshold d a ha
  obtain ⟨Rc, hRc, hcoup⟩ := Sandpile.Continuum.heat_field_coupling_of_version d hd hd3 ν
    ΩW PW W hW Z hZmod T hT hZcont hfdd htight C hCc hCs η (δ / 5) hη hδ5
  refine ⟨max (1 + 1 / T) (max Rs (max Rm Rc)),
    lt_of_lt_of_le (by positivity) (le_max_left _ _), ?_⟩
  intro R hR
  have hR1T : 1 + 1 / T ≤ R := (le_max_left _ _).trans hR
  have hTinv : (0 : ℝ) < 1 / T := by positivity
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRp : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hrest : max Rs (max Rm Rc) ≤ R := (le_max_right _ _).trans hR
  have hRsm : Rs ≤ R := (le_max_left _ _).trans hrest
  have hRmm : Rm ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hRcm : Rc ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hrest)
  have hTR : (1 : ℝ) ≤ T * R ^ 2 := by
    have h1 : 1 / T ≤ R := by linarith
    have h2 : R ≤ R ^ 2 := by nlinarith
    have h3 : 1 / T ≤ R ^ 2 := le_trans h1 h2
    rw [div_le_iff₀ hT] at h3
    nlinarith
  have hn1 : 1 ≤ ⌊T * R ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hTR)
  obtain ⟨P, hP, hPf, hPs, hPgap⟩ := hcoup R hRcm
  obtain ⟨Gw, hGwm, hGw⟩ := hwenv R hR1
  refine ⟨P, hP, hPf, hPs, ?_⟩
  set v : (Site d → ℝ) → ℝ → Space d → ℝ := fun σ s y =>
    Frozen.HeatPotentialInvariance.linInterp d R (scenery d σ) s y with hvdef
  set z : ΩW → ℝ → Space d → ℝ := fun ω s y => Z s y ω with hzdef
  set badM : Set (Site d → ℝ) := {σ | ∃ p ∈ C, M < |v σ p.1 p.2|} with hbadMdef
  set badO : Set (Site d → ℝ) := {σ | ∃ p ∈ C, ∃ q ∈ C,
    dist p q < a ∧ η < |v σ p.1 p.2 - v σ q.1 q.2|} with hbadOdef
  set badG : Set ((Site d → ℝ) × ΩW) := {p | ∃ q ∈ C,
    η < |v p.1 q.1 q.2 - z p.2 q.1 q.2|} with hbadGdef
  set badC : Set ΩW := {ω | ¬ ContinuousOn (fun q : ℝ × Space d => z ω q.1 q.2)
    (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))} with hbadCdef
  have hbadM : centeredMassLaw d ν badM ≤ ENNReal.ofReal (δ / 5) := by
    apply le_trans (measure_mono ?_) (hM₀ R hR1)
    rintro σ ⟨q, hq, hv⟩
    exact ⟨q, hq, (le_max_left M₀ 0).trans_lt hv⟩
  have hbadO : centeredMassLaw d ν badO ≤ ENNReal.ofReal (δ / 5) := hosc R hR1
  have hbadC : PW badC = 0 := ae_iff.mp hZcont
  have hsub : {p : (Site d → ℝ) × ΩW | ∃ u ∈ K,
      ε < |R ^ (-(2 - (d : ℝ) / 2)) *
            odometerOf (scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
          - brownianValue (B u) PB (z p.2) T u|} ⊆
      (Prod.fst ⁻¹' ((badM ∪ badO) ∪ Gwᶜ)) ∪ badG ∪ (Prod.snd ⁻¹' (badC ∪ Nz)) := by
    intro p hp
    by_cases hm : p.1 ∈ badM ∪ badO
    · exact Or.inl (Or.inl (Or.inl hm))
    by_cases hw : p.1 ∈ Gwᶜ
    · exact Or.inl (Or.inl (Or.inr hw))
    by_cases hg : p ∈ badG
    · exact Or.inl (Or.inr hg)
    by_cases hc : p.2 ∈ badC
    · exact Or.inr (Or.inl hc)
    by_cases hzb : p.2 ∈ Nz
    · exact Or.inr (Or.inr hzb)
    exfalso
    have hvc : ContinuousOn (fun q : ℝ × Space d => z p.2 q.1 q.2)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d))) := of_not_not hc
    have hσG : p.1 ∈ Gw := of_not_not hw
    have hmb : ¬ ∃ q ∈ C, M < |v p.1 q.1 q.2| := fun h => hm (Or.inl h)
    have hob : ¬ ∃ q ∈ C, ∃ r ∈ C, dist q r < a ∧ η < |v p.1 q.1 q.2 - v p.1 r.1 r.2| :=
      fun h => hm (Or.inr h)
    obtain ⟨i, hi⟩ := hnear (v p.1) hmb hob
    obtain ⟨u, hu, huerr⟩ := hp
    have hRne : R ≠ 0 := ne_of_gt hRp
    set n : ℕ := ⌊R ^ 2 * T⌋₊ with hndef
    set yy : Sandpile.Site d := fun j => ⌊R * u j⌋ with hyydef
    have hnT : (n : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
    have hnn : ⌊T * R ^ 2⌋₊ = n := by rw [hndef, mul_comm]
    have hun : ‖u‖ ≤ ρ := hKn u hu
    have hsd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
    have hmesh0 : ‖Support.meshPoint R u - u‖ ≤ Real.sqrt d / R :=
      Support.norm_meshPoint_sub_le hRp u
    have hsd : Real.sqrt d / R ≤ Real.sqrt d := div_le_self hsd0 hR1
    have hmeshn : ‖Support.meshPoint R u‖ ≤ ρ + Real.sqrt d := by
      have h := norm_add_le (Support.meshPoint R u - u) u
      rw [sub_add_cancel] at h
      linarith
    have hρ'val : ρ' = ρ + Real.sqrt d + 1 := hρ'def
    have hρA : ρ ≤ A := by rw [hρ'val] at hAbox; linarith
    have hyρ' : ‖Sandpile.External.Lclt.scaledSite R yy‖ ≤ ρ' := by
      rw [hyydef, Support.scaledSite_floor_eq_meshPoint, hρ'val]
      linarith
    have hcu : (T, u) ∈ C := by
      refine ⟨⟨hT.le, le_rfl⟩, ?_⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hqmem : (((n : ℝ) / R ^ 2, Support.meshPoint R u) : ℝ × Space d) ∈ C := by
      refine ⟨⟨div_nonneg (Nat.cast_nonneg n) (sq_nonneg R), ?_⟩, ?_⟩
      · apply (div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)).2
        rw [hndef]
        nlinarith [Nat.floor_le (show (0:ℝ) ≤ R ^ 2 * T by positivity)]
      · simp only [Metric.mem_closedBall, dist_zero_right]
        rw [hρ'val] at hAbox
        linarith
    have hmo : |v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u) - v p.1 T u| ≤ η :=
      le_of_not_gt (fun h => hob ⟨((n : ℝ) / R ^ 2, Support.meshPoint R u), hqmem, (T, u), hcu,
        by rw [hndef]; exact hmesh R hRmm T hT.le u, h⟩)
    have hcou : |v p.1 T u - z p.2 T u| ≤ η :=
      le_of_not_gt (fun h => hg ⟨(T, u), hcu, h⟩)
    have hqval : v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u)
        = Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n yy := by
      have h := Sandpile.linInterp_scaledSite R hRne (scenery d p.1) n 0 (Nat.zero_le n) yy
      simpa only [hvdef, hyydef, Nat.cast_zero, sub_zero, Nat.sub_zero,
        Support.scaledSite_floor_eq_meshPoint] using h
    have hfield : |Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) n yy
        - z p.2 T u| ≤ 2 * η := by
      rw [← hqval]
      have ht := abs_sub_le (v p.1 ((n : ℝ) / R ^ 2) (Support.meshPoint R u)) (v p.1 T u)
        (z p.2 T u)
      linarith
    have hA1 : (1 : ℝ) ≤ A := by linarith
    set f : ℕ → Sandpile.Site d → ℝ := fun k w =>
      -(Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) (n - k) w) with hfdef
    set g : ℕ → Sandpile.Site d → ℝ := fun k w =>
      cutoff A (Sandpile.External.Lclt.scaledSite R w) * f k w with hgdef
    have hE₁ : |stoppingSup n yy (fun k X => f k (X k)) -
        stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k))| ≤ ε / 8 := by
      refine hA₁ A hAA₁ R hR1 yy ρ' hρ'0 hyρ' (by linarith) n (hnn ▸ hn1) hnT
        (fun k X => f k (X k)) (fun τ hτ hτn => Sandpile.measurable_stopped_value n f hτ hτn)
        ?_ (Sandpile.bddAbove_walk_stopped_value hd yy n f)
        (Sandpile.bddAbove_walk_stopped_value hd yy n g)
        (fun τ hτ hτn => Sandpile.integrable_stopped_value hd yy n f hτ hτn)
        (fun τ hτ hτn => Sandpile.integrable_stopped_value hd yy n g hτ hτn)
      intro τ hτn X j hj
      exact hGw p.1 hσG A hA1 n hnT τ hτn X j hj
    have hcutgap : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ w : Space d,
        |cutoff A w * z p.2 s w - cutoff A w * v p.1 s w| ≤ η := by
      intro s hs w
      by_cases hy : 2 * A ≤ ‖w‖
      · rw [cutoff_eq_zero_of_norm_ge A hA0 w hy]
        simpa only [zero_mul, sub_self, abs_zero] using hη.le
      have hwC : (s, w) ∈ C := ⟨hs, by
        simpa only [Metric.mem_closedBall, dist_zero_right] using (le_of_not_ge hy)⟩
      have he : |v p.1 s w - z p.2 s w| ≤ η := le_of_not_gt (fun h => hg ⟨(s, w), hwC, h⟩)
      rw [← mul_sub, abs_mul, abs_of_nonneg (cutoff_nonneg A w), abs_sub_comm]
      nlinarith [cutoff_nonneg A w, cutoff_le_one A w, abs_nonneg (v p.1 s w - z p.2 s w)]
    have hE₂ := hstab R hRsm hRp u hu
      (fun s w => -(cutoff A w * v p.1 s w)) (fun s w => -(cutoff A w * z p.2 s w)) i
      ((((continuous_cutoff A).comp continuous_snd).continuousOn.mul hvc).neg)
      (fun s hs w => by
        have h := hi s hs w
        have hrw : -(cutoff A w * v p.1 s w) - -G i s w
            = -(cutoff A w * v p.1 s w - G i s w) := by ring
        rw [hrw, abs_neg]; exact h)
      (fun s hs w => by
        have h1 := hcutgap s hs w
        have h2 := hi s hs w
        have ht := abs_sub_le (cutoff A w * z p.2 s w) (cutoff A w * v p.1 s w) (G i s w)
        have hrw : -(cutoff A w * z p.2 s w) - -G i s w
            = -(cutoff A w * z p.2 s w - G i s w) := by ring
        rw [hrw, abs_neg]; linarith)
    have hwalkeq : stoppingSup n yy (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
        -(cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) *
          v p.1 (((n : ℕ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))))
        = stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k)) := by
      refine Sandpile.stoppingSup_congr_of_le n yy _ _ ?_
      intro k hk X
      simpa only [hvdef, hfdef] using
        Sandpile.cutoff_linInterp_scaledSite R hRne (scenery d p.1) A n k hk (X k)
    have hgrowz := hzenv p.2 hzb
    have hcz : ContinuousOn (fun q : ℝ × Space d => z p.2 q.1 q.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Space d))) := hvc
    have hcχ : ContinuousOn (fun q : ℝ × Space d => cutoff A q.2 * z p.2 q.1 q.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Space d))) :=
      ((continuous_cutoff A).comp continuous_snd).continuousOn.mul hvc
    have hgrowu : ∀ vv : ℝ≥0, vv ≤ T.toNNReal → ∀ w : Space d,
        ‖z p.2 (vv : ℝ) w‖ ≤ ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by
      intro vv hvv w
      have hvvT : (vv : ℝ) ≤ T := by
        have := NNReal.coe_le_coe.2 hvv
        rwa [Real.coe_toNNReal T hT.le] at this
      have h1 := hgrowz (vv : ℝ) ⟨vv.coe_nonneg, hvvT⟩ w
      have h2 : ‖w‖ ≤ ‖w - u‖ + ρ := by
        have h := norm_add_le (w - u) u
        rw [sub_add_cancel] at h
        linarith
      have h3 : (1 + ‖w‖) ≤ (1 + ρ) * (1 + ‖w - u‖) := by
        nlinarith [norm_nonneg (w - u), hρ]
      have h4 : (1 + ‖w‖) ^ mz ≤ ((1 + ρ) * (1 + ‖w - u‖)) ^ mz :=
        pow_le_pow_left₀ (by positivity) h3 mz
      rw [Real.norm_eq_abs]
      calc |z p.2 (vv : ℝ) w| ≤ (mz : ℝ) * (1 + ‖w‖) ^ mz := h1
        _ ≤ (mz : ℝ) * ((1 + ρ) * (1 + ‖w - u‖)) ^ mz :=
            mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg mz)
        _ = ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by rw [mul_pow]; ring
    have hgrowuχ : ∀ vv : ℝ≥0, vv ≤ T.toNNReal → ∀ w : Space d,
        ‖cutoff A w * z p.2 (vv : ℝ) w‖ ≤ ((mz : ℝ) * (1 + ρ) ^ mz) * (1 + ‖w - u‖) ^ mz := by
      intro vv hvv w
      have h := hgrowu vv hvv w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg A w)] at *
      nlinarith [cutoff_nonneg A w, cutoff_le_one A w, abs_nonneg (z p.2 (vv : ℝ) w)]
    obtain ⟨Denv, hDenv, hDdom⟩ := Sandpile.Support.exists_brownian_envelope_of_polynomial_growth
      (hB u) (hBmM u) (hBc u) (z p.2) T.toNNReal ((mz : ℝ) * (1 + ρ) ^ mz) (by positivity) mz
      hgrowu
    have hdom : ∀ᵐ ω' ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
        ‖z p.2 (T - (r : ℝ)) (B u r ω')‖ ≤ Denv ω' := by
      refine Filter.Eventually.of_forall fun ω' r hr => ?_
      have hrT : r ≤ T.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT.le]; exact hr
      have hsub : ((T.toNNReal - r : ℝ≥0) : ℝ) = T - (r : ℝ) := by
        rw [NNReal.coe_sub hrT, Real.coe_toNNReal T hT.le]
      have h := hDdom ω' (T.toNNReal - r) tsub_le_self r hrT
      rwa [hsub] at h
    have hdomχ : ∀ᵐ ω' ∂PB, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
        ‖cutoff A (B u r ω') * z p.2 (T - (r : ℝ)) (B u r ω')‖ ≤ Denv ω' := by
      filter_upwards [hdom] with ω' hω' r hr
      have h := hω' r hr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutoff_nonneg A _)]
      rw [Real.norm_eq_abs] at h
      nlinarith [cutoff_nonneg A (B u r ω'), cutoff_le_one A (B u r ω'),
        abs_nonneg (z p.2 (T - (r : ℝ)) (B u r ω'))]
    have hint1 := Sandpile.Continuum.integrable_stopped_reward_of_envelope (B u) PB (z p.2) T
      hcz (fun t => (hBmM u t).aemeasurable) (Filter.Eventually.of_forall (hBc u)) Denv hDenv hdom
    have hint2 := Sandpile.Continuum.integrable_stopped_reward_of_envelope (B u) PB
      (fun s w => cutoff A w * z p.2 s w) T hcχ (fun t => (hBmM u t).aemeasurable)
      (Filter.Eventually.of_forall (hBc u)) Denv hDenv hdomχ
    have hmeasY : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B u) τ →
        Measurable (fun ω' => B u (τ ω') ω') := fun τ hτ =>
      Sandpile.Continuum.measurable_stopped_position (hBmM u) (hBc u)
        (hτ.measurable (hBm u))
    have hint3 : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B u) τ → (∀ ω', (τ ω' : ℝ) ≤ T) →
        Integrable (fun ω' => (1 - cutoff A (B u (τ ω') ω')) *
          |z p.2 (T - (τ ω' : ℝ)) (B u (τ ω') ω')|) PB := by
      intro τ hτ hτT
      have hz1 : Integrable (fun ω' => |z p.2 (T - (τ ω' : ℝ)) (B u (τ ω') ω')|) PB := by
        simpa only [abs_neg] using (hint1 τ hτ hτT).abs
      refine Integrable.mono' hz1 ?_ ?_
      · exact (((continuous_cutoff A).measurable.comp (hmeasY τ hτ)).const_sub
          1).aestronglyMeasurable.mul hz1.aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω' => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        have h0 : 0 ≤ 1 - cutoff A (B u (τ ω') ω') := by
          linarith [cutoff_le_one A (B u (τ ω') ω')]
        rw [abs_of_nonneg h0]
        nlinarith [cutoff_nonneg A (B u (τ ω') ω'),
          abs_nonneg (z p.2 (T - (τ ω' : ℝ)) (B u (τ ω') ω'))]
    have hbdd1 : BddAbove (stoppingPayoffs (B u) PB (z p.2) T) :=
      Sandpile.Continuum.bddAbove_stoppingPayoffs_of_samplewise_growth (hB u) (hBmM u) (hBc u)
        (z p.2) T hT.le hcz (fun _ => (mz : ℝ) * (1 + ρ) ^ mz) ((mz : ℝ) * (1 + ρ) ^ mz)
        (Filter.Eventually.of_forall fun _ => le_refl _) mz
        (Filter.Eventually.of_forall fun _ vv hvv w => hgrowu vv
          (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT.le]; exact hvv) w)
    have hbdd2 : BddAbove (stoppingPayoffs (B u) PB (fun s w => cutoff A w * z p.2 s w) T) :=
      Sandpile.Continuum.bddAbove_stoppingPayoffs_of_samplewise_growth (hB u) (hBmM u) (hBc u)
        (fun s w => cutoff A w * z p.2 s w) T hT.le hcχ
        (fun _ => (mz : ℝ) * (1 + ρ) ^ mz) ((mz : ℝ) * (1 + ρ) ^ mz)
        (Filter.Eventually.of_forall fun _ => le_refl _) mz
        (Filter.Eventually.of_forall fun _ vv hvv w => hgrowuχ vv
          (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT.le]; exact hvv) w)
    have hE₃ := hA₂ A hAA₂ u ΩB inferInstance PB inferInstance (B u) (hB u) ρ hρ.le hun
      (by linarith) (z p.2) hgrowz hbdd1 hbdd2 hint1 hint2 hint3
      (fun τ hτ _ j => Sandpile.Continuum.measurableSet_reach_brownian (hBmM u) (hBc u) hτ _)
    have hcutB : |brownianDiscount (B u) PB (fun s w => cutoff A w * z p.2 s w) T
        - brownianDiscount (B u) PB (z p.2) T| ≤ ε / 8 := by
      rw [abs_sub_comm]; exact hE₃
    have hE₂' : |stoppingSup n yy (fun k X =>
          cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * f k (X k))
        - brownianDiscount (B u) PB (fun s w => cutoff A w * z p.2 s w) T|
        ≤ ε / 8 + 2 * η + 3 * η := by
      rw [← hwalkeq]
      simpa only [hnn, neg_neg] using hE₂
    simp only [hfdef] at hE₁ hE₂'
    have hb := Sandpile.abs_rescaled_odometer_sub_brownianValue_le hd R hRp (scenery d p.1) n yy
      (B u) PB (z p.2) (fun s w => cutoff A w * z p.2 s w) T u
      (fun k X => cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) *
        -(Frozen.HeatPotentialInvariance.meshValue d R (scenery d p.1) (n - k) (X k)))
      (2 * η) (ε / 8) (ε / 8 + 2 * η + 3 * η) (ε / 8) hfield hE₁ hE₂' hcutB
    rw [hnn] at huerr
    have he : -(2 - (d : ℝ) / 2) = (d : ℝ) / 2 - 2 := by ring
    rw [he] at huerr
    rw [hηdef] at hb
    linarith
  calc P _ ≤ centeredMassLaw d ν ((badM ∪ badO) ∪ Gwᶜ) + P badG + PW (badC ∪ Nz) :=
        measure_error_le_of_marginals (centeredMassLaw d ν) PW P hPf hPs
          ((badM ∪ badO) ∪ Gwᶜ) (badC ∪ Nz) badG _ hsub
    _ ≤ ((ENNReal.ofReal (δ / 5) + ENNReal.ofReal (δ / 5)) + ENNReal.ofReal (δ / 5))
          + ENNReal.ofReal (δ / 5) + (0 + ENNReal.ofReal (δ / 5)) := by
        refine add_le_add (add_le_add ?_ hPgap) ?_
        · exact (measure_union_le _ _).trans
            (add_le_add ((measure_union_le _ _).trans (add_le_add hbadM hbadO)) hGwm)
        · exact (measure_union_le _ _).trans (add_le_add (le_of_eq hbadC) hNz)
    _ = ENNReal.ofReal δ := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
