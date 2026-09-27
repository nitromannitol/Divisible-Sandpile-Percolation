/-
The oscillation of the rescaled odometer between two lattice sites at a general,
fixed continuum mesh distance, generalizing `Sandpile.exists_odometer_cell_oscillation`
(`MainExplOsc.lean`, unit lattice step only) to the separation clause 2 of
`thm:main-explosion`(i)(b) needs.

Clause 2's modulus-of-continuity sub-clause asks for the oscillation of the
interpolated field between two points `z, z' ∈ K` at a *fixed* continuum distance
`< δ`, not one that shrinks as `R → ∞`; the corresponding lattice separation `e`
between `⌊Rz⌋` and `⌊Rz'⌋` is therefore unbounded in lattice units as `R → ∞`,
only its continuum-scaled norm `‖scaledSite R e‖` stays bounded by `δ`. The two
general helper theorems `exists_odometer_cell_oscillation` built
(`Sandpile.abs_stoppingSup_translate_sub_le`,
`Sandpile.abs_rescaled_odometer_translate_sub_le`, both in `MainExplOsc.lean`)
already impose no bound on `e`'s size and need no change; what is generalized here
is `Sandpile.abs_cutoff_meshValue_translate_sub_le`, whose only use of the unit-step
hypothesis is to bound `‖scaledSite R e‖` by `√d/R` through `norm_scaledSite_sub_le`,
replaced here by taking that continuum bound directly as a hypothesis (`scaledSite`
is exactly additive in the site, so the bound is not even approximate).

Because the separation is now measured in continuum units fixed independently of
`R`, the threshold `δ` this file produces does not need to shrink as `R → ∞`
either: it is chosen once, before `R₀`, small enough to fall inside the two moduli
of continuity `heat_potential_invariance` supplies and to make the cutoff's
Lipschitz contribution `δ/A · M` at most one quarter of the target accuracy. The
radius `A` and the compact sets the field is read on are fixed first, using the
worst case `δ ≤ 1`, so that `A` does not depend on the value of `δ` finally chosen.
-/
import Sandpile.Support.MainExplOsc

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- `scaledSite` is exactly additive in the site: no approximation, unlike the
per-coordinate bound `norm_scaledSite_sub_le` needs for a general integer offset. -/
theorem scaledSite_add (R : ℝ) (y e : Site d) :
    Sandpile.External.Lclt.scaledSite R (y + e)
      = Sandpile.External.Lclt.scaledSite R y + Sandpile.External.Lclt.scaledSite R e := by
  ext i
  show (((y + e) i : ℤ) : ℝ) / R = ((y i : ℤ) : ℝ) / R + ((e i : ℤ) : ℝ) / R
  have : (((y + e) i : ℤ) : ℝ) = ((y i : ℤ) : ℝ) + ((e i : ℤ) : ℝ) := by
    simp only [Pi.add_apply]; push_cast; ring
  rw [this]; ring

/-- **The oscillation of the cutoff-weighted mesh field between two sites, at a continuum
separation bounded directly rather than derived from a unit lattice step.** This is
`Sandpile.abs_cutoff_meshValue_translate_sub_le` with `he : ∀i,|e i|≤1` replaced by
`heη : ‖scaledSite R e‖ ≤ η`, using the exact additivity `scaledSite_add` instead of
`norm_scaledSite_sub_le` to read off the corner shift. -/
theorem abs_cutoff_meshValue_translate_sub_le_of_dist
    (_hd : 1 ≤ d) (R : ℝ) (hR : 1 ≤ R) (A : ℝ) (hA : 0 < A)
    (ζ : Site d → ℝ) (n : ℕ) (e : Site d) (η : ℝ) (hη0 : 0 ≤ η)
    (heη : ‖Sandpile.External.Lclt.scaledSite R e‖ ≤ η)
    (M ε₀ : ℝ) (hM0 : 0 ≤ M) (hε₀0 : 0 ≤ ε₀)
    (hM : ∀ z : Site d, ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * η + 1 →
      |Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ M)
    (hε₀ : ∀ z : Site d, ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * η + 1 →
      |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
        - Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ ε₀) :
    ∀ z : Site d,
      |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z)) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z))
        - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n z)|
      ≤ η / A * M + ε₀ := by
  intro z
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have hdist : ‖Sandpile.External.Lclt.scaledSite R (e + z)
      - Sandpile.External.Lclt.scaledSite R z‖ ≤ η := by
    rw [scaledSite_add, add_sub_cancel_right]; exact heη
  by_cases hz : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * η + 1 - η
  · have hw : ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ ≤ 2 * A + 2 * η + 1 := by
      have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (e + z)
        - Sandpile.External.Lclt.scaledSite R z) (Sandpile.External.Lclt.scaledSite R z)
      rw [sub_add_cancel] at h
      linarith [h, hdist]
    have hlip := Sandpile.Continuum.abs_cutoff_sub_le A hA
      (Sandpile.External.Lclt.scaledSite R (e + z)) (Sandpile.External.Lclt.scaledSite R z)
    have hb : |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)| ≤ M := hM _ hw
    have hε : |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
        - Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ ε₀ :=
      hε₀ _ (by linarith)
    have hc1 : Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) ≤ 1 :=
      Sandpile.Continuum.cutoff_le_one A _
    have hc0 : 0 ≤ Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) :=
      Sandpile.Continuum.cutoff_nonneg A _
    have hkey : Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z)) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z))
        - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n z)
        = (Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z))
          + Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z) := by ring
    rw [hkey]
    have h1 : |(Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z))|
        ≤ η / A * M := by
      rw [abs_mul, abs_neg]
      have h2 : |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)|
          ≤ η / A := le_trans hlip (div_le_div_of_nonneg_right hdist hA.le)
      calc |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
              - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)|
              * |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)|
          ≤ (η / A) * M := mul_le_mul h2 hb (abs_nonneg _) (by positivity)
        _ = η / A * M := by ring
    have h2 : |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z)| ≤ ε₀ := by
      rw [abs_mul]
      have h3 : |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)| ≤ 1 := by
        rw [abs_of_nonneg hc0]; exact hc1
      have h4 : |-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ ε₀ := by
        rw [show -Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z
            = -(Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              - Frozen.HeatPotentialInvariance.meshValue d R ζ n z) by ring, abs_neg]
        exact hε
      calc |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)|
              * |-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
                + Frozen.HeatPotentialInvariance.meshValue d R ζ n z|
          ≤ 1 * ε₀ := mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
        _ = ε₀ := one_mul ε₀
    have hsum := abs_add_le ((Sandpile.Continuum.cutoff A
            (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)))
          (Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z))
    linarith
  · rw [not_le] at hz
    have hw2A : 2 * A ≤ ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ := by
      have h5 : ‖Sandpile.External.Lclt.scaledSite R z‖
          - ‖Sandpile.External.Lclt.scaledSite R (e + z)‖
          ≤ ‖Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z‖ := by
        have := abs_norm_sub_norm_le (Sandpile.External.Lclt.scaledSite R z)
          (Sandpile.External.Lclt.scaledSite R (e + z))
        rw [abs_le, norm_sub_rev] at this
        linarith [this.2]
      linarith [h5, hdist, hz]
    have hz2A : 2 * A ≤ ‖Sandpile.External.Lclt.scaledSite R z‖ := by linarith
    rw [Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA _ hw2A,
      Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA _ hz2A]
    simp only [zero_mul, sub_zero, abs_zero]
    positivity

set_option maxHeartbeats 1600000 in
/-- **The oscillation of the rescaled odometer between two lattice sites at a fixed
continuum mesh distance,** generalizing `exists_odometer_cell_oscillation` from a
unit lattice step to a continuum separation `η` produced by the theorem itself
(clause 2 of `thm:main-explosion`(i)(b) needs it at an arbitrary, prescribed target
distance, which this `η` may always be taken below). -/
theorem exists_odometer_oscillation_at_distance
    (_hLocalCLT : Sandpile.External.LocalCLT) (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (ρ : ℝ) (hρ : 0 ≤ ρ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η R₀ : ℝ, 0 < η ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      Sandpile.centeredMassLaw d ν
        {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧
          ‖Sandpile.External.Lclt.scaledSite R e‖ ≤ η ∧
          ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
              - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ y|}
        ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨ΩW, mW, PW, hPW, W, hW⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  obtain ⟨hfdd, htight⟩ := Sandpile.Frozen.heat_potential_invariance d (by omega) hd3
    ν hmean hvar hvar' θ₀ hθ₀ hexp PW W hW T hT
  obtain ⟨K, hK, hwenv⟩ := Sandpile.Support.exists_mesh_annulus_bound
    Sandpile.External.heatKernelBounds hd hd3 (θ := 1/2) (by norm_num) (by norm_num)
    ν hmean hθ₀ hexp T hT.le (δ / 4) (by positivity)
  obtain ⟨A₁, hA₁4, hA₁⟩ := Sandpile.exists_walk_cutoff_stoppingSup_gap d hd 1
    (K := K) (T := T) (ε := ε / 4) hK hT (by positivity)
  have hsd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
  -- fix the cutoff radius and the two compact sets using the worst case η ≤ 1
  set ρ' : ℝ := Real.sqrt d * (ρ + 1) + 1 with hρ'def
  have hρ'0 : 0 ≤ ρ' := by rw [hρ'def]; positivity
  set A : ℝ := max A₁ (2 * ρ' + 2) with hAdef
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₁4 (le_max_left _ _)
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hAρ' : 2 * ρ' ≤ A := by
    have := le_max_right A₁ (2 * ρ' + 2)
    rw [← hAdef] at this
    linarith
  set C₁ : Set (ℝ × Sandpile.Continuum.Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall 0 ρ' with hC₁def
  have hC₁c : IsCompact C₁ := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hC₁s : C₁ ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  set C₂ : Set (ℝ × Sandpile.Continuum.Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall 0 (2 * A + 5) with hC₂def
  have hC₂c : IsCompact C₂ := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hC₂s : C₂ ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  obtain ⟨δ₁, hδ₁, hosc₁⟩ := (htight C₁ hC₁c hC₁s).2 (δ / 4) (ε / 8) (by positivity) (by positivity)
  obtain ⟨M₀, hM₀⟩ := (htight C₂ hC₂c hC₂s).1 (δ / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, hosc₂⟩ := (htight C₂ hC₂c hC₂s).2 (δ / 4) (ε / 8) (by positivity) (by positivity)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_right _ _
  have hM : ∀ R : ℝ, 1 ≤ R →
      (Sandpile.centeredMassLaw d ν) {σ | ∃ p ∈ C₂, M < |Frozen.HeatPotentialInvariance.linInterp d R
        (Sandpile.scenery d σ) p.1 p.2|} ≤ ENNReal.ofReal (δ / 4) := by
    intro R hR
    refine le_trans (measure_mono ?_) (hM₀ R hR)
    rintro σ ⟨p, hp, hv⟩
    exact ⟨p, hp, (le_max_left M₀ 0).trans_lt hv⟩
  -- choose the actual separation η, small enough for both moduli of continuity and
  -- for the cutoff's Lipschitz contribution
  set η : ℝ := min 1 (min (δ₁ / 2) (min (δ₂ / 2) (A * ε / (8 * (M + 1))))) with hηdef
  have hη0 : 0 < η := by
    rw [hηdef]
    refine lt_min (by norm_num) (lt_min (by linarith) (lt_min (by linarith) ?_))
    positivity
  have hη1 : η ≤ 1 := le_trans (min_le_left _ _) le_rfl
  have hηδ₁ : η < δ₁ := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _))
    (by linarith)
  have hηδ₂ : η < δ₂ := lt_of_le_of_lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) (by linarith)
  have hηAM : η ≤ A * ε / (8 * (M + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hηAM' : η / A * M ≤ ε / 8 := by
    have hMM1 : M ≤ M + 1 := by linarith
    have hkey : η * (8 * (M + 1)) ≤ A * ε :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 8 * (M + 1))).mp hηAM
    have hstep : η * M ≤ η * (M + 1) := mul_le_mul_of_nonneg_left hMM1 hη0.le
    rw [div_mul_eq_mul_div, div_le_iff₀ hA0]
    nlinarith [hkey, hstep]
  set R₀ : ℝ := max (1 + 1 / T) 1 with hR₀def
  have hR₀0 : 0 < R₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨η, R₀, hη0, hR₀0, ?_⟩
  intro R hR
  have hR1T : 1 + 1 / T ≤ R := (le_max_left _ _).trans hR
  have hR1 : (1 : ℝ) ≤ R := by
    have : (0:ℝ) < 1 / T := by positivity
    linarith
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hTR : (1 : ℝ) ≤ T * R ^ 2 := by
    have h1 : 1 / T ≤ R := by
      have : (0:ℝ) < 1 / T := by positivity
      linarith
    have h2 : R ≤ R ^ 2 := by nlinarith
    have h3 : 1 / T ≤ R ^ 2 := le_trans h1 h2
    rw [div_le_iff₀ hT] at h3
    nlinarith
  have hn1 : 1 ≤ ⌊T * R ^ 2⌋₊ := Nat.le_floor (by exact_mod_cast hTR)
  have hnT : ((⌊T * R ^ 2⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := by
    have h := Nat.floor_le (show (0:ℝ) ≤ T * R ^ 2 by positivity)
    calc ((⌊T * R ^ 2⌋₊ : ℕ) : ℝ) ≤ T * R ^ 2 := h
      _ = R ^ 2 * T := by ring
  obtain ⟨Gw, hGw, hGwenv⟩ := hwenv R hR1
  set badA : Set (Site d → ℝ) := {σ | ∃ p ∈ C₁, ∃ q ∈ C₁, dist p q < δ₁ ∧
    ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
      - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|} with hbadAdef
  set badM : Set (Site d → ℝ) := {σ | ∃ p ∈ C₂, M < |Frozen.HeatPotentialInvariance.linInterp d R
    (Sandpile.scenery d σ) p.1 p.2|} with hbadMdef
  set badB : Set (Site d → ℝ) := {σ | ∃ p ∈ C₂, ∃ q ∈ C₂, dist p q < δ₂ ∧
    ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
      - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|} with hbadBdef
  have hbadA : centeredMassLaw d ν badA ≤ ENNReal.ofReal (δ / 4) := hosc₁ R hR1
  have hbadM : centeredMassLaw d ν badM ≤ ENNReal.ofReal (δ / 4) := hM R hR1
  have hbadB : centeredMassLaw d ν badB ≤ ENNReal.ofReal (δ / 4) := hosc₂ R hR1
  have hsub : {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧
        ‖Sandpile.External.Lclt.scaledSite R e‖ ≤ η ∧
        ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
            - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ y|}
      ⊆ badA ∪ badM ∪ badB ∪ Gwᶜ := by
    rintro σ ⟨y, e, hy, heη, hgt⟩
    by_cases hA' : σ ∈ badA
    · exact Or.inl (Or.inl (Or.inl hA'))
    by_cases hM' : σ ∈ badM
    · exact Or.inl (Or.inl (Or.inr hM'))
    by_cases hB : σ ∈ badB
    · exact Or.inl (Or.inr hB)
    by_cases hG : σ ∈ Gw
    · exfalso
      have hnotA : ¬ (∃ p ∈ C₁, ∃ q ∈ C₁, dist p q < δ₁ ∧
          ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
            - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|) := hA'
      have hnotM : ¬ (∃ p ∈ C₂, M < |Frozen.HeatPotentialInvariance.linInterp d R
          (Sandpile.scenery d σ) p.1 p.2|) := hM'
      have hnotB : ¬ (∃ p ∈ C₂, ∃ q ∈ C₂, dist p q < δ₂ ∧
          ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
            - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|) := hB
      set n : ℕ := ⌊T * R ^ 2⌋₊ with hndef
      have hn1' : 1 ≤ n := hn1
      have hnT' : (n : ℝ) ≤ R ^ 2 * T := hnT
      have hRne : R ≠ 0 := ne_of_gt hR0
      have hnormy : ‖Sandpile.External.Lclt.scaledSite R y‖ ≤ Real.sqrt d * (ρ + 1) := by
        have hc : ∀ i : Fin d, |(Sandpile.External.Lclt.scaledSite R y) i| ≤ ρ + 1 := by
          intro i
          have h1 : |((y i : ℤ) : ℝ)| ≤ R * ρ + 1 := by
            have h2 : (⌈R * ρ⌉₊ : ℝ) ≤ R * ρ + 1 := by
              have h3 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ R * ρ by positivity)
              linarith
            have h4 : |((y i : ℤ) : ℝ)| ≤ (⌈R * ρ⌉₊ : ℝ) := by
              have h5 : ((|y i| : ℤ) : ℝ) ≤ ((⌈R * ρ⌉ : ℤ) : ℝ) := by exact_mod_cast hy i
              rw [Int.cast_abs] at h5
              have h6 : ((⌈R * ρ⌉ : ℤ) : ℝ) ≤ (⌈R * ρ⌉₊ : ℝ) := by
                have h7 : ⌈R * ρ⌉ ≤ (⌈R * ρ⌉₊ : ℤ) := Int.ceil_le.mpr (Nat.le_ceil (R * ρ))
                exact_mod_cast h7
              linarith
            linarith
          have h2 : (Sandpile.External.Lclt.scaledSite R y) i = ((y i : ℤ) : ℝ) / R := rfl
          rw [h2, abs_div, abs_of_pos hR0]
          rw [div_le_iff₀ hR0]
          nlinarith [abs_nonneg ((y i : ℤ) : ℝ), h1, hR1, hρ]
        exact Sandpile.Continuum.norm_le_of_coord_le (v := Sandpile.External.Lclt.scaledSite R y)
          (by positivity : (0:ℝ) ≤ ρ + 1) hc
      have hyρ' : ‖Sandpile.External.Lclt.scaledSite R y‖ ≤ ρ' := by
        rw [hρ'def]; nlinarith [hnormy]
      have hdist1 : ‖Sandpile.External.Lclt.scaledSite R (y + e)
          - Sandpile.External.Lclt.scaledSite R y‖ ≤ η := by
        rw [Sandpile.scaledSite_add, add_sub_cancel_left]; exact heη
      have hyeρ' : ‖Sandpile.External.Lclt.scaledSite R (y + e)‖ ≤ ρ' := by
        have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (y + e)
          - Sandpile.External.Lclt.scaledSite R y) (Sandpile.External.Lclt.scaledSite R y)
        rw [sub_add_cancel] at h
        rw [hρ'def]
        nlinarith [h, hdist1, hnormy, hη1]
      have hnR2T : (n : ℝ) / R ^ 2 ≤ T := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < R ^ 2)]
        calc (n : ℝ) ≤ R ^ 2 * T := hnT'
          _ = T * R ^ 2 := by ring
      have hnR20 : (0 : ℝ) ≤ (n : ℝ) / R ^ 2 := by positivity
      have hp1 : (((n : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R (y + e)) : ℝ × _) ∈ C₁ :=
        ⟨⟨hnR20, hnR2T⟩, by
          simp only [Metric.mem_closedBall, dist_zero_right]; exact hyeρ'⟩
      have hq1 : (((n : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R y) : ℝ × _) ∈ C₁ :=
        ⟨⟨hnR20, hnR2T⟩, by
          simp only [Metric.mem_closedBall, dist_zero_right]; exact hyρ'⟩
      have hdistpq : dist (((n : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R (y + e)) : ℝ × _)
          (((n : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R y) : ℝ × _) < δ₁ := by
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
        simp only
        exact lt_of_le_of_lt hdist1 hηδ₁
      have hE₀ : |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) n (y + e)
          - Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) n y| ≤ ε / 8 := by
        have h := le_of_not_gt (fun hlt => hnotA ⟨_, hp1, _, hq1, hdistpq, hlt⟩)
        simp only at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n 0 (Nat.zero_le n) (y + e)
        have h2 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n 0 (Nat.zero_le n) y
        simp only [Nat.cast_zero, sub_zero] at h1 h2
        rwa [h1, h2] at h
      have hMb : ∀ k : ℕ, k ≤ n → ∀ z : Site d,
          ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * η + 1 →
          |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z| ≤ M := by
        intro k hk z hz
        have hzC₂ : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 5 := by
          nlinarith [hη1]
        have hnkT : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ T := by
          have h1 : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.sub_le n k
          have h2 : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ (n : ℝ) / R ^ 2 :=
            div_le_div_of_nonneg_right h1 (by positivity)
          linarith [hnR2T]
        have hnk0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) / R ^ 2 := by positivity
        have hp : ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R z) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hzC₂⟩
        have h := le_of_not_gt (fun hlt => hnotM ⟨_, hp, hlt⟩)
        simp only at h
        rw [show ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) from Nat.cast_sub hk] at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk z
        rwa [h1] at h
      have hε₀b : ∀ k : ℕ, k ≤ n → ∀ z : Site d,
          ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * η + 1 →
          |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) (e + z)
            - Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z| ≤ ε / 8 := by
        intro k hk z hz
        have hzC₂ : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 5 := by
          nlinarith [hη1]
        have hdistz : ‖Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z‖ ≤ η := by
          rw [Sandpile.scaledSite_add, add_sub_cancel_right]; exact heη
        have hezC₂ : ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ ≤ 2 * A + 5 := by
          have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z) (Sandpile.External.Lclt.scaledSite R z)
          rw [sub_add_cancel] at h
          nlinarith [h, hdistz, hz, hη1]
        have hnkT : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ T := by
          have h1 : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
          have h2 : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ (n : ℝ) / R ^ 2 :=
            div_le_div_of_nonneg_right h1 (by positivity)
          linarith [hnR2T]
        have hnk0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) / R ^ 2 := by positivity
        have hp : ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R (e + z)) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hezC₂⟩
        have hq : ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R z) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hzC₂⟩
        have hdistpq : dist ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R (e + z)) : ℝ × _)
            ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R z) : ℝ × _) < δ₂ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
          simp only
          exact lt_of_le_of_lt hdistz hηδ₂
        have h := le_of_not_gt (fun hlt => hnotB ⟨_, hp, _, hq, hdistpq, hlt⟩)
        simp only at h
        rw [show ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) from Nat.cast_sub hk] at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk (e + z)
        have h2 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk z
        rwa [h1, h2] at h
      set G : ℕ → Site d → ℝ := fun k z =>
        -(Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z) with hGdef
      set F : ℕ → (ℕ → Site d) → ℝ := fun k X => G k (X k) with hFdef
      set Gχ : ℕ → (ℕ → Site d) → ℝ := fun k X =>
        Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (X k)) * F k X with hGχdef
      have hE₁ : |Sandpile.stoppingSup n y F - Sandpile.stoppingSup n y Gχ| ≤ ε / 4 := by
        refine hA₁ A (le_max_left _ _) R hR1 y ρ' hρ'0 hyρ' hAρ' n hn1' hnT'
          F (fun τ hτ hτn => Sandpile.measurable_stopped_value n G hτ hτn) ?_
          (Sandpile.bddAbove_walk_stopped_value hd y n G)
          (Sandpile.bddAbove_walk_stopped_value hd y n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z))
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd y n G hτ hτn)
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd y n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z)
            hτ hτn)
        intro τ hτn X j hj
        have h := hGwenv σ hG A hA1 n hnT' τ hτn X j hj
        simpa only [hGdef] using h
      have hE₁' : |Sandpile.stoppingSup n (y + e) F - Sandpile.stoppingSup n (y + e) Gχ| ≤ ε / 4 := by
        refine hA₁ A (le_max_left _ _) R hR1 (y + e) ρ' hρ'0 hyeρ' hAρ' n hn1' hnT'
          F (fun τ hτ hτn => Sandpile.measurable_stopped_value n G hτ hτn) ?_
          (Sandpile.bddAbove_walk_stopped_value hd (y + e) n G)
          (Sandpile.bddAbove_walk_stopped_value hd (y + e) n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z))
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd (y + e) n G hτ hτn)
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd (y + e) n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z)
            hτ hτn)
        intro τ hτn X j hj
        have h := hGwenv σ hG A hA1 n hnT' τ hτn X j hj
        simpa only [hGdef] using h
      have hE₂ : |Sandpile.stoppingSup n (y + e) Gχ - Sandpile.stoppingSup n y Gχ| ≤ ε / 4 := by
        refine Sandpile.abs_stoppingSup_translate_sub_le hd n y e
          (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z))
          (ε / 4) (fun k hk z => ?_)
        have h := Sandpile.abs_cutoff_meshValue_translate_sub_le_of_dist hd R hR1 A hA0
          (Sandpile.scenery d σ) (n - k) e η hη0.le heη M (ε / 8) hM0 (by positivity)
          (fun w hw => hMb k hk w hw) (fun w hw => hε₀b k hk w hw) z
        linarith [h, hηAM']
      have hb := Sandpile.abs_rescaled_odometer_translate_sub_le hd R hR0 (Sandpile.scenery d σ) n y e
        Gχ (ε / 8) (ε / 4) (ε / 4) (ε / 4) hE₀ hE₁ hE₁' hE₂
      have : ¬ (ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) n (y + e)
          - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) n y|) := by
        intro hlt
        have hsum : ε / 8 + ε / 4 + ε / 4 + ε / 4 < ε := by linarith
        linarith [hb, hsum]
      exact this hgt
    · exact Or.inr hG
  calc centeredMassLaw d ν {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧
        ‖Sandpile.External.Lclt.scaledSite R e‖ ≤ η ∧
        ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
            - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ y|}
      ≤ centeredMassLaw d ν (badA ∪ badM ∪ badB ∪ Gwᶜ) := measure_mono hsub
    _ ≤ centeredMassLaw d ν (badA ∪ badM ∪ badB) + centeredMassLaw d ν Gwᶜ :=
        measure_union_le _ _
    _ ≤ (centeredMassLaw d ν (badA ∪ badM) + centeredMassLaw d ν badB) + centeredMassLaw d ν Gwᶜ := by
        gcongr
        exact measure_union_le _ _
    _ ≤ ((centeredMassLaw d ν badA + centeredMassLaw d ν badM) + centeredMassLaw d ν badB)
          + centeredMassLaw d ν Gwᶜ := by
        gcongr
        exact measure_union_le _ _
    _ ≤ ((ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4)) + ENNReal.ofReal (δ / 4))
          + ENNReal.ofReal (δ / 4) := by
        gcongr
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Sandpile
