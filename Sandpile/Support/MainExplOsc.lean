import Sandpile.Support.MainExplWalkValue
import Sandpile.Support.ExplStability
import Sandpile.Support.D4CritStationary
import Sandpile.Support.KillBox
import Sandpile.Support.ExplCutoff
import Sandpile.Continuum.WhiteNoiseExists
import Sandpile.Frozen.HeatPotentialInvariance
import Sandpile.Support.MainExplAnnulus
import Sandpile.Support.ExplWalkCutoff
import Sandpile.External.HeatKernelBoundsProved

/-!
# The walk value at a translated starting site, and the oscillation of the odometer

This proves the remaining estimate needed for the odometer's parabolic scaling limit: the
oscillation of the rescaled odometer between two nearby lattice sites at unit lattice
separation. The exact identity splitting the rescaled odometer at a site into the interpolated
field there plus the walk value there reduces this to the field's oscillation, which is an
equicontinuity clause supplied elsewhere, and to the walk value's dependence on its starting
site. On the lattice, unlike for Brownian motion, the walk started at `x + y` is exactly the
walk started at `x` translated by `y`, so the value at `x + y` is the value at `x` evaluated at
the translated reward, and since the value is `1`-Lipschitz in the reward, translating the
starting site moves the value by at most the oscillation of the reward under that translation.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The walk value at a translated starting site is the value at the translated
reward.**  The walk started at `x + y` is the walk started at `x` translated by `y`,
and translating carries the stopping times of the one to the stopping times of the
other, so the two suprema are over the same set of reals. -/
theorem stoppingSup_translate (n : ℕ) (x y : Site d) (F : ℕ → (ℕ → Site d) → ℝ) :
    Sandpile.stoppingSup n (x + y) F
      = Sandpile.stoppingSup n x (fun k X => F k fun j => y + X j) := by
  classical
  unfold Sandpile.stoppingSup
  congr 1
  have hshift : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ →
      IsWalkStopping fun X => τ fun j => y + X j := by
    intro τ hτ k X Y hXY hk
    exact hτ k (fun j => y + X j) (fun j => y + Y j) (fun j hj => by rw [hXY j hj]) hk
  have hint : ∀ (τ : (ℕ → Site d) → ℕ),
      ∫ X, F (τ X) X ∂(Sandpile.walkLaw d (x + y))
        = ∫ X, F (τ fun j => y + X j) (fun j => y + X j) ∂(Sandpile.walkLaw d x) :=
    fun τ => ((Sandpile.measurePreserving_pathTranslate x y).integral_comp'
      (fun X => F (τ X) X)).symm
  ext a
  constructor
  · rintro ⟨τ, hτ, hτn, rfl⟩
    exact ⟨fun X => τ fun j => y + X j, hshift τ hτ, fun X => hτn _, hint τ⟩
  · rintro ⟨σ, hσ, hσn, rfl⟩
    refine ⟨fun X => σ fun j => -y + X j, ?_, fun X => hσn _, ?_⟩
    · intro k X Y hXY hk
      exact hσ k (fun j => -y + X j) (fun j => -y + Y j) (fun j hj => by rw [hXY j hj]) hk
    · rw [hint fun X => σ fun j => -y + X j]
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [neg_add_cancel_left]

/-- **The walk value moves by at most the oscillation of its reward under the
translation.**  For a reward that reads the walk through its position at the stopping
time, moving the starting site by `y` moves the value by at most the sup-norm distance
between the reward and its translate, over the times below the horizon.  This is the
lattice counterpart of a continuity in the starting point, and the Brownian side has no
counterpart at all: `IsBrownian` relates the motions started at two points in no way. -/
theorem abs_stoppingSup_translate_sub_le (hd : 1 ≤ d) (n : ℕ) (x y : Site d)
    (f : ℕ → Site d → ℝ) (E : ℝ)
    (hfE : ∀ k, k ≤ n → ∀ z : Site d, |f k (y + z) - f k z| ≤ E) :
    |Sandpile.stoppingSup n (x + y) (fun k X => f k (X k))
        - Sandpile.stoppingSup n x (fun k X => f k (X k))| ≤ E := by
  rw [stoppingSup_translate n x y fun k X => f k (X k)]
  exact Sandpile.abs_stoppingSup_sub_le_of_reward hd n x
    (fun k X => f k (y + X k)) (fun k X => f k (X k)) E
    (Sandpile.bddAbove_walk_stopped_value hd x n fun k z => f k (y + z))
    (Sandpile.bddAbove_walk_stopped_value hd x n f)
    (fun τ hτ hτn =>
      Sandpile.integrable_stopped_value hd x n (fun k z => f k (y + z)) hτ hτn)
    (fun τ hτ hτn => Sandpile.integrable_stopped_value hd x n f hτ hτn)
    (fun k hk X => hfE k hk (X k))

/-- **The oscillation of the rescaled odometer between two lattice sites, in four
named errors.**  The exact identity of `sandpile.tex:1881-1890` writes the rescaled
odometer at a site as the mesh field there plus the walk value there, so the difference
between two sites is the oscillation of the field, plus the two cutoff errors that replace
the unbounded reward by a cut-off one at each site, plus the oscillation of the walk value
at the CUT-OFF reward, which `abs_stoppingSup_translate_sub_le` bounds by the oscillation of
that reward under the translation.  Nothing here is assumed about how the four errors are
obtained; each is supplied by a named result of the paper, the first and the last by the
equicontinuity clause of `prop:dlt4-heat-potential-invariance` and the two middle ones by
`Sandpile.exists_walk_cutoff_stoppingSup_gap`. -/
theorem abs_rescaled_odometer_translate_sub_le (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R)
    (ζ : Site d → ℝ) (t : ℕ) (y e : Site d)
    (Fχ : ℕ → (ℕ → Site d) → ℝ) (E₀ E₁ E₁' E₂ : ℝ)
    (hfield : |Frozen.HeatPotentialInvariance.meshValue d R ζ t (y + e)
        - Frozen.HeatPotentialInvariance.meshValue d R ζ t y| ≤ E₀)
    (hcut : |Sandpile.stoppingSup t y
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - Sandpile.stoppingSup t y Fχ| ≤ E₁)
    (hcut' : |Sandpile.stoppingSup t (y + e)
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - Sandpile.stoppingSup t (y + e) Fχ| ≤ E₁')
    (htr : |Sandpile.stoppingSup t (y + e) Fχ - Sandpile.stoppingSup t y Fχ| ≤ E₂) :
    |R ^ ((d : ℝ) / 2 - 2) * odometerOf ζ t (y + e)
        - R ^ ((d : ℝ) / 2 - 2) * odometerOf ζ t y| ≤ E₀ + E₁ + E₁' + E₂ := by
  rw [rescaled_difference_representation hd R hR ζ t (y + e),
    rescaled_difference_representation hd R hR ζ t y]
  set A := Frozen.HeatPotentialInvariance.meshValue d R ζ t (y + e)
  set A' := Frozen.HeatPotentialInvariance.meshValue d R ζ t y
  set S := Sandpile.stoppingSup t (y + e)
    (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
  set S' := Sandpile.stoppingSup t y
    (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
  set C := Sandpile.stoppingSup t (y + e) Fχ
  set C' := Sandpile.stoppingSup t y Fχ
  have hsplit : A + S - (A' + S') = (A - A') + (S - C) + (C - C') + (C' - S') := by ring
  rw [hsplit]
  have h2 : |C' - S'| ≤ E₁ := by rw [abs_sub_comm]; exact hcut
  have h3 : |S - C| ≤ E₁' := hcut'
  have hb1 := abs_le.mp hfield
  have hb2 := abs_le.mp h3
  have hb3 := abs_le.mp htr
  have hb4 := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hb4.1, hb4.2]

namespace Continuum

/-- The cutoff `χ_A` is `1/A`-Lipschitz. -/
theorem abs_cutoff_sub_le (A : ℝ) (hA : 0 < A) (w w' : Space d) :
    |cutoff A w - cutoff A w'| ≤ ‖w - w'‖ / A := by
  rw [Sandpile.Continuum.cutoff]
  have hA0 : (0 : ℝ) ≤ A := le_of_lt hA
  have key : ∀ u v : ℝ, |min 1 u - min 1 v| ≤ |u - v| := by
    intro u v
    rcases le_total u v with huv | huv
    · have h1 : min 1 u ≤ min 1 v := min_le_min le_rfl huv
      rw [abs_of_nonpos (sub_nonpos.mpr h1), abs_of_nonpos (sub_nonpos.mpr huv)]
      rcases le_total v 1 with hv | hv
      · have hu' : min 1 u = u := min_eq_right (le_trans huv hv)
        have hv' : min 1 v = v := min_eq_right hv
        linarith
      · rcases le_total u 1 with hu | hu
        · have hu' : min 1 u = u := min_eq_right hu
          have hv' : min 1 v = 1 := min_eq_left hv
          linarith
        · have hu' : min 1 u = 1 := min_eq_left hu
          have hv' : min 1 v = 1 := min_eq_left hv
          linarith
    · have h1 : min 1 v ≤ min 1 u := min_le_min le_rfl huv
      rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr huv)]
      rcases le_total u 1 with hu | hu
      · have hu' : min 1 u = u := min_eq_right hu
        have hv' : min 1 v = v := min_eq_right (le_trans huv hu)
        linarith
      · rcases le_total v 1 with hv | hv
        · have hu' : min 1 u = 1 := min_eq_left hu
          have hv' : min 1 v = v := min_eq_right hv
          linarith
        · have hu' : min 1 u = 1 := min_eq_left hu
          have hv' : min 1 v = 1 := min_eq_left hv
          linarith
  have key2 : ∀ u v : ℝ, |max 0 u - max 0 v| ≤ |u - v| := by
    intro u v
    rcases le_total u v with huv | huv
    · have h1 : max 0 u ≤ max 0 v := max_le_max le_rfl huv
      rw [abs_of_nonpos (sub_nonpos.mpr h1), abs_of_nonpos (sub_nonpos.mpr huv)]
      rcases le_total 0 u with hu | hu
      · have hu' : max 0 u = u := max_eq_right hu
        have hv' : max 0 v = v := max_eq_right (le_trans hu huv)
        linarith
      · rcases le_total 0 v with hv | hv
        · have hu' : max 0 u = 0 := max_eq_left hu
          have hv' : max 0 v = v := max_eq_right hv
          linarith
        · have hu' : max 0 u = 0 := max_eq_left hu
          have hv' : max 0 v = 0 := max_eq_left hv
          linarith
    · have h1 : max 0 v ≤ max 0 u := max_le_max le_rfl huv
      rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonneg (sub_nonneg.mpr huv)]
      rcases le_total 0 v with hv | hv
      · have hu' : max 0 u = u := max_eq_right (le_trans hv huv)
        have hv' : max 0 v = v := max_eq_right hv
        linarith
      · rcases le_total 0 u with hu | hu
        · have hu' : max 0 u = u := max_eq_right hu
          have hv' : max 0 v = 0 := max_eq_left hv
          linarith
        · have hu' : max 0 u = 0 := max_eq_left hu
          have hv' : max 0 v = 0 := max_eq_left hv
          linarith
  calc |min 1 (max 0 (2 - ‖w‖ / A)) - min 1 (max 0 (2 - ‖w'‖ / A))|
      ≤ |max 0 (2 - ‖w‖ / A) - max 0 (2 - ‖w'‖ / A)| := key _ _
    _ ≤ |(2 - ‖w‖ / A) - (2 - ‖w'‖ / A)| := key2 _ _
    _ = |‖w'‖ - ‖w‖| / A := by
        rw [show (2 - ‖w‖ / A) - (2 - ‖w'‖ / A) = (‖w'‖ - ‖w‖) / A by ring]
        rw [abs_div, abs_of_pos hA]
    _ ≤ ‖w - w'‖ / A :=
        div_le_div_of_nonneg_right
          (by simpa [norm_sub_rev] using abs_norm_sub_norm_le w' w) hA0


end Continuum

/-- **The oscillation of the cutoff-weighted mesh field between two lattice sites at unit
lattice separation.** The cutoff factor changes by at most its Lipschitz constant `1/A` times
the continuum-scaled separation `√d/R`, and the mesh field itself changes by at most `ε₀`;
splitting the difference of the two products along these two changes bounds it by
`√d/(RA) · M + ε₀`. -/
theorem abs_cutoff_meshValue_translate_sub_le
    (hd : 1 ≤ d) (R : ℝ) (hR : 1 ≤ R) (A : ℝ) (hA : 0 < A)
    (ζ : Site d → ℝ) (n : ℕ) (e : Site d) (he : ∀ i, |e i| ≤ 1)
    (M ε₀ : ℝ) (hM0 : 0 ≤ M) (hε₀0 : 0 ≤ ε₀)
    (hM : ∀ z : Site d, ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * Real.sqrt d + 1 →
      |Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ M)
    (hε₀ : ∀ z : Site d, ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * Real.sqrt d + 1 →
      |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
        - Frozen.HeatPotentialInvariance.meshValue d R ζ n z| ≤ ε₀) :
    ∀ z : Site d,
      |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z)) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z))
        - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
          (-Frozen.HeatPotentialInvariance.meshValue d R ζ n z)|
      ≤ Real.sqrt d / (R * A) * M + ε₀ := by
  intro z
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hsd0 : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hdist : ‖Sandpile.External.Lclt.scaledSite R (e + z)
      - Sandpile.External.Lclt.scaledSite R z‖ ≤ Real.sqrt d / R := by
    have h := Sandpile.norm_scaledSite_sub_le (m := 1) hR0 (e + z) z (by norm_num)
      (fun i => by
        have hcast : (((e + z) i : ℤ) : ℝ) - ((z i : ℤ) : ℝ) = (e i : ℝ) := by
          simp only [Pi.add_apply]
          push_cast
          ring
        rw [hcast]
        exact_mod_cast he i)
    simpa using h
  have hdiv : Real.sqrt d / R ≤ Real.sqrt d := div_le_self hsd0 hR
  by_cases hz : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * Real.sqrt d + 1 - Real.sqrt d
  · have hw : ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ ≤ 2 * A + 2 * Real.sqrt d + 1 := by
      have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (e + z)
        - Sandpile.External.Lclt.scaledSite R z) (Sandpile.External.Lclt.scaledSite R z)
      rw [sub_add_cancel] at h
      have h2 : ‖Sandpile.External.Lclt.scaledSite R (e + z)
          - Sandpile.External.Lclt.scaledSite R z‖ ≤ Real.sqrt d := le_trans hdist hdiv
      linarith
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
        ≤ Real.sqrt d / (R * A) * M := by
      rw [abs_mul, abs_neg]
      have h2 : |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)|
          ≤ Real.sqrt d / (R * A) := by
        refine le_trans hlip ?_
        refine le_trans (div_le_div_of_nonneg_right hdist hA.le) ?_
        rw [div_div]
      calc |Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
              - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)|
              * |Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)|
          ≤ (Real.sqrt d / (R * A)) * M :=
            mul_le_mul h2 hb (abs_nonneg _) (by positivity)
        _ = Real.sqrt d / (R * A) * M := by ring
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
    have hsum := abs_add_le
          ((Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R (e + z))
            - Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z)) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)))
          (Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R ζ n (e + z)
              + Frozen.HeatPotentialInvariance.meshValue d R ζ n z))
    linarith
  · rw [not_le] at hz
    have hw2A : 2 * A ≤ ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ := by
      have h2 : ‖Sandpile.External.Lclt.scaledSite R (e + z)
          - Sandpile.External.Lclt.scaledSite R z‖ ≤ Real.sqrt d := le_trans hdist hdiv
      have h5 : ‖Sandpile.External.Lclt.scaledSite R z‖
          - ‖Sandpile.External.Lclt.scaledSite R (e + z)‖
          ≤ ‖Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z‖ := by
        have := abs_norm_sub_norm_le (Sandpile.External.Lclt.scaledSite R z)
          (Sandpile.External.Lclt.scaledSite R (e + z))
        rw [abs_le, norm_sub_rev] at this
        linarith [this.2]
      linarith [h5, h2, hz]
    have hz2A : 2 * A ≤ ‖Sandpile.External.Lclt.scaledSite R z‖ := by linarith
    rw [Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA _ hw2A,
      Sandpile.Continuum.cutoff_eq_zero_of_norm_ge A hA _ hz2A]
    simp only [zero_mul, sub_zero, abs_zero]
    positivity

set_option maxHeartbeats 1600000 in
/-- **The oscillation of the rescaled odometer between two lattice sites at unit lattice
separation `e`,** the estimate clause 1 of `thm:main-explosion`(i)(b) needs: with probability
at least `1 - δ`, the difference `R^(d/2-2)(u_{⌊TR²⌋}(y+e) - u_{⌊TR²⌋}(y))` stays below any
prescribed accuracy `ε`, uniformly over `y` in a box of radius `⌈Rρ⌉` and `e` with `|e_i| ≤ 1`,
once the scale `R` is large enough. -/
theorem exists_odometer_cell_oscillation
    (_hLocalCLT : Sandpile.External.LocalCLT) (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (ρ : ℝ) (hρ : 0 ≤ ρ) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      Sandpile.centeredMassLaw d ν
        {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧ (∀ i, |e i| ≤ 1) ∧
          ε < |R ^ ((d : ℝ) / 2 - 2) *
                Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
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
  set ρ' : ℝ := (ρ + 1) * (Real.sqrt d + 1) + Real.sqrt d with hρ'def
  have hρ'0 : 0 ≤ ρ' := by rw [hρ'def]; positivity
  set A : ℝ := max A₁ (2 * ρ' + 1) with hAdef
  have hA0 : (0 : ℝ) < A := by
    rw [hAdef]; exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hA4 : (4 : ℝ) ≤ A := le_trans hA₁4 (le_max_left _ _)
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hAρ' : 2 * ρ' ≤ A := le_trans (by linarith) (le_max_right _ _)
  set C₁ : Set (ℝ × Sandpile.Continuum.Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall 0 ρ' with hC₁def
  have hC₁c : IsCompact C₁ := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hC₁s : C₁ ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  set C₂ : Set (ℝ × Sandpile.Continuum.Space d) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall 0 (2 * A + 3 * Real.sqrt d + 1) with hC₂def
  have hC₂c : IsCompact C₂ := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hC₂s : C₂ ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) :=
    fun _ h => ⟨h.1, Set.mem_univ _⟩
  obtain ⟨δ₁, hδ₁, hosc₁⟩ := (htight C₁ hC₁c hC₁s).2 (δ / 4) (ε / 8) (by positivity) (by positivity)
  obtain ⟨M₀, hM₀⟩ := (htight C₂ hC₂c hC₂s).1 (δ / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, hosc₂⟩ := (htight C₂ hC₂c hC₂s).2 (δ / 4) (ε / 8) (by positivity) (by positivity)
  set M : ℝ := max M₀ 0 with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_right _ _
  have hM : ∀ R : ℝ, 1 ≤ R →
      (Sandpile.centeredMassLaw d ν)
        {σ | ∃ p ∈ C₂, M < |Frozen.HeatPotentialInvariance.linInterp d R
          (Sandpile.scenery d σ) p.1 p.2|} ≤ ENNReal.ofReal (δ / 4) := by
    intro R hR
    refine le_trans (measure_mono ?_) (hM₀ R hR)
    rintro σ ⟨p, hp, hv⟩
    exact ⟨p, hp, (le_max_left M₀ 0).trans_lt hv⟩
  have hsd0 : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsd1 : (1 : ℝ) ≤ Real.sqrt d := by
    have h : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    calc (1:ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt d := Real.sqrt_le_sqrt h
  set R₀ : ℝ := max (1 + 1 / T) (max (2 * Real.sqrt d / δ₁) (max (2 * Real.sqrt d / δ₂)
    (max (8 * Real.sqrt d * M / (A * ε)) 1))) with hR₀def
  have hR₀0 : 0 < R₀ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨R₀, hR₀0, ?_⟩
  intro R hR
  have hR1T : 1 + 1 / T ≤ R := (le_max_left _ _).trans hR
  have hR1 : (1 : ℝ) ≤ R := by
    have : (0:ℝ) < 1 / T := by positivity
    linarith
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hRδ₁ : 2 * Real.sqrt d / δ₁ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRδ₂ : 2 * Real.sqrt d / δ₂ ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hRM : 8 * Real.sqrt d * M / (A * ε) ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hR)))
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
  have hsub : {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧ (∀ i, |e i| ≤ 1) ∧
        ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
            - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ y|}
      ⊆ badA ∪ badM ∪ badB ∪ Gwᶜ := by
    rintro σ ⟨y, e, hy, he, hgt⟩
    by_cases hA : σ ∈ badA
    · exact Or.inl (Or.inl (Or.inl hA))
    by_cases hM' : σ ∈ badM
    · exact Or.inl (Or.inl (Or.inr hM'))
    by_cases hB : σ ∈ badB
    · exact Or.inl (Or.inr hB)
    by_cases hG : σ ∈ Gw
    · exfalso
      have hnotA : ¬ (∃ p ∈ C₁, ∃ q ∈ C₁, dist p q < δ₁ ∧
          ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
            - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|) := hA
      have hnotM : ¬ (∃ p ∈ C₂, M < |Frozen.HeatPotentialInvariance.linInterp d R
          (Sandpile.scenery d σ) p.1 p.2|) := hM'
      have hnotB : ¬ (∃ p ∈ C₂, ∃ q ∈ C₂, dist p q < δ₂ ∧
          ε / 8 < |Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) p.1 p.2
            - Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1 q.2|) := hB
      set n : ℕ := ⌊T * R ^ 2⌋₊ with hndef
      have hn1' : 1 ≤ n := hn1
      have hnT' : (n : ℝ) ≤ R ^ 2 * T := hnT
      have hRne : R ≠ 0 := ne_of_gt hR0
      -- membership of the two mesh points in C₁
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
        rw [hρ'def]; nlinarith [hnormy, hsd0, hρ]
      have hdist1 : ‖Sandpile.External.Lclt.scaledSite R (y + e)
          - Sandpile.External.Lclt.scaledSite R y‖ ≤ Real.sqrt d / R := by
        have h := Sandpile.norm_scaledSite_sub_le (m := 1) hR0 (y + e) y (by norm_num)
          (fun i => by
            have hcast : (((y + e) i : ℤ) : ℝ) - ((y i : ℤ) : ℝ) = (e i : ℝ) := by
              simp only [Pi.add_apply]; push_cast; ring
            rw [hcast]
            exact_mod_cast he i)
        simpa using h
      have hsdR : Real.sqrt d / R ≤ Real.sqrt d := div_le_self hsd0 hR1
      have hyeρ' : ‖Sandpile.External.Lclt.scaledSite R (y + e)‖ ≤ ρ' := by
        have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (y + e)
          - Sandpile.External.Lclt.scaledSite R y) (Sandpile.External.Lclt.scaledSite R y)
        rw [sub_add_cancel] at h
        have h2 : Real.sqrt d * (ρ + 1) ≤ ρ' - Real.sqrt d := by
          rw [hρ'def]; nlinarith [hsd0, hρ]
        have h3 : ‖Sandpile.External.Lclt.scaledSite R y‖ ≤ ρ' - Real.sqrt d := le_trans hnormy h2
        linarith [h, hdist1, hsdR, h3]
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
        have h2 : Real.sqrt d / R ≤ δ₁ / 2 := by
          rw [div_le_iff₀ hδ₁] at hRδ₁
          rw [div_le_iff₀ hR0]
          nlinarith [hRδ₁, hδ₁]
        linarith [hdist1, h2, hδ₁]
      have hE₀ : |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) n (y + e)
          - Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) n y| ≤ ε / 8 := by
        have h := le_of_not_gt (fun hlt => hnotA ⟨_, hp1, _, hq1, hdistpq, hlt⟩)
        simp only at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n 0
          (Nat.zero_le n) (y + e)
        have h2 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n 0 (Nat.zero_le n) y
        simp only [Nat.cast_zero, sub_zero] at h1 h2
        rwa [h1, h2] at h
      -- the M and ε₀ bounds
      have hMb : ∀ k : ℕ, k ≤ n → ∀ z : Site d,
          ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * Real.sqrt d + 1 →
          |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z| ≤ M := by
        intro k hk z hz
        have hzC₂ : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 3 * Real.sqrt d + 1 := by
          linarith [hsd0]
        have hnkT : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ T := by
          have h1 : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast Nat.sub_le n k
          have h2 : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ (n : ℝ) / R ^ 2 :=
            div_le_div_of_nonneg_right h1 (by positivity)
          linarith [hnR2T]
        have hnk0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) / R ^ 2 := by positivity
        have hp : ((((n - k : ℕ) : ℝ) / R ^ 2,
              Sandpile.External.Lclt.scaledSite R z) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hzC₂⟩
        have h := le_of_not_gt (fun hlt => hnotM ⟨_, hp, hlt⟩)
        simp only at h
        rw [show ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) from Nat.cast_sub hk] at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk z
        rwa [h1] at h
      have hε₀b : ∀ k : ℕ, k ≤ n → ∀ z : Site d,
          ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 2 * Real.sqrt d + 1 →
          |Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) (e + z)
            - Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z|
              ≤ ε / 8 := by
        intro k hk z hz
        have hzC₂ : ‖Sandpile.External.Lclt.scaledSite R z‖ ≤ 2 * A + 3 * Real.sqrt d + 1 := by
          linarith [hsd0]
        have hdistz : ‖Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z‖ ≤ Real.sqrt d / R := by
          have h := Sandpile.norm_scaledSite_sub_le (m := 1) hR0 (e + z) z (by norm_num)
            (fun i => by
              have hcast : (((e + z) i : ℤ) : ℝ) - ((z i : ℤ) : ℝ) = (e i : ℝ) := by
                simp only [Pi.add_apply]; push_cast; ring
              rw [hcast]
              exact_mod_cast he i)
          simpa using h
        have hezC₂ :
            ‖Sandpile.External.Lclt.scaledSite R (e + z)‖ ≤ 2 * A + 3 * Real.sqrt d + 1 := by
          have h := norm_add_le (Sandpile.External.Lclt.scaledSite R (e + z)
            - Sandpile.External.Lclt.scaledSite R z) (Sandpile.External.Lclt.scaledSite R z)
          rw [sub_add_cancel] at h
          linarith [h, hdistz, hsdR]
        have hnkT : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ T := by
          have h1 : ((n - k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n k
          have h2 : ((n - k : ℕ) : ℝ) / R ^ 2 ≤ (n : ℝ) / R ^ 2 :=
            div_le_div_of_nonneg_right h1 (by positivity)
          linarith [hnR2T]
        have hnk0 : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) / R ^ 2 := by positivity
        have hp : ((((n - k : ℕ) : ℝ) / R ^ 2,
              Sandpile.External.Lclt.scaledSite R (e + z)) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hezC₂⟩
        have hq : ((((n - k : ℕ) : ℝ) / R ^ 2,
              Sandpile.External.Lclt.scaledSite R z) : ℝ × _) ∈ C₂ :=
          ⟨⟨hnk0, hnkT⟩, by simp only [Metric.mem_closedBall, dist_zero_right]; exact hzC₂⟩
        have hdistpq :
            dist ((((n - k : ℕ) : ℝ) / R ^ 2,
                  Sandpile.External.Lclt.scaledSite R (e + z)) : ℝ × _)
              ((((n - k : ℕ) : ℝ) / R ^ 2, Sandpile.External.Lclt.scaledSite R z) : ℝ × _)
              < δ₂ := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm]
          simp only
          have h2 : Real.sqrt d / R ≤ δ₂ / 2 := by
            rw [div_le_iff₀ hδ₂] at hRδ₂
            rw [div_le_iff₀ hR0]
            nlinarith [hRδ₂, hδ₂]
          linarith [hdistz, h2, hδ₂]
        have h := le_of_not_gt (fun hlt => hnotB ⟨_, hp, _, hq, hdistpq, hlt⟩)
        simp only at h
        rw [show ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) from Nat.cast_sub hk] at h
        have h1 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk (e + z)
        have h2 := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) n k hk z
        rwa [h1, h2] at h
      -- the cutoff errors
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
            (fun k z =>
              Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z))
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd y n G hτ hτn)
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd y n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z)
            hτ hτn)
        intro τ hτn X j hj
        have h := hGwenv σ hG A hA1 n hnT' τ hτn X j hj
        simpa only [hGdef] using h
      have hE₁' :
          |Sandpile.stoppingSup n (y + e) F - Sandpile.stoppingSup n (y + e) Gχ| ≤ ε / 4 := by
        refine hA₁ A (le_max_left _ _) R hR1 (y + e) ρ' hρ'0 hyeρ' hAρ' n hn1' hnT'
          F (fun τ hτ hτn => Sandpile.measurable_stopped_value n G hτ hτn) ?_
          (Sandpile.bddAbove_walk_stopped_value hd (y + e) n G)
          (Sandpile.bddAbove_walk_stopped_value hd (y + e) n
            (fun k z =>
              Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z))
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd (y + e) n G hτ hτn)
          (fun τ hτ hτn => Sandpile.integrable_stopped_value hd (y + e) n
            (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) * G k z)
            hτ hτn)
        intro τ hτn X j hj
        have h := hGwenv σ hG A hA1 n hnT' τ hτn X j hj
        simpa only [hGdef] using h
      -- the reward oscillation
      have hE₂ : |Sandpile.stoppingSup n (y + e) Gχ - Sandpile.stoppingSup n y Gχ| ≤ ε / 4 := by
        refine Sandpile.abs_stoppingSup_translate_sub_le hd n y e
          (fun k z => Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R z) *
            (-Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ) (n - k) z))
          (ε / 4) (fun k hk z => ?_)
        have h := Sandpile.abs_cutoff_meshValue_translate_sub_le hd R hR1 A hA0
          (Sandpile.scenery d σ) (n - k) e he M (ε / 8) hM0 (by positivity)
          (fun w hw => hMb k hk w hw) (fun w hw => hε₀b k hk w hw) z
        have hMle : Real.sqrt d / (R * A) * M ≤ ε / 8 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < R * A)]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < A * ε)] at hRM
          nlinarith [hRM, hA0, hε, hM0, hsd0]
        linarith [h, hMle]
      have hb := Sandpile.abs_rescaled_odometer_translate_sub_le hd R hR0
        (Sandpile.scenery d σ) n y e
        Gχ (ε / 8) (ε / 4) (ε / 4) (ε / 4) hE₀ hE₁ hE₁' hE₂
      have : ¬ (ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) n (y + e)
          - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) n y|) := by
        intro hlt
        have hsum : ε / 8 + ε / 4 + ε / 4 + ε / 4 < ε := by linarith
        linarith [hb, hsum]
      exact this hgt
    · exact Or.inr hG
  calc centeredMassLaw d ν {σ | ∃ y e : Sandpile.Site d, (∀ i, |y i| ≤ ⌈R * ρ⌉) ∧ (∀ i, |e i| ≤ 1) ∧
        ε < |R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ (y + e)
            - R ^ ((d : ℝ) / 2 - 2) * Sandpile.odometerOf (Sandpile.scenery d σ) ⌊T * R ^ 2⌋₊ y|}
      ≤ centeredMassLaw d ν (badA ∪ badM ∪ badB ∪ Gwᶜ) := measure_mono hsub
    _ ≤ centeredMassLaw d ν (badA ∪ badM ∪ badB) + centeredMassLaw d ν Gwᶜ :=
        measure_union_le _ _
    _ ≤ (centeredMassLaw d ν (badA ∪ badM) + centeredMassLaw d ν badB)
          + centeredMassLaw d ν Gwᶜ := by
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
