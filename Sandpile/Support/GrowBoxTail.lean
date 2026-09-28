import Sandpile.Support.GrowIncrementMoment
import Sandpile.Support.GrowAnchorMoment
import Sandpile.Support.MainExplKolmogorovTail
import Sandpile.Support.GrowAeMoment

/-!
# A uniform polynomial tail for the potential on a unit box

Gives a polynomial tail for the supremum of the continuous version of the Gaussian heat
potential on a unit space-time box, uniform in the box's spatial centre. The potential is
stationary in space, since the increment and anchor moment bounds hold at every space point
and not merely inside a bounded region, so translating the unit box `[0, T] × [-1, 1]^d` to any
centre `v : Fin d → ℝ` costs nothing: the increment and anchor moments of the translated process
are exactly those of the untranslated one, read at the translated point. A single application of
`kolmogorov_polynomial_tail` therefore serves every centre with the same constant `B`.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The process `Y` reindexed by a single coordinate `u : Fin (d + 1) → ℝ`, whose first
coordinate `u 0` is read as time and whose remaining coordinates `u j.succ` are read as the
spatial position shifted by the fixed centre `v : Fin d → ℝ`. -/
noncomputable def piPotential {ΩW : Type*} (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ) (v : Fin d → ℝ)
    (u : Fin (d + 1) → ℝ) (ω : ΩW) : ℝ :=
  Y (u 0, fun j => u j.succ + v j) ω

/-- `piPotential Y v u` is measurable in `ω` whenever every time-space slice of `Y` is. -/
theorem measurable_piPotential {ΩW : Type*} [MeasurableSpace ΩW] (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ)
    (hYmeas : ∀ z, Measurable (Y z)) (v : Fin d → ℝ) (u : Fin (d + 1) → ℝ) :
    Measurable (piPotential Y v u) :=
  hYmeas _

/-- For a fixed sample `ω`, `piPotential Y v · ω` is continuous in `u` whenever `Y · ω` is
continuous, since it factors through the continuous reindexing map `u ↦ (u 0, u j.succ + v j)`. -/
theorem continuousOn_piPotential {ΩW : Type*} (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ)
    (hYcont : ∀ ω, Continuous fun z => Y z ω) (v : Fin d → ℝ) (ω : ΩW) :
    Continuous fun u : Fin (d + 1) → ℝ => piPotential Y v u ω := by
  unfold piPotential
  refine (hYcont ω).comp ?_
  exact (continuous_apply (0 : Fin (d + 1))).prodMk
    (continuous_pi fun j => (continuous_apply j.succ).add continuous_const)

/-- **A polynomial tail for the supremum of the potential on a unit space-time
box, uniform in the box's spatial centre.** -/
theorem exists_potential_box_tail (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 < T) {ΩW : Type} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ) (hYmeas : ∀ z, Measurable (Y z))
    (hYmod : ∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) T →
      Y z =ᵐ[PW] fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω)
    (hYcont : ∀ ω, Continuous fun z => Y z ω) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : Fin d → ℝ, ∀ Λ : ℝ, 0 < Λ →
      PW {ω | ∃ u ∈ Set.Icc (boxLo d 1) (boxHi d T 1), Λ < |piPotential Y v u ω|}
        ≤ ENNReal.ofReal ((B / Λ) ^ (8 * ((d : ℝ) + 2))) := by
  classical
  obtain ⟨Kc, hKc0, hKc⟩ := exists_potential_moment_bound hd hd3 hν2 hT PW W hW
  obtain ⟨Manc, hManc0, hManc⟩ :=
    exists_anchor_moment hd hd3 hν2 hT.le PW W hW (p := 8 * ((d : ℝ) + 2)) (by positivity)
  obtain ⟨K, hK1, hK⟩ := exists_toLp_norm_bound d hd
  set p : ℝ := 8 * ((d : ℝ) + 2) with hpdef
  set q : ℝ := (d : ℝ) + 2 with hqdef
  have hp : 0 < p := by rw [hpdef]; positivity
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  set M : ℝ := max (Kc * K ^ q) Manc with hMdef
  have hab : boxLo d 1 ≤ boxHi d T 1 := boxLo_le_boxHi d 1 T hT.le zero_le_one
  have hq' : ((d + 1 : ℕ) : ℝ) < q := by push_cast; rw [hqdef]; linarith
  obtain ⟨B, hB0, hB⟩ :=
    kolmogorov_polynomial_tail (d + 1) (boxLo d 1) (boxHi d T 1) hab p q M hp hq'
  refine ⟨B, hB0, fun v Λ hΛ => ?_⟩
  refine hB PW inferInstance (piPotential Y v) (measurable_piPotential Y hYmeas v) ?_ ?_ ?_ ?_
    (fun ω => (continuousOn_piPotential Y hYcont v ω).continuousOn) Λ hΛ
  · -- increment integrability on the box
    intro u hu u' hu'
    have hu0 : u 0 ∈ Set.Icc (0 : ℝ) T := ((mem_box_iff T 1 u).mp hu).1
    have hu'0 : u' 0 ∈ Set.Icc (0 : ℝ) T := ((mem_box_iff T 1 u').mp hu').1
    set x : Space d := WithLp.toLp 2 (fun j : Fin d => u j.succ + v j) with hxdef
    set x' : Space d := WithLp.toLp 2 (fun j : Fin d => u' j.succ + v j) with hx'def
    have hae : (fun ω => |piPotential Y v u ω - piPotential Y v u' ω| ^ p)
        =ᵐ[PW] fun ω =>
          |gaussianPotential d ν2 W (u 0) x ω - gaussianPotential d ν2 W (u' 0) x' ω| ^ p := by
      have h1 := hYmod (u 0, fun j => u j.succ + v j) hu0
      have h2 := hYmod (u' 0, fun j => u' j.succ + v j) hu'0
      filter_upwards [h1, h2] with ω hω1 hω2
      show |Y (u 0, fun j => u j.succ + v j) ω - Y (u' 0, fun j => u' j.succ + v j) ω| ^ p = _
      rw [hω1, hω2]
    have hint := integrable_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 hu0.1 hu'0.1 x x' hp
    exact hint.congr hae.symm
  · -- increment moment bound on the box
    intro u hu u' hu'
    have hu0 : u 0 ∈ Set.Icc (0 : ℝ) T := ((mem_box_iff T 1 u).mp hu).1
    have hu'0 : u' 0 ∈ Set.Icc (0 : ℝ) T := ((mem_box_iff T 1 u').mp hu').1
    set x : Space d := WithLp.toLp 2 (fun j : Fin d => u j.succ + v j) with hxdef
    set x' : Space d := WithLp.toLp 2 (fun j : Fin d => u' j.succ + v j) with hx'def
    have hae : (fun ω => |piPotential Y v u ω - piPotential Y v u' ω| ^ p)
        =ᵐ[PW] fun ω =>
          |gaussianPotential d ν2 W (u 0) x ω - gaussianPotential d ν2 W (u' 0) x' ω| ^ p := by
      have h1 := hYmod (u 0, fun j => u j.succ + v j) hu0
      have h2 := hYmod (u' 0, fun j => u' j.succ + v j) hu'0
      filter_upwards [h1, h2] with ω hω1 hω2
      show |Y (u 0, fun j => u j.succ + v j) ω - Y (u' 0, fun j => u' j.succ + v j) ω| ^ p = _
      rw [hω1, hω2]
    rw [integral_congr_ae hae]
    have hfeq : (fun j : Fin d => u j.succ + v j) - (fun j : Fin d => u' j.succ + v j)
        = (fun j : Fin d => u j.succ) - (fun j : Fin d => u' j.succ) := by
      funext j
      simp only [Pi.sub_apply]
      ring
    have hab : dist (fun j : Fin d => u j.succ + v j) (fun j : Fin d => u' j.succ + v j)
        = dist (fun j : Fin d => u j.succ) (fun j : Fin d => u' j.succ) := by
      rw [dist_eq_norm, dist_eq_norm, hfeq]
    have hnormle : ‖x - x'‖
        ≤ K * dist (fun j : Fin d => u j.succ) (fun j : Fin d => u' j.succ) := by
      rw [hxdef, hx'def]
      calc ‖(WithLp.toLp 2 (fun j : Fin d => u j.succ + v j) : Space d)
              - WithLp.toLp 2 (fun j : Fin d => u' j.succ + v j)‖
          ≤ K * dist (fun j : Fin d => u j.succ + v j) (fun j : Fin d => u' j.succ + v j) :=
            hK _ _
        _ = K * dist (fun j : Fin d => u j.succ) (fun j : Fin d => u' j.succ) := by rw [hab]
    have hdistsucc : dist (fun j : Fin d => u j.succ) (fun j : Fin d => u' j.succ) ≤ dist u u' := by
      refine (dist_pi_le_iff dist_nonneg).mpr fun j => ?_
      exact dist_le_pi_dist u u' j.succ
    have htime : |u 0 - u' 0| ≤ dist u u' := by
      rw [← Real.dist_eq]; exact dist_le_pi_dist u u' 0
    have hmax : max |u 0 - u' 0| ‖x - x'‖ ≤ K * dist u u' := by
      refine max_le ?_ ?_
      · exact le_trans htime (le_mul_of_one_le_left dist_nonneg hK1)
      · exact le_trans hnormle (mul_le_mul_of_nonneg_left hdistsucc hK0)
    have hmax0 : (0 : ℝ) ≤ max |u 0 - u' 0| ‖x - x'‖ :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    have hmono : (max |u 0 - u' 0| ‖x - x'‖) ^ q ≤ (K * dist u u') ^ q :=
      Real.rpow_le_rpow hmax0 hmax (by rw [hqdef]; positivity)
    have hqK : (K * dist u u') ^ q = K ^ q * dist u u' ^ q :=
      Real.mul_rpow hK0 dist_nonneg
    calc ∫ ω, |gaussianPotential d ν2 W (u 0) x ω - gaussianPotential d ν2 W (u' 0) x' ω| ^ p ∂PW
        ≤ Kc * (max |u 0 - u' 0| ‖x - x'‖) ^ q := (hKc (u 0) hu0 (u' 0) hu'0 x x').2
      _ ≤ Kc * (K * dist u u') ^ q := mul_le_mul_of_nonneg_left hmono hKc0
      _ = Kc * K ^ q * dist u u' ^ q := by rw [hqK]; ring
      _ ≤ M * dist u u' ^ q :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · -- anchor integrability
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    set x : Space d := WithLp.toLp 2 (fun j : Fin d => (boxLo d 1) j.succ + v j) with hxdef
    have hbl0 : boxLo d 1 (0 : Fin (d + 1)) = (0 : ℝ) := rfl
    have hae : (fun ω => |piPotential Y v (boxLo d 1) ω| ^ p)
        =ᵐ[PW] fun ω => |gaussianPotential d ν2 W 0 x ω| ^ p := by
      have h1 := hYmod (boxLo d 1 0, fun j => boxLo d 1 j.succ + v j) (by rw [hbl0]; exact h0mem)
      filter_upwards [h1] with ω hω
      show |Y (boxLo d 1 0, fun j => boxLo d 1 j.succ + v j) ω| ^ p = _
      rw [hbl0] at hω ⊢
      rw [hω]
    exact (hManc 0 h0mem x).1.congr hae.symm
  · -- anchor moment bound
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    set x : Space d := WithLp.toLp 2 (fun j : Fin d => (boxLo d 1) j.succ + v j) with hxdef
    have hbl0 : boxLo d 1 (0 : Fin (d + 1)) = (0 : ℝ) := rfl
    have hae : (fun ω => |piPotential Y v (boxLo d 1) ω| ^ p)
        =ᵐ[PW] fun ω => |gaussianPotential d ν2 W 0 x ω| ^ p := by
      have h1 := hYmod (boxLo d 1 0, fun j => boxLo d 1 j.succ + v j) (by rw [hbl0]; exact h0mem)
      filter_upwards [h1] with ω hω
      show |Y (boxLo d 1 0, fun j => boxLo d 1 j.succ + v j) ω| ^ p = _
      rw [hbl0] at hω ⊢
      rw [hω]
    rw [integral_congr_ae hae]
    exact le_trans (hManc 0 h0mem x).2 (le_max_right _ _)

end Sandpile.Support
