import Sandpile.Support.MainExplKolmogorovTail

/-!
# A polynomial tail for the box supremum, uniform in scale and centre

A polynomial tail for the supremum of the interpolated rescaled field on a
space-time box of fixed size, uniform in the scale AND in the centre of the box.

The union bound of the cutoff error of `sandpile.tex:1908-1921` runs over
infinitely many boxes, so its tail must have a rate. `kolmogorov_polynomial_tail`
supplies one from the two moment bounds of `ssec:scaling-dlt4`, whose constants
do not depend on the scale or on the centre: the increment bound is
`exists_moment_modulus_linInterp`, which sees only the displacement of its two
arguments, and the anchor bound is `exists_one_point_moment_linInterp`, which
sees only the time. Since the constant produced by the criterion depends on the
BOX, the centre is carried by translating the field rather than the box: the
process is `piFieldAt`, the field read at the translate of the origin-centred box
by `v`, and one constant then serves every centre.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile.Frozen.HeatPotentialInvariance

variable {d : ℕ}

/-- The translation of `ℝ^{d+1}` that moves the space coordinates by `v` and fixes the
time coordinate. -/
noncomputable def piShift (v : Sandpile.Continuum.Space d) : Fin (d + 1) → ℝ :=
  Fin.cons 0 (fun j => v j)

/-- `piShift v` leaves the time coordinate, index `0`, untouched. -/
@[simp] theorem piShift_zero (v : Sandpile.Continuum.Space d) : piShift v 0 = 0 := rfl

/-- `piShift v` reads back the space coordinate `j` of `v` at index `j.succ`. -/
@[simp] theorem piShift_succ (v : Sandpile.Continuum.Space d) (j : Fin d) :
    piShift v j.succ = v j := rfl

/-- The interpolated rescaled field with its space argument translated by `v`. -/
noncomputable def piFieldAt (d : ℕ) (R : ℝ) (v : Sandpile.Continuum.Space d)
    (u : Fin (d + 1) → ℝ) (σ : Site d → ℝ) : ℝ :=
  piField d R (u + piShift v) σ

/-- Translating the space-time argument by `piShift v` leaves the time coordinate of `ofPi`
unchanged. -/
theorem ofPi_shift_fst (v : Sandpile.Continuum.Space d) (u : Fin (d + 1) → ℝ) :
    (ofPi (u + piShift v)).1 = u 0 := by
  show u 0 + piShift v 0 = u 0
  rw [piShift_zero, add_zero]

/-- Translating the space-time argument by `piShift v` shifts the `j`-th space coordinate of
`ofPi` by `v j`. -/
theorem ofPi_shift_snd (v : Sandpile.Continuum.Space d) (u : Fin (d + 1) → ℝ) (j : Fin d) :
    (ofPi (u + piShift v)).2 j = u j.succ + v j := rfl

/-- The translation by `piShift v` cancels in the difference of the `j`-th space coordinates of
two points, leaving the difference of the untranslated arguments. -/
theorem abs_ofPi_shift_sub (v : Sandpile.Continuum.Space d) (u u' : Fin (d + 1) → ℝ)
    (j : Fin d) :
    |(ofPi (u + piShift v)).2 j - (ofPi (u' + piShift v)).2 j| = |u j.succ - u' j.succ| := by
  rw [ofPi_shift_snd, ofPi_shift_snd]
  ring_nf

/-- **A polynomial tail for the supremum of the interpolated field on a box of fixed size,
uniform in the scale and in the centre.**  The exponent is the moment exponent `p`, which is
what the union bound over the boxes of a lattice needs. -/
theorem exists_box_tail
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (p : ℝ) (hp : 2 ≤ p)
    (hq : ((d : ℝ) + 1) < p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
    (T L : ℝ) (hT : 0 ≤ T) (hL : 0 ≤ L)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hint : Integrable (fun z => |z| ^ p) ν) :
    ∃ B : ℝ, 0 < B ∧ ∀ R : ℝ, 1 ≤ R → ∀ v : Sandpile.Continuum.Space d, ∀ Λ : ℝ, 0 < Λ →
      Sandpile.centeredMassLaw d ν
          {σ | ∃ u ∈ Set.Icc (boxLo d L) (boxHi d T L), Λ < |piFieldAt d R v u σ|}
        ≤ ENNReal.ofReal ((B / Λ) ^ p) := by
  classical
  set β : ℝ := min (1 - (d : ℝ) / 4) ((1 - θ) / 4) with hβdef
  have hp0 : (0:ℝ) < p := by linarith
  obtain ⟨M₁, hM₁, hmod⟩ := exists_moment_modulus_linInterp hHK hd hd3 hθ0 hθ1 p hp
    T (2 * (d : ℝ) * L) hT (by positivity)
  obtain ⟨M₂, hM₂, hone⟩ := exists_one_point_moment_linInterp hHK hd hd3 p hp T hT
  have hrm : (0:ℝ) ≤ Sandpile.resampleMoment ν p := LatticeProb.pairMoment_nonneg ν p
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hβ0 : (0:ℝ) < β := lt_min (by linarith) (by linarith)
  have hpβ : (0:ℝ) ≤ p * β := by positivity
  set M : ℝ := max (M₁ * Sandpile.resampleMoment ν p * (1 + (d : ℝ)) ^ (p * β))
    (M₂ * Sandpile.resampleMoment ν p) with hMdef
  have hab : boxLo d L ≤ boxHi d T L := boxLo_le_boxHi d L T hT hL
  obtain ⟨B, hB0, hB⟩ := kolmogorov_polynomial_tail (d + 1) (boxLo d L) (boxHi d T L) hab
    p (p * β) M hp0 (by push_cast; linarith)
  refine ⟨B, hB0, ?_⟩
  intro R hR v Λ hΛ
  have hmem : ∀ u ∈ Set.Icc (boxLo d L) (boxHi d T L),
      u + piShift v ∈ Set.Icc (boxLo d (L + ‖v‖)) (boxHi d T (L + ‖v‖)) := by
    intro u hu
    obtain ⟨⟨h0, hTu⟩, hj⟩ := (mem_box_iff T L u).mp hu
    refine (mem_box_iff T (L + ‖v‖) (u + piShift v)).mpr ⟨⟨?_, ?_⟩, fun j => ?_⟩
    · show (0:ℝ) ≤ u 0 + piShift v 0
      rw [piShift_zero, add_zero]; exact h0
    · show u 0 + piShift v 0 ≤ T
      rw [piShift_zero, add_zero]; exact hTu
    · have hvj : |v j| ≤ ‖v‖ := abs_coord_le_norm v j
      rw [abs_le] at hvj
      have hshow : (u + piShift v) j.succ = u j.succ + v j := rfl
      rw [hshow]
      exact ⟨by linarith [(hj j).1], by linarith [(hj j).2]⟩
  refine hB (Sandpile.centeredMassLaw d ν) inferInstance
    (fun u σ => piFieldAt d R v u σ) ?_ ?_ ?_ ?_ ?_ ?_ Λ hΛ
  · exact fun u => measurable_piField R (u + piShift v)
  · intro u hu u' hu'
    exact integrable_piField_sub_rpow hd ν (by linarith) hint R T (L + ‖v‖)
      (u + piShift v) (u' + piShift v) (hmem u hu) (hmem u' hu')
  · intro u hu u' hu'
    have hu0 := (mem_box_iff T L u).mp hu
    have hu'0 := (mem_box_iff T L u').mp hu'
    have hsum : ∑ j : Fin d, |(ofPi (u + piShift v)).2 j - (ofPi (u' + piShift v)).2 j|
        ≤ 2 * (d : ℝ) * L := by
      calc ∑ j : Fin d, |(ofPi (u + piShift v)).2 j - (ofPi (u' + piShift v)).2 j|
          = ∑ j : Fin d, |(ofPi u).2 j - (ofPi u').2 j| := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_ofPi_shift_sub]
            rfl
        _ ≤ 2 * (d : ℝ) * L := sum_abs_sub_box_le hu hu'
    have hmain := hmod ν inferInstance hmean hint R hR
      (ofPi (u + piShift v)).1 (ofPi (u' + piShift v)).1
      (ofPi (u + piShift v)).2 (ofPi (u' + piShift v)).2
      (by rw [ofPi_shift_fst]; exact hu0.1.1) (by rw [ofPi_shift_fst]; exact hu'0.1.1)
      (by rw [ofPi_shift_fst]; exact hu0.1.2) (by rw [ofPi_shift_fst]; exact hu'0.1.2) hsum
    refine le_trans hmain ?_
    have hcoord : |(ofPi (u + piShift v)).1 - (ofPi (u' + piShift v)).1|
        + ∑ j : Fin d, |(ofPi (u + piShift v)).2 j - (ofPi (u' + piShift v)).2 j|
        = |u 0 - u' 0| + ∑ j : Fin d, |u j.succ - u' j.succ| := by
      rw [ofPi_shift_fst, ofPi_shift_fst]
      refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
      rw [abs_ofPi_shift_sub]
    rw [hcoord]
    have hδ0 : (0:ℝ) ≤ |u 0 - u' 0| + ∑ j : Fin d, |u j.succ - u' j.succ| := by
      have h1 : (0:ℝ) ≤ ∑ j : Fin d, |u j.succ - u' j.succ| :=
        Finset.sum_nonneg fun j _ => abs_nonneg _
      have h2 := abs_nonneg (u 0 - u' 0)
      linarith
    have hpow : (|u 0 - u' 0| + ∑ j : Fin d, |u j.succ - u' j.succ|) ^ (p * β)
        ≤ (1 + (d : ℝ)) ^ (p * β) * dist u u' ^ (p * β) := by
      rw [← Real.mul_rpow (by positivity) dist_nonneg]
      exact Real.rpow_le_rpow hδ0 (sum_abs_sub_le_dist_pi u u') hpβ
    calc M₁ * Sandpile.resampleMoment ν p
          * (|u 0 - u' 0| + ∑ j : Fin d, |u j.succ - u' j.succ|) ^ (p * β)
        ≤ M₁ * Sandpile.resampleMoment ν p
          * ((1 + (d : ℝ)) ^ (p * β) * dist u u' ^ (p * β)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = M₁ * Sandpile.resampleMoment ν p * (1 + (d : ℝ)) ^ (p * β)
          * dist u u' ^ (p * β) := by ring
      _ ≤ M * dist u u' ^ (p * β) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _)
  · exact integrable_piField_rpow hd ν (by linarith) hint R T (L + ‖v‖)
      (boxLo d L + piShift v) (hmem _ (Set.left_mem_Icc.mpr hab))
  · have h := hone ν inferInstance hmean hint R hR
      (ofPi (boxLo d L + piShift v)).1 (ofPi (boxLo d L + piShift v)).2
      (by rw [ofPi_shift_fst]; exact le_rfl) (by rw [ofPi_shift_fst]; exact hT)
    exact le_trans h (le_max_right _ _)
  · intro σ
    have hbase := continuousOn_linInterp_box hHK hd hd3 hθ0 hθ1 R hR (Sandpile.scenery d σ)
      T (‖v‖ + Real.sqrt (d : ℝ) * L) hT (by positivity)
    have hmaps : Set.MapsTo (fun u => ofPi (u + piShift v))
        (Set.Icc (boxLo d L) (boxHi d T L))
        (Set.Icc (0:ℝ) T ×ˢ Metric.closedBall (0 : Sandpile.Continuum.Space d)
          (‖v‖ + Real.sqrt (d : ℝ) * L)) := by
      intro u hu
      obtain ⟨⟨h0, hTu⟩, hj⟩ := (mem_box_iff T L u).mp hu
      refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [ofPi_shift_fst]; exact h0
      · rw [ofPi_shift_fst]; exact hTu
      · rw [Metric.mem_closedBall, dist_zero_right]
        have hsplit : (ofPi (u + piShift v)).2 = (ofPi u).2 + v := by
          ext j
          rw [ofPi_shift_snd]
          rfl
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        have := norm_ofPi_le hL (fun j => abs_le.mpr ⟨(hj j).1, (hj j).2⟩)
        linarith
    have hcont : ContinuousOn (fun u : Fin (d + 1) → ℝ => ofPi (u + piShift v))
        (Set.Icc (boxLo d L) (boxHi d T L)) :=
      (continuous_ofPi.comp (continuous_id.add continuous_const)).continuousOn
    exact hbase.comp hcont hmaps

end Sandpile.Support
