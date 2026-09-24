/-
The arm of Step 2 (`sandpile.tex:2285-2288`): "If `z` is processed, then `{𝒳_1 > 0}` has an arm
from a fixed ball around `z` down to the bottom side."

A discovered point is the end of a chain of segments on which the field, at every rational
parameter, is at least the level the exploration explores.  Almost surely the unit ball field
is continuous and agrees with the field the exploration computes at every one of the countably
many points a chain reads, so on that event the whole chain lies in the superlevel set, and
therefore, the level being positive, in `{𝒳_1 > 0}`.  The chain is compact and connected and
joins the square of the discovered point to the starting side of the rectangle, which is the
arm the estimate of `sandpile.tex:2221-2227` bounds.
-/
import Sandpile.Support.CrossExploreDecide
import Sandpile.Support.CrossAnnulusBlocking

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- The points at which a step of a discovered chain reads the field. -/
def stepPts (a b : Fin 2 → ℝ) : Set (Space 2) :=
  {u | ∃ p p' : Space 2, p ∈ sampPts a b ∧ p' ∈ sampPts a b ∧ ∃ q : ℚ, u = segPt p p' (q : ℝ)}

theorem countable_stepPts (a b : Fin 2 → ℝ) : (stepPts a b).Countable := by
  classical
  have hc : Countable ↥(sampPts a b) := countable_sampPts_coe a b
  have hsub : stepPts a b ⊆
      Set.range (fun t : ↥(sampPts a b) × ↥(sampPts a b) × ℚ =>
        segPt (t.1 : Space 2) (t.2.1 : Space 2) ((t.2.2 : ℚ) : ℝ)) := by
    rintro u ⟨p, p', hp, hp', q, rfl⟩
    exact ⟨(⟨p, hp⟩, ⟨p', hp'⟩, q), rfl⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

instance countable_stepPts_coe (a b : Fin 2 → ℝ) : Countable ↥(stepPts a b) :=
  (countable_stepPts a b).to_subtype

theorem segPt_mem_stepPts {a b : Fin 2 → ℝ} {p p' : Space 2} (hp : p ∈ sampPts a b)
    (hp' : p' ∈ sampPts a b) (q : ℚ) : segPt p p' (q : ℝ) ∈ stepPts a b :=
  ⟨p, p', hp, hp', q, rfl⟩

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}

/-- Almost surely the field the exploration computes agrees with the unit ball field at every
point at which a chain reads it. -/
theorem ae_blockField_eq_on_stepPts [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) (a b : Fin 2 → ℝ) :
    ∀ᵐ ω ∂P, ∀ u ∈ stepPts a b, blockField d W u ω = ballField d W 1 u ω := by
  have h : ∀ u : ↥(stepPts a b), ∀ᵐ ω ∂P,
      blockField d W (u : Space 2) ω = ballField d W 1 (u : Space 2) ω :=
    fun u => blockField_ae_eq hd hW (u : Space 2)
  have := (ae_all_iff (ι := ↥(stepPts a b))).mpr h
  filter_upwards [this] with ω hω u hu
  exact hω ⟨u, hu⟩

variable {a b : Fin 2 → ℝ} {lev : ℝ} {D : Finset (Sandpile.Site 2)} {ω : Ω}

omit [MeasurableSpace Ω] in
/-- **The arm of a discovered point.**  On the event that the unit ball field is continuous and
is computed by the exploration at every point a chain reads, a discovered point either lies on
the starting side of the rectangle or is joined to it by a compact connected subset of the
positive set. -/
theorem reached_arm (hlev : 0 < lev)
    (hcont : Continuous fun u => ballField d W 1 u ω)
    (heq : ∀ u ∈ stepPts a b, blockField d W u ω = ballField d W 1 u ω)
    {p : Space 2} (h : reachedPt a b lev (blockField d W) D ω p) :
    p 0 = a 0 ∨ ∃ Γ : Set (Space 2), IsCompact Γ ∧ IsConnected Γ ∧
      Γ ⊆ {u | 0 < ballField d W 1 u ω} ∧ p ∈ Γ ∧ ∃ y ∈ Γ, y 0 = a 0 := by
  obtain ⟨k, w, hw, h0, hr, hD, hs, hlast⟩ := exists_nat_chain_of_reachedPt h
  match k, hlast with
  | 0, hlast => exact Or.inl (by rw [← hlast]; exact h0)
  | (k + 1), hlast =>
    refine Or.inr ⟨pathSet (k + 1) w, isCompact_pathSet _ _, isConnected_pathSet k w, ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      have hjk : j < k + 1 := Finset.mem_range.mp hj
      have hlevseg : ∀ u ∈ segSet (w j) (w (j + 1)), lev ≤ ballField d W 1 u ω := by
        refine le_on_segSet hcont (w j) (w (j + 1)) lev ?_
        intro q hq0 hq1
        have hstep := (hs j hjk).2.2 q hq0 hq1
        rwa [heq _ (segPt_mem_stepPts (hw j (by omega)) (hw (j + 1) (by omega)) q)] at hstep
      exact lt_of_lt_of_le hlev (hlevseg y hyj)
    · rw [← hlast]; exact end_mem_pathSet k w
    · exact ⟨w 0, start_mem_pathSet k w, h0⟩

/-- The corner of a square, as a point of the plane. -/
noncomputable def sqPoint (z : Sandpile.Site 2) : Space 2 :=
  WithLp.toLp 2 (fun i => (z i : ℝ))

theorem sqPoint_apply (z : Sandpile.Site 2) (i : Fin 2) : sqPoint z i = (z i : ℝ) := rfl

theorem norm_le_three {u v : Space 2} (h : ∀ i, |u i - v i| ≤ 2) : ‖u - v‖ ≤ 3 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin 2, ‖(u - v) i‖ ^ 2 ≤ 9 := by
    rw [Fin.sum_univ_two]
    have h0 := h 0
    have h1 := h 1
    have e0 : ‖(u - v) 0‖ = |u 0 - v 0| := by
      rw [PiLp.sub_apply, Real.norm_eq_abs]
    have e1 : ‖(u - v) 1‖ = |u 1 - v 1| := by
      rw [PiLp.sub_apply, Real.norm_eq_abs]
    rw [e0, e1]
    nlinarith [abs_nonneg (u 0 - v 0), abs_nonneg (u 1 - v 1)]
  calc Real.sqrt (∑ i : Fin 2, ‖(u - v) i‖ ^ 2) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt hsum
    _ = 3 := by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]

theorem abs_sub_le_two_of_sqAdj {p : Space 2} {z : Sandpile.Site 2}
    (h : sqAdj (sqOf p) z) (i : Fin 2) : |p i - (z i : ℝ)| ≤ 2 := by
  have hadj := h i
  rw [abs_le, sqOf_apply] at hadj
  have hfl : ((⌊p i⌋ : ℤ) : ℝ) ≤ p i := Int.floor_le _
  have hfl' : p i < ((⌊p i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hc1 : ((z i : ℤ) : ℝ) - 1 ≤ ((⌊p i⌋ : ℤ) : ℝ) := by exact_mod_cast by omega
  have hc2 : ((⌊p i⌋ : ℤ) : ℝ) ≤ ((z i : ℤ) : ℝ) + 1 := by exact_mod_cast by omega
  rw [abs_le]
  constructor <;> linarith

omit [MeasurableSpace Ω] in
/-- **The positive arm of a discovered square.**  A square discovered at distance more than
three from the starting side carries a positive arm from a ball of radius three about it to
that side. -/
theorem positiveArm_of_mem_reachSq (hlev : 0 < lev)
    (hcont : Continuous fun u => ballField d W 1 u ω)
    (heq : ∀ u ∈ stepPts a b, blockField d W u ω = ballField d W 1 u ω)
    {z : Sandpile.Site 2} (hz : z ∈ reachSq a b lev (blockField d W) D ω)
    (hfar : (3 : ℝ) ≤ (z 0 : ℝ) - a 0) :
    PositiveArm (fun u => ballField d W 1 u ω) (sqPoint z) 3 ((z 0 : ℝ) - a 0) := by
  rcases (mem_reachSq.mp hz).2 with hside | ⟨p, hreach, hadj⟩
  · exfalso
    have h1 : ((z 0 : ℤ) : ℝ) ≤ a 0 := by
      rw [hside]
      exact Int.floor_le _
    linarith
  rcases reached_arm hlev hcont heq hreach with hp0 | ⟨Γ, hcomp, hconn, hsub, hpΓ, y, hyΓ, hy0⟩
  · exfalso
    have h1 := abs_sub_le_two_of_sqAdj hadj 0
    rw [hp0, abs_le] at h1
    linarith [h1.1, h1.2]
  refine ⟨Γ, hcomp, hconn, hsub, ⟨(p : Space 2), hpΓ, ?_⟩, ⟨y, hyΓ, ?_⟩⟩
  · exact norm_le_three (fun i => abs_sub_le_two_of_sqAdj hadj i)
  · have hcoord : ‖(y - sqPoint z) 0‖ ≤ ‖y - sqPoint z‖ :=
      PiLp.norm_apply_le (p := 2) (y - sqPoint z) 0
    rw [PiLp.sub_apply, Real.norm_eq_abs, hy0, sqPoint_apply] at hcoord
    have : |a 0 - (z 0 : ℝ)| = (z 0 : ℝ) - a 0 := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith [this ▸ hcoord]

end Sandpile.Support
