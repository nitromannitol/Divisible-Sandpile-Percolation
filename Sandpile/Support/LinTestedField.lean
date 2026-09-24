/-
The tested field `F_R` of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5665-5668`):

  `a_R(x) = R^{(d-4)/2} φ_R(x)`,  `F_R = ∑_{x∈Z^d} a_R(x) u_{n_R}(x)`,

and the four properties Step 2 of the proof asks of it: it is measurable, it
reads only the union of the boxes of radius `n_R` about the sites carrying a
weight, it is convex in each coordinate of the scenery, and its right derivative
in the coordinate `z` lies between `0` and `∑_x a_R(x) g_{n_R}(x,z)`.  The last
is the display of `sandpile.tex:5791-5795`, with the time-`n_R` Green kernel in
place of the full Green function, which is the sharper of the two and is what
the convex-linear bound consumes.
-/
import Sandpile.Support.LinConvexSite
import Sandpile.Support.FiniteCoord
import Sandpile.Support.Concentration

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The tested field `F_R = ∑_x a_R(x) u_{n_R}(x)` of `sandpile.tex:5660-5663`. -/
noncomputable def testedField (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (ζ : Site d → ℝ) : ℝ :=
  ∑ x ∈ s, a x * odometerOf ζ n x

/-- The sites the tested field reads: the union of the boxes of radius `n`. -/
noncomputable def testedSites (s : Finset (Site d)) (n : ℕ) : Finset (Site d) :=
  s.biUnion fun x => boxFinset x n

theorem measurable_testedField (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) :
    Measurable (testedField s a n) :=
  Finset.measurable_sum _ fun x _ => (measurable_odometerOf n x).const_mul (a x)

theorem testedField_congr (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (ζ η : Site d → ℝ) (h : ∀ z ∈ testedSites s n, ζ z = η z) :
    testedField s a n ζ = testedField s a n η := by
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  refine odometerOf_congr_box n x ζ η fun z hz => h z ?_
  exact Finset.mem_biUnion.2 ⟨x, hx, mem_boxFinset hz⟩

theorem convexOn_testedField_update (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (v : Site d) (ζ : Site d → ℝ) :
    ConvexOn ℝ (Set.univ : Set ℝ) fun y => testedField s a n (Function.update ζ v y) := by
  classical
  have hterm : ∀ x ∈ s, ConvexOn ℝ (Set.univ : Set ℝ)
      fun y => a x * odometerOf (Function.update ζ v y) n x := fun x hx =>
    (convexOn_section (odometerOf_convexOn n x) ζ v).smul (ha x hx)
  have hsum : ConvexOn ℝ (Set.univ : Set ℝ)
      fun y => ∑ x ∈ s, a x * odometerOf (Function.update ζ v y) n x := by
    classical
    induction s using Finset.induction with
    | empty => simpa using (convexOn_const (c := (0:ℝ)) convex_univ)
    | insert w t hw ih =>
        have hrw : (fun y => ∑ x ∈ insert w t, a x * odometerOf (Function.update ζ v y) n x)
            = fun y => a w * odometerOf (Function.update ζ v y) n w
              + ∑ x ∈ t, a x * odometerOf (Function.update ζ v y) n x := by
          funext y; rw [Finset.sum_insert hw]
        rw [hrw]
        exact (hterm w (Finset.mem_insert_self w t)).add
          (ih (fun x hx => ha x (Finset.mem_insert_of_mem hx))
              (fun x hx => hterm x (Finset.mem_insert_of_mem hx)))
  exact hsum

/-- `0 ≤ ∂_{ζ(z)}F_R`: the tested field is nondecreasing in every coordinate. -/
theorem rightDerivField_testedField_nonneg (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (v : Site d) (ζ : Site d → ℝ) :
    0 ≤ rightDerivField (testedField s a n) v ζ := by
  refine rightDerivField_nonneg _ v ζ (convexOn_testedField_update s a n ha v ζ) ?_
  intro y hy
  refine Finset.sum_le_sum fun x hx => ?_
  refine mul_le_mul_of_nonneg_left ?_ (ha x hx)
  refine odometerOf_mono n x fun z => ?_
  by_cases hz : z = v
  · subst hz; simpa using hy
  · simp [Function.update_of_ne hz]

/-- `∂_{ζ(z)}F_R ≤ ∑_x a_R(x) g_n(x,z)`, the bound of `sandpile.tex:5786-5790`
with the time-`n` Green kernel in place of the full Green function. -/
theorem rightDerivField_testedField_le (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (ha : ∀ x ∈ s, 0 ≤ a x) (v : Site d) (ζ : Site d → ℝ) :
    rightDerivField (testedField s a n) v ζ ≤ ∑ x ∈ s, a x * greenTime d n x v := by
  refine rightDerivField_le _ v ζ _ (convexOn_testedField_update s a n ha v ζ) ?_
  intro y hy
  have hsub : testedField s a n (Function.update ζ v y) - testedField s a n ζ
      = ∑ x ∈ s, a x *
        (odometerOf (Function.update ζ v y) n x - odometerOf ζ n x) := by
    rw [testedField, testedField, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hsub, Finset.sum_mul]
  refine Finset.sum_le_sum fun x hx => ?_
  have hstep : odometerOf (Function.update ζ v y) n x - odometerOf ζ n x
      ≤ greenTime d n x v * (y - ζ v) := by
    have h := abs_odometerOf_update_le ζ v y n x
    have h1 : odometerOf (Function.update ζ v y) n x - odometerOf ζ n x
        ≤ greenTime d n x v * |ζ v - y| := by
      have := neg_le_of_abs_le h
      linarith
    have h2 : |ζ v - y| = y - ζ v := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rwa [h2] at h1
  calc a x * (odometerOf (Function.update ζ v y) n x - odometerOf ζ n x)
      ≤ a x * (greenTime d n x v * (y - ζ v)) :=
        mul_le_mul_of_nonneg_left hstep (ha x hx)
    _ = a x * greenTime d n x v * (y - ζ v) := by ring

end Sandpile
