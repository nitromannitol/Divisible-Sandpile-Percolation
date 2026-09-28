import LatticeProb.Prob.LpSmooth

/-!
# Convexity bound on the resampling quotient

The convexity step of `lem:convex-linear-bound` (`sandpile.tex:1547-1569`): the resampling
quotient of a coordinatewise convex function lies between the right derivatives at the two
endpoints.
-/

open MeasureTheory Set

namespace Sandpile

/-- For a convex function on the line, the right derivative at the left endpoint
is at most the slope, and the slope is at most the right derivative at the right
endpoint. -/
theorem convexOn_slope_bounds {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.univ : Set ℝ) f)
    {u v du dv : ℝ} (huv : u < v)
    (hdu : HasDerivWithinAt f du (Set.Ici u) u)
    (hdv : HasDerivWithinAt f dv (Set.Ici v) v) :
    du ≤ slope f u v ∧ slope f u v ≤ dv := by
  have hint : (v : ℝ) ∈ interior (Set.univ : Set ℝ) := by simp
  refine ⟨hf.le_slope_of_hasDerivWithinAt_Ioi (mem_univ _) (mem_univ _) huv
      (hdu.mono Ioi_subset_Ici_self), ?_⟩
  have h1 : slope f u v ≤ derivWithin f (Iio v) v :=
    hf.slope_le_leftDeriv_of_mem_interior (mem_univ _) hint huv
  have h2 : derivWithin f (Iio v) v ≤ derivWithin f (Ioi v) v :=
    hf.leftDeriv_le_rightDeriv_of_mem_interior hint
  have h3 : derivWithin f (Ioi v) v = dv :=
    (hdv.mono Ioi_subset_Ici_self).derivWithin (uniqueDiffWithinAt_Ioi v)
  linarith [h1, h2, h3.le, h3.ge]

variable {N : ℕ}

/-- The resampling difference of a coordinatewise convex function is the change
in the coordinate times a quotient lying between the two right derivatives. -/
theorem exists_slope_between (F : (Fin N → ℝ) → ℝ) (D : Fin N → (Fin N → ℝ) → ℝ)
    (hconv : ∀ (i : Fin N) (ξ : Fin N → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ξ i y))
    (hderiv : ∀ (i : Fin N) (ξ : Fin N → ℝ),
      HasDerivWithinAt (fun y => F (Function.update ξ i y)) (D i ξ) (Set.Ici (ξ i)) (ξ i))
    (i : Fin N) (ξ : Fin N → ℝ) (y : ℝ) :
    ∃ Δ : ℝ, F ξ - F (Function.update ξ i y) = (ξ i - y) * Δ ∧
      min (D i ξ) (D i (Function.update ξ i y)) ≤ Δ ∧
        Δ ≤ max (D i ξ) (D i (Function.update ξ i y)) := by
  classical
  set g : ℝ → ℝ := fun z => F (Function.update ξ i z) with hgdef
  set ξ' : Fin N → ℝ := Function.update ξ i y with hξ'
  have hgξ : g (ξ i) = F ξ := by
    rw [hgdef]
    simp
  have hgy : g y = F ξ' := rfl
  have hξ'i : ξ' i = y := by rw [hξ']; simp
  have hsec : (fun z => F (Function.update ξ' i z)) = g := by
    funext z
    rw [hgdef, hξ', Function.update_idem]
  have hd1 : HasDerivWithinAt g (D i ξ) (Set.Ici (ξ i)) (ξ i) := hderiv i ξ
  have hd2 : HasDerivWithinAt g (D i ξ') (Set.Ici y) y := by
    have := hderiv i ξ'
    rw [hsec, hξ'i] at this
    exact this
  have hconvg : ConvexOn ℝ (Set.univ : Set ℝ) g := hconv i ξ
  rcases lt_trichotomy (ξ i) y with hlt | heq | hgt
  · refine ⟨slope g (ξ i) y, ?_, ?_, ?_⟩
    · rw [slope_def_field]
      field_simp
      rw [hgξ, hgy]
      ring
    · exact le_trans (min_le_left _ _) (convexOn_slope_bounds hconvg hlt hd1 hd2).1
    · exact le_trans (convexOn_slope_bounds hconvg hlt hd1 hd2).2 (le_max_right _ _)
  · refine ⟨D i ξ, ?_, ?_, ?_⟩
    · have hxx : ξ' = ξ := by rw [hξ', ← heq]; simp
      simp [hxx, heq]
    · exact min_le_left _ _
    · exact le_max_left _ _
  · refine ⟨slope g y (ξ i), ?_, ?_, ?_⟩
    · rw [slope_def_field]
      field_simp
      rw [hgξ, hgy]
    · exact le_trans (min_le_right _ _) (convexOn_slope_bounds hconvg hgt hd2 hd1).1
    · exact le_trans (convexOn_slope_bounds hconvg hgt hd2 hd1).2 (le_max_left _ _)

end Sandpile
