import Sandpile.External.RSW.Homeomorphisms

/-!
# Combining interval comparison functions

The pointwise product of two increasing unit-interval isomorphisms is another such
isomorphism and is bounded above by either factor.
-/

open Set

noncomputable section

namespace Sandpile.External.RSW

/-- The pointwise product of two unit-interval isomorphisms. -/
def unitIntervalIsoProductMap (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (x : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨(f x : ℝ) * (g x : ℝ), mul_nonneg (f x).property.1 (g x).property.1,
    (mul_le_of_le_one_right (f x).property.1 (g x).property.2).trans (f x).property.2⟩

/-- The product map is strictly increasing. -/
theorem unitIntervalIsoProductMap_strictMono (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) :
    StrictMono (unitIntervalIsoProductMap f g) := by
  intro x y hxy
  have hf : (f x : ℝ) < f y := f.strictMono hxy
  have hg : (g x : ℝ) < g y := g.strictMono hxy
  have hgy : (0 : ℝ) < g y := lt_of_le_of_lt (g x).property.1 hg
  change (f x : ℝ) * (g x : ℝ) < (f y : ℝ) * (g y : ℝ)
  exact (mul_le_mul_of_nonneg_left hg.le (f x).property.1).trans_lt
    (mul_lt_mul_of_pos_right hf hgy)

/-- The product map is surjective. -/
theorem unitIntervalIsoProductMap_surjective (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) :
    Function.Surjective (unitIntervalIsoProductMap f g) := by
  let F : Icc (0 : ℝ) 1 → ℝ := fun x => (f x : ℝ) * (g x : ℝ)
  have hcont : Continuous F :=
    (continuous_subtype_val.comp f.continuous).mul (continuous_subtype_val.comp g.continuous)
  have hFbot : F ⊥ = 0 := by
    simp only [F, OrderIso.map_bot]
    change (0 : ℝ) * 0 = 0
    ring
  have hFtop : F ⊤ = 1 := by
    simp only [F, OrderIso.map_top]
    change (1 : ℝ) * 1 = 1
    ring
  intro y
  have hy : (y : ℝ) ∈ Icc (F ⊥) (F ⊤) := by
    rw [hFbot, hFtop]
    exact y.property
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show (⊥ : Icc (0 : ℝ) 1) ≤ ⊤ from bot_le)
    hcont.continuousOn hy
  refine ⟨x, ?_⟩
  exact Subtype.ext hx

/-- An isomorphism bounded above by each of two given interval isomorphisms. -/
def unitIntervalIsoProduct (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) :
    Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective (unitIntervalIsoProductMap f g)
    (unitIntervalIsoProductMap_strictMono f g) (unitIntervalIsoProductMap_surjective f g)

/-- The product isomorphism is bounded by its first factor. -/
theorem unitIntervalIsoProduct_le_left (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (x : Icc (0 : ℝ) 1) : unitIntervalIsoProduct f g x ≤ f x := by
  change (f x : ℝ) * (g x : ℝ) ≤ f x
  exact mul_le_of_le_one_right (f x).property.1 (g x).property.2

/-- The product isomorphism is bounded by its second factor. -/
theorem unitIntervalIsoProduct_le_right (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (x : Icc (0 : ℝ) 1) : unitIntervalIsoProduct f g x ≤ g x := by
  change (f x : ℝ) * (g x : ℝ) ≤ g x
  exact mul_le_of_le_one_left (g x).property.1 (f x).property.2

end Sandpile.External.RSW
