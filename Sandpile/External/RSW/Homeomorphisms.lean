import Sandpile.External.RSW.Endpoint

/-!
# Increasing homeomorphisms for the RSW comparison

Positive powers and reflection construct the increasing interval isomorphisms used to
quantify the crossing estimates.
-/

open Set

noncomputable section

namespace Sandpile.External.RSW

/-- Raising to a positive real power is an order isomorphism of the unit interval. -/
def unitIntervalRpow (a : ℝ) (ha : 0 < a) : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 where
  toFun x := ⟨(x : ℝ) ^ a, Real.rpow_nonneg x.property.1 _,
    Real.rpow_le_one x.property.1 x.property.2 ha.le⟩
  invFun x := ⟨(x : ℝ) ^ a⁻¹, Real.rpow_nonneg x.property.1 _,
    Real.rpow_le_one x.property.1 x.property.2 (inv_pos.mpr ha).le⟩
  left_inv x := Subtype.ext (Real.rpow_rpow_inv x.property.1 ha.ne')
  right_inv x := Subtype.ext (Real.rpow_inv_rpow x.property.1 ha.ne')
  map_rel_iff' := by
    intro x y
    exact Real.rpow_le_rpow_iff x.property.1 y.property.1 ha

/-- Reflection `x ↦ 1 - x` reverses the order on the unit interval. -/
def unitIntervalReflect : Icc (0 : ℝ) 1 ≃o (Icc (0 : ℝ) 1)ᵒᵈ where
  toFun x := OrderDual.toDual ⟨1 - (x : ℝ), by linarith [x.property.2],
    by linarith [x.property.1]⟩
  invFun x := ⟨1 - (OrderDual.ofDual x).val, by linarith [(OrderDual.ofDual x).property.2],
    by linarith [(OrderDual.ofDual x).property.1]⟩
  left_inv x := by
    apply Subtype.ext
    change 1 - (1 - (x : ℝ)) = (x : ℝ)
    ring
  right_inv x := by
    apply OrderDual.ofDual.injective
    apply Subtype.ext
    change 1 - (1 - (OrderDual.ofDual x).val) = (OrderDual.ofDual x).val
    ring
  map_rel_iff' := by
    intro x y
    change 1 - (y : ℝ) ≤ 1 - (x : ℝ) ↔ (x : ℝ) ≤ (y : ℝ)
    constructor <;> intro h <;> linarith

/-- The comparison isomorphism `x ↦ (1 - (1 - x)^(1/a))^a` for `a > 0`. -/
def crossingComparisonIso (a : ℝ) (ha : 0 < a) : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
  ((unitIntervalReflect.trans (unitIntervalRpow a⁻¹ (inv_pos.mpr ha)).dual).trans
    unitIntervalReflect.symm).trans (unitIntervalRpow a ha)

/-- The value of the crossing comparison isomorphism. -/
theorem crossingComparisonIso_apply (a : ℝ) (ha : 0 < a) (x : Icc (0 : ℝ) 1) :
    (crossingComparisonIso a ha x : ℝ) = (1 - (1 - (x : ℝ)) ^ a⁻¹) ^ a := rfl

end Sandpile.External.RSW
