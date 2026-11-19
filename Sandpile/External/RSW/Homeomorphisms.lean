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

/-- The map obtained by reflecting the value of the crossing comparison isomorphism. -/
def crossingComparisonFlip (a : ℝ) (ha : 0 < a) (x : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  OrderDual.ofDual (unitIntervalReflect (crossingComparisonIso a ha x))

/-- The reflected crossing comparison map is `1 - f_a`. -/
theorem crossingComparisonFlip_apply (a : ℝ) (ha : 0 < a) (x : Icc (0 : ℝ) 1) :
    (crossingComparisonFlip a ha x : ℝ) =
      1 - (1 - (1 - (x : ℝ)) ^ a⁻¹) ^ a := rfl

/-- The reflected crossing comparison map is an involution. -/
theorem crossingComparisonFlip_involutive (a : ℝ) (ha : 0 < a) :
    Function.Involutive (crossingComparisonFlip a ha) := by
  intro x
  apply Subtype.ext
  simp only [crossingComparisonFlip_apply, sub_sub_cancel]
  have hx0 : 0 ≤ 1 - (x : ℝ) := by linarith [x.property.2]
  have hx1 : 1 - (x : ℝ) ≤ 1 := by linarith [x.property.1]
  have hb : 0 ≤ 1 - (1 - (x : ℝ)) ^ a⁻¹ :=
    sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (inv_pos.mpr ha).le)
  rw [Real.rpow_rpow_inv hb ha.ne']
  simp only [sub_sub_cancel]
  rw [Real.rpow_inv_rpow hx0 ha.ne']
  ring

/-- Reflection of a point of the unit interval. -/
def unitIntervalComplement (x : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  OrderDual.ofDual (unitIntervalReflect x)

/-- The reflected comparison map reverses order. -/
theorem crossingComparisonFlip_antitone (a : ℝ) (ha : 0 < a) :
    Antitone (crossingComparisonFlip a ha) := by
  intro x y hxy
  change 1 - (crossingComparisonIso a ha y : ℝ) ≤
    1 - (crossingComparisonIso a ha x : ℝ)
  have hh : (crossingComparisonIso a ha x : ℝ) ≤ (crossingComparisonIso a ha y : ℝ) :=
    (crossingComparisonIso a ha).monotone hxy
  linarith

/-- The comparison inequality is symmetric under interchange of the two complementary
probabilities. -/
theorem crossingComparison_duality (a : ℝ) (ha : 0 < a) (x y : Icc (0 : ℝ) 1) :
    crossingComparisonIso a ha (unitIntervalComplement y) ≤ x ↔
      crossingComparisonIso a ha (unitIntervalComplement x) ≤ y := by
  have forward (u v : Icc (0 : ℝ) 1)
      (h : crossingComparisonIso a ha (unitIntervalComplement v) ≤ u) :
      crossingComparisonIso a ha (unitIntervalComplement u) ≤ v := by
    have h₁ : unitIntervalComplement u ≤
        crossingComparisonFlip a ha (unitIntervalComplement v) := by
      change 1 - (u : ℝ) ≤ 1 - (crossingComparisonIso a ha (unitIntervalComplement v) : ℝ)
      have h' : (crossingComparisonIso a ha (unitIntervalComplement v) : ℝ) ≤ (u : ℝ) := h
      linarith
    have h₂ := (crossingComparisonFlip_antitone a ha) h₁
    rw [crossingComparisonFlip_involutive a ha] at h₂
    change 1 - (v : ℝ) ≤ 1 - (crossingComparisonIso a ha (unitIntervalComplement u) : ℝ) at h₂
    change (crossingComparisonIso a ha (unitIntervalComplement u) : ℝ) ≤ (v : ℝ)
    linarith
  exact ⟨forward x y, forward y x⟩

/-- Increasing the exponent decreases the crossing comparison function. -/
theorem crossingComparisonIso_le_of_le_exponent {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x : Icc (0 : ℝ) 1) :
    (crossingComparisonIso b (lt_of_lt_of_le ha hab) x : ℝ) ≤
      (crossingComparisonIso a ha x : ℝ) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hx0 : 0 ≤ 1 - (x : ℝ) := by linarith [x.property.2]
  have hx1 : 1 - (x : ℝ) ≤ 1 := by linarith [x.property.1]
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb ha).2 hab
  have hroot : (1 - (x : ℝ)) ^ a⁻¹ ≤ (1 - (x : ℝ)) ^ b⁻¹ :=
    Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (inv_pos.mpr hb).le hinv
  have hbase0 : 0 ≤ 1 - (1 - (x : ℝ)) ^ b⁻¹ :=
    sub_nonneg.mpr (Real.rpow_le_one hx0 hx1 (inv_pos.mpr hb).le)
  have hbase1 : 1 - (1 - (x : ℝ)) ^ b⁻¹ ≤ 1 := by
    linarith [Real.rpow_nonneg hx0 b⁻¹]
  have hbase : 1 - (1 - (x : ℝ)) ^ b⁻¹ ≤ 1 - (1 - (x : ℝ)) ^ a⁻¹ := by
    linarith
  rw [crossingComparisonIso_apply, crossingComparisonIso_apply]
  exact (Real.rpow_le_rpow_of_exponent_ge' hbase0 hbase1 ha.le hab).trans
    (Real.rpow_le_rpow hbase0 hbase ha.le)

end Sandpile.External.RSW
