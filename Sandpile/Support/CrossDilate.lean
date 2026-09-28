import Sandpile.Support.CrossBallScaleLaw

/-!
# Dilating a crossing event

The geometric half of `eq:rescaled-crossing-estimate` (`sandpile.tex:2404-2413`): a
crossing of a rectangle by a superlevel set of a field is the same thing as a crossing of
the dilated rectangle by the superlevel set of the dilated field.

  "Indeed, if `R = h/s`, then the event in `eq:rescaled-crossing-estimate` has the same
   probability as `H_{[-(a/h)R,(a/h)R]×[0,2R]}(Lh/R)`."

That sentence is the change of variables `u = s w` applied to the crossing event. Here it
is proved as a statement about the events themselves, in both directions
(`crosses_smul_level` and its converse `crosses_of_smul_level`, built from `crosses_smul`
and `image_smul_setOf`), so nothing about the law of the field is used: a dilation of the
plane is a homeomorphism, it carries a compact connected subset of a rectangle to a compact
connected subset of the dilated rectangle, and it carries the superlevel set of `f` to the
superlevel set of `w ↦ f(a⁻¹ w)`.

What this does NOT do is compare the probabilities of the two events, which is where the
scaling in law of `Sandpile/Support/CrossBallScaleLaw.lean` enters, and which has to pass
through the chain events of `Sandpile/Support/CrossUnion.lean` because a crossing event is
not known to be measurable.
-/

open MeasureTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- A crossing dilates to a crossing: the image of the witness under `z ↦ a z`
is compact and connected, lies in the dilated rectangle because every coordinate
inequality survives multiplication by a positive number, and meets the two
dilated sides. -/
theorem crosses_smul {a : ℝ} (ha : 0 < a) {p q : Fin 2 → ℝ} {i : Fin 2}
    {S : Set (Sandpile.Continuum.Space 2)} (h : Crosses p q i S) :
    Crosses (fun j => a * p j) (fun j => a * q j) i
      ((fun z : Sandpile.Continuum.Space 2 => a • z) '' S) := by
  obtain ⟨Γ, hsub, hcpt, hconn, ⟨x, hx, hxa⟩, ⟨y, hy, hyb⟩⟩ := h
  refine ⟨(fun z : Sandpile.Continuum.Space 2 => a • z) '' Γ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzS, hzR⟩ := hsub hz
    refine ⟨⟨z, hzS, rfl⟩, ?_⟩
    intro j
    have hj := hzR j
    exact ⟨mul_le_mul_of_nonneg_left hj.1 (le_of_lt ha),
      mul_le_mul_of_nonneg_left hj.2 (le_of_lt ha)⟩
  · exact hcpt.image (continuous_const_smul a)
  · exact hconn.image _ (Continuous.continuousOn (continuous_const_smul a))
  · exact ⟨a • x, ⟨x, hx, rfl⟩, by show a * x i = a * p i; rw [hxa]⟩
  · exact ⟨a • y, ⟨y, hy, rfl⟩, by show a * y i = a * q i; rw [hyb]⟩

/-- The dilated superlevel set is the superlevel set of the dilated field. -/
theorem image_smul_setOf {a : ℝ} (ha : 0 < a) (f : Sandpile.Continuum.Space 2 → ℝ) (l : ℝ) :
    (fun z : Sandpile.Continuum.Space 2 => a • z) '' {u | l ≤ f u}
      = {w | l ≤ f (a⁻¹ • w)} := by
  have hane : a ≠ 0 := ne_of_gt ha
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    show l ≤ f (a⁻¹ • (a • z))
    rwa [inv_smul_smul₀ hane]
  · intro hw
    refine ⟨a⁻¹ • w, hw, ?_⟩
    exact smul_inv_smul₀ hane w

/-- A crossing of a rectangle at a level, read on the dilated rectangle for the
dilated field. -/
theorem crosses_smul_level {a : ℝ} (ha : 0 < a) {p q : Fin 2 → ℝ} {i : Fin 2}
    (f : Sandpile.Continuum.Space 2 → ℝ) (l : ℝ) (h : Crosses p q i {u | l ≤ f u}) :
    Crosses (fun j => a * p j) (fun j => a * q j) i {w | l ≤ f (a⁻¹ • w)} := by
  rw [← image_smul_setOf ha f l]
  exact crosses_smul ha h

/-- The converse: a crossing of the dilated rectangle by the dilated field is a
crossing of the rectangle. -/
theorem crosses_of_smul_level {a : ℝ} (ha : 0 < a) {p q : Fin 2 → ℝ} {i : Fin 2}
    (f : Sandpile.Continuum.Space 2 → ℝ) (l : ℝ)
    (h : Crosses (fun j => a * p j) (fun j => a * q j) i {w | l ≤ f (a⁻¹ • w)}) :
    Crosses p q i {u | l ≤ f u} := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hinv : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha
  have h2 := crosses_smul_level hinv (fun w => f (a⁻¹ • w)) l h
  have hset : {w : Sandpile.Continuum.Space 2 | l ≤ f (a⁻¹ • (a⁻¹)⁻¹ • w)} = {u | l ≤ f u} := by
    ext w
    show l ≤ f (a⁻¹ • (a⁻¹)⁻¹ • w) ↔ l ≤ f w
    rw [inv_inv, inv_smul_smul₀ hane]
  have hcorner : ∀ r : Fin 2 → ℝ, (fun j => a⁻¹ * (a * r j)) = r := by
    intro r
    funext j
    rw [inv_mul_cancel_left₀ hane]
  rw [hset, hcorner p, hcorner q] at h2
  exact h2

end Sandpile.Frozen.FixedScaleCrossings
