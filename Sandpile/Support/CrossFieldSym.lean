/-
The symmetries of a planar field in the form the crossing estimates use them.

A crossing event of the field `X` on a translated rectangle is, as a subset of
the probability space, the crossing event of the TRANSLATED FIELD on the
original rectangle (`crossingSet_translate`).  The two sets are equal, not
merely of equal measure, so the identity holds for the outer measure of a
crossing event, which is not known to be measurable.  That is what replaces the
translation invariance of a law on the space of planar functions: equality in
law controls the measures of measurable sets only, and the crossing event is not
one of them.

What the symmetry hypothesis is then used for is to feed the cited crossing
comparison, `Sandpile.External.ContinuumRSW`, with the translated field: the
predicates `IsSymmetricField` and `IsAssociatedField` of
`Sandpile/Support/CrossField.lean` are stable under the plane symmetries
(`isSymmetricField_comp`, `isAssociatedField_comp`), because those symmetries
form a group, which is the content of `PlaneSymmetry.comp`.  Association is
stable under the spatial symmetries only; it is not preserved by the sign flip,
and nothing here claims that it is.
-/
import Sandpile.Support.CrossField
import Sandpile.Support.CrossTranslate

open MeasureTheory Set

namespace Sandpile.Continuum

namespace PlaneSymmetry

theorem comp_toFun (T S : PlaneSymmetry) (u : Space 2) :
    (T.comp S).toFun u = T.toFun (S.toFun u) := by
  ext k
  simp only [toFun_apply, comp, Equiv.trans_apply]
  ring

theorem translation_toFun (v u : Space 2) : (translation v).toFun u = u + v := by
  ext k
  simp [toFun_apply, translation]

end PlaneSymmetry

theorem measurable_fieldMap {Ω : Type*} [MeasurableSpace Ω]
    {X : Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u)) :
    Measurable (fun ω => (fun u => X u ω) : Ω → (Space 2 → ℝ)) :=
  measurable_pi_lambda _ hX

theorem measure_preimage_fieldLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Space 2 → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    {A : Set (Space 2 → ℝ)} (hA : MeasurableSet A) :
    P ((fun ω => (fun u => X u ω) : Ω → (Space 2 → ℝ)) ⁻¹' A) = fieldLaw P X A := by
  rw [fieldLaw, Measure.map_apply (measurable_fieldMap hX) hA]

theorem isSymmetricField_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Space 2 → Ω → ℝ} (hsym : IsSymmetricField P X) (S : PlaneSymmetry) (δ : ℝ)
    (hδ : δ = 1 ∨ δ = -1) : IsSymmetricField P (fun u ω => δ * X (S.toFun u) ω) := by
  intro T ε hε
  have hsign : ε * δ = 1 ∨ ε * δ = -1 := by
    rcases hε with h | h <;> rcases hδ with h' | h' <;> rw [h, h'] <;> norm_num
  have hfun : (fun (u : Space 2) (ω : Ω) => ε * (δ * X (S.toFun (T.toFun u)) ω))
      = fun (u : Space 2) (ω : Ω) => (ε * δ) * X ((S.comp T).toFun u) ω := by
    funext u ω
    rw [PlaneSymmetry.comp_toFun S T u]
    ring
  show fieldLaw P (fun u ω => ε * (δ * X (S.toFun (T.toFun u)) ω)) = _
  rw [hfun, hsym (S.comp T) (ε * δ) hsign, hsym S δ hδ]

theorem isAssociatedField_comp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Space 2 → Ω → ℝ} (hass : IsAssociatedField P X) (S : PlaneSymmetry) :
    IsAssociatedField P (fun u ω => X (S.toFun u) ω) := by
  intro k q f g hf hg hfm hgm hfb hgb
  exact hass k (fun i => S.toFun (q i)) f g hf hg hfm hgm hfb hgb

theorem isSymmetricField_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Space 2 → Ω → ℝ} (hsym : IsSymmetricField P X) (v : Space 2) :
    IsSymmetricField P (fun u ω => X (u + v) ω) := by
  have h := isSymmetricField_comp hsym (PlaneSymmetry.translation v) 1 (Or.inl rfl)
  have hfun : (fun (u : Space 2) (ω : Ω) => (1 : ℝ) * X ((PlaneSymmetry.translation v).toFun u) ω)
      = fun (u : Space 2) (ω : Ω) => X (u + v) ω := by
    funext u ω
    rw [PlaneSymmetry.translation_toFun, one_mul]
  rwa [hfun] at h

theorem isAssociatedField_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Space 2 → Ω → ℝ} (hass : IsAssociatedField P X) (v : Space 2) :
    IsAssociatedField P (fun u ω => X (u + v) ω) := by
  have h := isAssociatedField_comp hass (PlaneSymmetry.translation v)
  have hfun : (fun (u : Space 2) (ω : Ω) => X ((PlaneSymmetry.translation v).toFun u) ω)
      = fun (u : Space 2) (ω : Ω) => X (u + v) ω := by
    funext u ω
    rw [PlaneSymmetry.translation_toFun]
  rwa [hfun] at h

end Sandpile.Continuum

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

theorem crosses_translate_iff (v : Sandpile.Continuum.Space 2) (a b : Fin 2 → ℝ) (i : Fin 2)
    (S : Set (Sandpile.Continuum.Space 2)) :
    Crosses (fun k => a k + v k) (fun k => b k + v k) i S ↔
      Crosses a b i ((fun u => u + v) ⁻¹' S) := by
  constructor
  · intro hX
    have hback := crosses_translate (v := -v)
      (a := fun k => a k + v k) (b := fun k => b k + v k) (i := i)
      (S := (fun u : Sandpile.Continuum.Space 2 => u + v) ⁻¹' S)
      (by
        have hset : (fun u : Sandpile.Continuum.Space 2 => u + -v) ⁻¹'
            ((fun u : Sandpile.Continuum.Space 2 => u + v) ⁻¹' S) = S := by
          ext u; simp
        rw [hset]
        exact hX)
    have hA : (fun k => a k + v k + (-v) k) = a := by
      funext k; simp only [PiLp.neg_apply]; ring
    have hB : (fun k => b k + v k + (-v) k) = b := by
      funext k; simp only [PiLp.neg_apply]; ring
    rw [hA, hB] at hback
    exact hback
  · intro hX
    exact crosses_translate (v := v) hX

theorem crossingSet_translate {Ω : Type*} (X : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (v : Sandpile.Continuum.Space 2) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    {ω | Crosses (fun k => a k + v k) (fun k => b k + v k) i {u | l ≤ X u ω}}
      = {ω | Crosses a b i {u | l ≤ X (u + v) ω}} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  exact crosses_translate_iff v a b i {u | l ≤ X u ω}

end Sandpile.Support
