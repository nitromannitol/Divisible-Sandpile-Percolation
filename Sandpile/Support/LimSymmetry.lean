/-
From the crossing bound on the rectangles `[-al,al]×[0,2h]` in the left-right
direction to the same bound on an arbitrary axis-parallel rectangle in either
coordinate direction.

`prop:fixed-scale-crossings` (`sandpile.tex:2119-2135`) and the rescaled estimate
(`sandpile.tex:2429-2436`) are stated for the rectangles `[-a,a]×[0,2h]` crossed
left-right, while Step 1 of `lem:finite-scale-extraction`
(`sandpile.tex:2431-2484`) is applied to an arbitrary rectangle and either
crossing direction.  The passage is the invariance in law of the field asserted
at `sandpile.tex:2103-2104`:

  "The unit-scale field `𝒳_1` is stationary, sign-symmetric, invariant under
   rotations by `π/2` and coordinate reflections, and has dependence range `2`."

which for the ball fields is `Sandpile.Frozen.FixedScaleCrossings.isSymmetricField_ballField`.

The crossing event is not known to be measurable, so equality in law does not
transfer it directly; the chain events of `Sandpile/Support/CrossUnion.lean`
bracket it at two levels a distance `ε` apart, and the transfer therefore costs
`ε` in the level.  That is the same device as
`Sandpile/Support/LimTransfer.lean`, here between two fields on ONE space rather
than between two spaces.

The symmetry that does the work is `rectSymmetry`: the plane symmetry which
interchanges the two coordinates when the prescribed direction is the vertical
one and then translates the centred rectangle onto the prescribed one.
-/
import Sandpile.Support.LimTransfer
import Sandpile.Support.CrossSymmetry

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A crossing of one rectangle, for the field read through a plane symmetry, is
a crossing of the image rectangle in the image direction. -/
theorem crosses_image_of_symmetry {T : Sandpile.Continuum.PlaneSymmetry}
    {a' b' a b : Fin 2 → ℝ} {i : Fin 2} {S : Set (Sandpile.Continuum.Space 2)}
    (hrect : ∀ p ∈ rectSet a' b', T.toFun p ∈ rectSet a b)
    (hface0 : ∀ p : Sandpile.Continuum.Space 2, p 0 = a' 0 → (T.toFun p) i = a i)
    (hface1 : ∀ p : Sandpile.Continuum.Space 2, p 0 = b' 0 → (T.toFun p) i = b i)
    (h : Crosses a' b' 0 (T.toFun ⁻¹' S)) : Crosses a b i S := by
  obtain ⟨Γ, hsub, hcomp, hconn, ⟨p, hp, hpa⟩, ⟨q, hq, hqb⟩⟩ := h
  have hcont : Continuous T.toFun := continuous_planeSymmetry T
  refine ⟨T.toFun '' Γ, ?_, hcomp.image hcont, hconn.image _ hcont.continuousOn,
    ⟨T.toFun p, ⟨p, hp, rfl⟩, hface0 p hpa⟩, ⟨T.toFun q, ⟨q, hq, rfl⟩, hface1 q hqb⟩⟩
  rintro w ⟨u, huΓ, rfl⟩
  obtain ⟨h1, h2⟩ := hsub huΓ
  exact ⟨h1, hrect u h2⟩

/-- The plane symmetry carrying `[-al,al]×[0,2h]`, crossed left-right, onto the
rectangle with corners `a` and `b`, crossed in the direction `i`. -/
noncomputable def rectSymmetry (a b : Fin 2 → ℝ) (i : Fin 2) :
    Sandpile.Continuum.PlaneSymmetry where
  perm := Equiv.swap 0 i
  sign := fun _ => 1
  sign_eq := fun _ => Or.inl rfl
  shift := fun k => if k = i then (a i + b i) / 2 else a k

theorem rectSymmetry_apply_i (a b : Fin 2 → ℝ) (i : Fin 2) (p : Sandpile.Continuum.Space 2) :
    (rectSymmetry a b i).toFun p i = p 0 + (a i + b i) / 2 := by
  have h : (Equiv.swap (0 : Fin 2) i) i = 0 := by fin_cases i <;> decide
  simp [Sandpile.Continuum.PlaneSymmetry.toFun_apply, rectSymmetry, h]

theorem rectSymmetry_apply_swap (a b : Fin 2 → ℝ) (i : Fin 2)
    (p : Sandpile.Continuum.Space 2) :
    (rectSymmetry a b i).toFun p (swapIdx i) = p 1 + a (swapIdx i) := by
  have h : (Equiv.swap (0 : Fin 2) i) (swapIdx i) = 1 := by fin_cases i <;> decide
  have hne : swapIdx i ≠ i := by fin_cases i <;> decide
  simp [Sandpile.Continuum.PlaneSymmetry.toFun_apply, rectSymmetry, h, hne]

/-- The lower corner of the centred rectangle the symmetry starts from. -/
noncomputable def centLo (a b : Fin 2 → ℝ) (i : Fin 2) : Fin 2 → ℝ := ![-((b i - a i) / 2), 0]

/-- Its upper corner. -/
noncomputable def centHi (a b : Fin 2 → ℝ) (i : Fin 2) : Fin 2 → ℝ :=
  ![(b i - a i) / 2, 2 * ((b (swapIdx i) - a (swapIdx i)) / 2)]

theorem centLo_zero (a b : Fin 2 → ℝ) (i : Fin 2) :
    centLo a b i 0 = -((b i - a i) / 2) := rfl

theorem centLo_one (a b : Fin 2 → ℝ) (i : Fin 2) : centLo a b i 1 = 0 := rfl

theorem centHi_zero (a b : Fin 2 → ℝ) (i : Fin 2) :
    centHi a b i 0 = (b i - a i) / 2 := rfl

theorem centHi_one (a b : Fin 2 → ℝ) (i : Fin 2) :
    centHi a b i 1 = 2 * ((b (swapIdx i) - a (swapIdx i)) / 2) := rfl

theorem rectSymmetry_maps_rect (a b : Fin 2 → ℝ) (i : Fin 2)
    (p : Sandpile.Continuum.Space 2) (hp : p ∈ rectSet (centLo a b i) (centHi a b i)) :
    (rectSymmetry a b i).toFun p ∈ rectSet a b := by
  have h0 := hp 0
  have h1 := hp 1
  rw [centLo_zero, centHi_zero] at h0
  rw [centLo_one, centHi_one] at h1
  intro k
  rcases (show k = i ∨ k = swapIdx i by fin_cases i <;> fin_cases k <;> decide) with rfl | rfl
  · rw [rectSymmetry_apply_i]
    constructor <;> linarith [h0.1, h0.2]
  · rw [rectSymmetry_apply_swap]
    constructor <;> linarith [h1.1, h1.2]

theorem rectSymmetry_face_lo (a b : Fin 2 → ℝ) (i : Fin 2)
    (p : Sandpile.Continuum.Space 2) (hp : p 0 = centLo a b i 0) :
    ((rectSymmetry a b i).toFun p) i = a i := by
  rw [centLo_zero] at hp
  rw [rectSymmetry_apply_i, hp]
  ring

theorem rectSymmetry_face_hi (a b : Fin 2 → ℝ) (i : Fin 2)
    (p : Sandpile.Continuum.Space 2) (hp : p 0 = centHi a b i 0) :
    ((rectSymmetry a b i).toFun p) i = b i := by
  rw [centHi_zero] at hp
  rw [rectSymmetry_apply_i, hp]
  ring

/-- The crossing bound on the centred rectangle gives the crossing bound on an
arbitrary rectangle in either direction, at a level lower by `ε`. -/
theorem measure_crossing_general_of_symmetric {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hX : ∀ u, Measurable (X u))
    (hcX : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    {a b : Fin 2 → ℝ} (hab : ∀ k, a k < b k) (i : Fin 2) {pr l ε : ℝ} (hε : 0 < ε)
    (hcent : ENNReal.ofReal pr ≤
      P {ω | Crosses (centLo a b i) (centHi a b i) 0 {u | l ≤ X u ω}}) :
    ENNReal.ofReal pr ≤ P {ω | Crosses a b i {u | l - ε ≤ X u ω}} := by
  set T := rectSymmetry a b i with hT
  set Y : Sandpile.Continuum.Space 2 → Ω → ℝ := fun u ω => X (T.toFun u) ω with hY
  have hYm : ∀ u, Measurable (Y u) := fun u => hX (T.toFun u)
  have hYc : ∀ᵐ ω ∂P, Continuous fun u => Y u ω := by
    filter_upwards [hcX] with ω hω
    exact hω.comp (continuous_planeSymmetry T)
  have hlaw : Sandpile.Continuum.fieldLaw P X = Sandpile.Continuum.fieldLaw P Y := by
    have h := hsym T 1 (Or.inl rfl)
    have hfun : (fun (u : Sandpile.Continuum.Space 2) (ω : Ω) => (1 : ℝ) * X (T.toFun u) ω) = Y := by
      funext u ω; rw [one_mul]
    rw [hfun] at h
    exact h.symm
  have hlo : centLo a b i 0 < centHi a b i 0 := by
    have h := hab i
    rw [centLo_zero, centHi_zero]
    linarith
  have hhi : centLo a b i 1 < centHi a b i 1 := by
    have h := hab (swapIdx i)
    rw [centLo_one, centHi_one]
    linarith
  have hbracket : P {ω | Crosses (centLo a b i) (centHi a b i) 0 {u | l ≤ X u ω}}
      ≤ P {ω | Crosses (centLo a b i) (centHi a b i) 0 {u | l - ε ≤ Y u ω}} :=
    calc P {ω | Crosses (centLo a b i) (centHi a b i) 0 {u | l ≤ X u ω}}
        ≤ P (crossApprox X (centLo a b i) (centHi a b i) 0 (l - ε)) :=
          measure_crossing_le_crossApprox P hlo hhi hε hcX
      _ = P (crossApprox Y (centLo a b i) (centHi a b i) 0 (l - ε)) :=
          measure_crossApprox_eq_of_fieldLaw P P X Y hX hYm hlaw _ _ 0 (l - ε)
      _ ≤ P {ω | Crosses (centLo a b i) (centHi a b i) 0 {u | l - ε ≤ Y u ω}} :=
          measure_crossApprox_le_crossing P hYc
  refine le_trans hcent (le_trans hbracket (measure_mono ?_))
  intro ω hω
  exact crosses_image_of_symmetry (rectSymmetry_maps_rect a b i)
    (rectSymmetry_face_lo a b i) (rectSymmetry_face_hi a b i) hω

end Sandpile.Support
