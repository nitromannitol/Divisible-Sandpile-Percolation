import Sandpile.Support.CrossCameronMartin
import Sandpile.Support.CrossLocalEvents
import Sandpile.Support.CrossBallMemLp

/-!
# The Cameron-Martin shift on the crossing event

The Cameron-Martin shift read on the crossing event of Step 3 of `prop:fixed-scale-crossings`
(`sandpile.tex:2337-2350`): since the unit kernel has mass `𝔪`, the shift raises every field
value used by the exploration by `ℓ`, so by sign symmetry, for `ℓ ≥ 0`,
`P({𝒳₁<ℓ} crosses) = P_ℓ(E_R(θ))`. The measurable representative `closedCrossEvent` of the
crossing is a countable intersection of countable unions of countable intersections of single
field values, so it is the preimage, under the map that reads the whole field, of one event
`evalCrossEvent` on the function space. Three facts are proved and combined:
`closedCrossEvent_preimage_eval` identifies the crossing event with that preimage;
`closedCrossEvent_congr_rect` shows it depends only on the field inside the rectangle, because
every point a chain event evaluates lies on the chain, which a good chain keeps inside; and
`closedCrossEvent_add_const` shows adding a constant to the field lowers the level by it.
Together with `whiteNoise_tilted_map_shift` these give `whiteNoise_tilted_closedCrossEvent`:
the tilt by `a𝒲(k) - a²‖k‖²/2` moves the crossing at level `l` to the crossing at level
`l - a𝔪`, whenever every unit kernel of the rectangle pairs with `k` to the mass `𝔪`.
-/

open MeasureTheory ProbabilityTheory Set
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The canonical crossing event on the space of all planar fields. -/
noncomputable def evalCrossEvent (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    Set (Space 2 → ℝ) :=
  closedCrossEvent (fun (u : Space 2) (f : Space 2 → ℝ) => f u) a b i l

/-- The canonical crossing event `evalCrossEvent` is measurable, being built as a countable
intersection of countable unions of preimages of the coordinate evaluation maps. -/
theorem measurableSet_evalCrossEvent (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    MeasurableSet (evalCrossEvent a b i l) :=
  measurableSet_closedCrossEvent_local _ a b i l fun x _ => measurable_pi_apply x

/-- The crossing event is the preimage of the canonical one under the map that reads the
whole field. -/
theorem closedCrossEvent_preimage_eval {Ω : Type*} [MeasurableSpace Ω]
    (X : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    closedCrossEvent X a b i l
      = (fun ω => fun u : Space 2 => X u ω) ⁻¹' evalCrossEvent a b i l := by
  unfold evalCrossEvent closedCrossEvent crossApprox
  simp only [Set.preimage_iInter, Set.preimage_iUnion]
  rfl

/-- A good chain evaluates the field only at points of the rectangle, so the crossing event
depends only on the field there. -/
theorem closedCrossEvent_congr_rect {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ)
    (h : ∀ u ∈ rectSet a b, X u = Y u) :
    closedCrossEvent X a b i l = closedCrossEvent Y a b i l := by
  have hpath : ∀ (l' : ℝ) (ch : {ch : VertexChain a b // GoodChain a b i ch}),
      pathEvent X l' (ch.1.1 + 1) (chainFun ch.1)
        = pathEvent Y l' (ch.1.1 + 1) (chainFun ch.1) := by
    intro l' ch
    have hmem : ∀ (j : ℕ) (q : ℚ), j < ch.1.1 + 1 → 0 ≤ q → q ≤ 1 →
        segPt (chainFun ch.1 j) (chainFun ch.1 (j + 1)) (q : ℝ) ∈ rectSet a b := by
      intro j q hj hq0 hq1
      exact ch.2.1 (Set.mem_biUnion (Finset.mem_range.mpr hj)
        ⟨(q : ℝ), ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩, rfl⟩)
    ext ω
    simp only [pathEvent, Set.mem_setOf_eq]
    constructor
    · intro hh j q hj hq0 hq1
      have := hh j q hj hq0 hq1
      rwa [h _ (hmem j q hj hq0 hq1)] at this
    · intro hh j q hj hq0 hq1
      have := hh j q hj hq0 hq1
      rwa [← h _ (hmem j q hj hq0 hq1)] at this
  unfold closedCrossEvent crossApprox
  exact Set.iInter_congr fun n => Set.iUnion_congr fun ch => hpath _ ch

/-- Adding a constant to the field lowers the crossing level by that constant. -/
theorem closedCrossEvent_add_const {Ω : Type*} [MeasurableSpace Ω]
    (X : Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l m : ℝ) :
    closedCrossEvent (fun u ω => X u ω + m) a b i l = closedCrossEvent X a b i (l - m) := by
  have hpath : ∀ (l' : ℝ) (n : ℕ) (v : ℕ → Space 2),
      pathEvent (fun u ω => X u ω + m) l' n v = pathEvent X (l' - m) n v := by
    intro l' n v
    ext ω
    simp only [pathEvent, Set.mem_setOf_eq]
    constructor
    · intro hh j q hj hq0 hq1
      have := hh j q hj hq0 hq1
      linarith
    · intro hh j q hj hq0 hq1
      have := hh j q hj hq0 hq1
      linarith
  unfold closedCrossEvent crossApprox
  refine Set.iInter_congr fun n => Set.iUnion_congr fun ch => ?_
  rw [hpath]
  congr 1
  ring

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {W : (Space d → ℝ) → Ω → ℝ}

/-- **The shift identity of Step 3.**  Tilting the white noise by `a𝒲(k) - a²‖k‖²/2` turns the
crossing of the unit ball field at level `l` into the crossing at level `l - a𝔪`, provided
every unit kernel of the rectangle pairs with `k` to the mass `𝔪`. -/
theorem whiteNoise_tilted_closedCrossEvent (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) {k : Space d → ℝ}
    (hk : MemLp k 2 (volume : Measure (Space d)))
    (hv : 0 < ∫ y : Space d, k y * k y) (a m : ℝ)
    (aa bb : Fin 2 → ℝ) (i : Fin 2) (l : ℝ)
    (hmass : ∀ u ∈ rectSet aa bb, (∫ y : Space d, ballKernel d 1 u y * k y) = m) :
    (P.tilted (fun ω => a * W k ω - a ^ 2 * (∫ y : Space d, k y * k y) / 2))
        (closedCrossEvent (ballField d W 1) aa bb i l)
      = P (closedCrossEvent (ballField d W 1) aa bb i (l - a * m)) := by
  classical
  set g : Space 2 → (Space d → ℝ) := fun u => ballKernel d 1 u with hgdef
  have hg : ∀ u, MemLp (g u) 2 (volume : Measure (Space d)) :=
    fun u => memLp_ballKernel hd one_pos u
  have hfieldmeas : Measurable fun ω => fun u : Space 2 => ballField d W 1 u ω :=
    measurable_pi_lambda _ fun u => hW.meas _ (hg u)
  have hshiftmeas : Measurable fun ω => fun u : Space 2 =>
      ballField d W 1 u ω + a * ∫ y : Space d, g u y * k y :=
    measurable_pi_lambda _ fun u => (hW.meas _ (hg u)).add_const _
  have hB := measurableSet_evalCrossEvent aa bb i l
  have hfeq : (fun ω => fun u : Space 2 => ballField d W 1 u ω)
      = fun ω => fun t : Space 2 => W (g t) ω := rfl
  have hfeq2 : (fun ω => fun t : Space 2 => W (g t) ω + a * ∫ y : Space d, g t y * k y)
      = fun ω => fun u : Space 2 =>
          ballField d W 1 u ω + a * ∫ y : Space d, g u y * k y := rfl
  rw [closedCrossEvent_preimage_eval, ← Measure.map_apply hfieldmeas hB, hfeq,
    whiteNoise_tilted_map_shift hW hk hv g hg a, hfeq2, Measure.map_apply hshiftmeas hB,
    ← closedCrossEvent_preimage_eval
      (fun u ω => ballField d W 1 u ω + a * ∫ y : Space d, g u y * k y) aa bb i l]
  congr 1
  rw [closedCrossEvent_congr_rect
    (fun u ω => ballField d W 1 u ω + a * ∫ y : Space d, g u y * k y)
    (fun u ω => ballField d W 1 u ω + a * m) aa bb i l ?_,
    closedCrossEvent_add_const]
  intro u hu
  funext ω
  rw [hmass u hu]

end Sandpile.Support
