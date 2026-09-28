import Sandpile.Support.CrossRescale

/-!
# The chain vocabulary under a rational translation

The chain vocabulary of `Sandpile/Support/CrossUnion.lean` under a translation
of the plane by a vector with rational coordinates.

`Sandpile/Support/CrossRescale.lean` does the same for a rational dilation, and
for the same reason: an admissible vertex has each coordinate rational or on a
side of the rectangle, and a translation by a rational vector preserves both
alternatives while an irrational one destroys the first.  The two together move
a chain event of one rectangle to a chain event of any rectangle obtained from
it by a rational dilation followed by a rational translation, as EQUAL subsets
of the probability space.

This is what the circuit of `sandpile.tex:2229` needs: the four rectangles of an
annulus `B(x,4ρ) \ B(x,ρ)` are translates of the two rectangles anchored at the
origin, and the uniform crossing estimate of
`Sandpile.Support.uniform_crossing_constant` is stated only for the anchored
ones.
-/

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The point of the plane with the prescribed rational coordinates. -/
noncomputable def ratPoint (r : Fin 2 → ℚ) : Sandpile.Continuum.Space 2 :=
  WithLp.toLp 2 (fun k : Fin 2 => (r k : ℝ))

/-- The `k`-th coordinate of `ratPoint r` is `r k` cast to `ℝ`. -/
theorem ratPoint_apply (r : Fin 2 → ℚ) (k : Fin 2) : ratPoint r k = (r k : ℝ) := rfl

/-- A point of a segment translates with the segment. -/
theorem segPt_add (w₀ : Sandpile.Continuum.Space 2) (v w : Sandpile.Continuum.Space 2) (t : ℝ) :
    segPt (v + w₀) (w + w₀) t = segPt v w t + w₀ := by
  unfold segPt
  rw [add_sub_add_right_eq_sub]
  abel

/-- A segment translates to the segment between the translated endpoints. -/
theorem segSet_add (w₀ : Sandpile.Continuum.Space 2) (v w : Sandpile.Continuum.Space 2) :
    segSet (v + w₀) (w + w₀)
      = (fun z : Sandpile.Continuum.Space 2 => z + w₀) '' segSet v w := by
  unfold segSet
  rw [← Set.image_comp]
  exact Set.image_congr fun t _ => segPt_add w₀ v w t

/-- A chain of segments translates to the chain through the translated
vertices. -/
theorem pathSet_add (w₀ : Sandpile.Continuum.Space 2) (n : ℕ)
    (v : ℕ → Sandpile.Continuum.Space 2) :
    pathSet n (fun j => v j + w₀)
      = (fun z : Sandpile.Continuum.Space 2 => z + w₀) '' pathSet n v := by
  unfold pathSet
  rw [Set.image_iUnion₂]
  exact Set.iUnion₂_congr fun j _ => segSet_add w₀ (v j) (v (j + 1))

/-- The chain event of the translated chain for the translated field is the
chain event of the chain for the field. -/
theorem pathEvent_add {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (w₀ : Sandpile.Continuum.Space 2) (l : ℝ) (n : ℕ)
    (v : ℕ → Sandpile.Continuum.Space 2) :
    pathEvent (fun w ω => X (w - w₀) ω) l n (fun j => v j + w₀) = pathEvent X l n v := by
  unfold pathEvent
  ext ω
  constructor
  · intro h j q hj hq0 hq1
    have h2 : l ≤ X (segPt (v j + w₀) (v (j + 1) + w₀) (q : ℝ) - w₀) ω := h j q hj hq0 hq1
    rwa [segPt_add w₀ (v j) (v (j + 1)) (q : ℝ), add_sub_cancel_right] at h2
  · intro h j q hj hq0 hq1
    show l ≤ X (segPt (v j + w₀) (v (j + 1) + w₀) (q : ℝ) - w₀) ω
    rw [segPt_add w₀ (v j) (v (j + 1)) (q : ℝ), add_sub_cancel_right]
    exact h j q hj hq0 hq1

/-- A translation by a vector with RATIONAL coordinates preserves admissibility
of a vertex: a rational coordinate stays rational and a coordinate on a side
stays on the translated side. -/
theorem vertexOK_add {a b : Fin 2 → ℝ} {p : Sandpile.Continuum.Space 2} (r : Fin 2 → ℚ)
    (h : VertexOK a b p) :
    VertexOK (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ)) (p + ratPoint r) := by
  intro k
  have hpk : (p + ratPoint r) k = p k + (r k : ℝ) := rfl
  rcases h k with ⟨q, hq⟩ | hk | hk
  · exact Or.inl ⟨q + r k, by rw [hpk, hq]; push_cast; ring⟩
  · exact Or.inr (Or.inl (by rw [hpk, hk]))
  · exact Or.inr (Or.inr (by rw [hpk, hk]))

/-- A rectangle translates to the rectangle between the translated corners. -/
theorem rectSet_add (w₀ : Sandpile.Continuum.Space 2) (a b : Fin 2 → ℝ) :
    rectSet (fun k => a k + w₀ k) (fun k => b k + w₀ k)
      = (fun z : Sandpile.Continuum.Space 2 => z + w₀) '' rectSet a b := by
  ext w
  constructor
  · intro hw
    refine ⟨w - w₀, ?_, sub_add_cancel w w₀⟩
    intro k
    have h := hw k
    have hk : (w - w₀) k = w k - w₀ k := rfl
    rw [hk]
    constructor
    · linarith [h.1]
    · linarith [h.2]
  · rintro ⟨z, hz, rfl⟩
    intro k
    have h := hz k
    have hk : (z + w₀) k = z k + w₀ k := rfl
    rw [hk]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The chain of translated vertices, for a rational translation. -/
noncomputable def addChain {a b : Fin 2 → ℝ} (r : Fin 2 → ℚ) (ch : VertexChain a b) :
    VertexChain (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ)) :=
  ⟨ch.1, fun j => ⟨(ch.2 j : Sandpile.Continuum.Space 2) + ratPoint r,
    vertexOK_add r (ch.2 j).2⟩⟩

/-- The chain event depends only on the vertices actually used. -/
theorem pathEvent_congr {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (l : ℝ) (n : ℕ)
    (v w : ℕ → Sandpile.Continuum.Space 2) (h : ∀ j ≤ n, v j = w j) :
    pathEvent X l n v = pathEvent X l n w := by
  unfold pathEvent
  ext ω
  constructor
  · intro hh j q hj hq0 hq1
    rw [← h j (by omega), ← h (j + 1) (by omega)]
    exact hh j q hj hq0 hq1
  · intro hh j q hj hq0 hq1
    rw [h j (by omega), h (j + 1) (by omega)]
    exact hh j q hj hq0 hq1

/-- The translated chain reads as the translate of the chain, at the indices the
chain uses. -/
theorem chainFun_addChain {a b : Fin 2 → ℝ} (r : Fin 2 → ℚ) (ch : VertexChain a b) (j : ℕ)
    (hj : j < ch.1 + 2) :
    chainFun (addChain r ch) j = chainFun ch j + ratPoint r := by
  unfold chainFun addChain
  simp [hj]

/-- A chain that crosses the rectangle translates to a chain that crosses the
translated rectangle. -/
theorem goodChain_addChain {a b : Fin 2 → ℝ} {i : Fin 2} (r : Fin 2 → ℚ)
    {ch : VertexChain a b} (h : GoodChain a b i ch) :
    GoodChain (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ)) i (addChain r ch) := by
  obtain ⟨hsub, h0, h1⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hcongr : pathSet (ch.1 + 1) (chainFun (addChain r ch))
        = pathSet (ch.1 + 1) (fun j => chainFun ch j + ratPoint r) :=
      pathSet_congr _ _ _ fun j hj => chainFun_addChain r ch j (by omega)
    have hps : pathSet ((addChain r ch).1 + 1) (chainFun (addChain r ch))
        = (fun z : Sandpile.Continuum.Space 2 => z + ratPoint r) ''
          pathSet (ch.1 + 1) (chainFun ch) := by
      rw [show (addChain r ch).1 = ch.1 from rfl, hcongr]
      exact pathSet_add _ _ _
    have hrect : rectSet (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ))
        = (fun z : Sandpile.Continuum.Space 2 => z + ratPoint r) '' rectSet a b :=
      rectSet_add (ratPoint r) a b
    rw [hps, hrect]
    exact Set.image_mono hsub
  · rw [chainFun_addChain r ch 0 (by omega)]
    show chainFun ch 0 i + (r i : ℝ) = a i + (r i : ℝ)
    rw [h0]
  · rw [show (addChain r ch).1 = ch.1 from rfl, chainFun_addChain r ch (ch.1 + 1) (by omega)]
    show chainFun ch (ch.1 + 1) i + (r i : ℝ) = b i + (r i : ℝ)
    rw [h1]

/-- Every chain event of the rectangle is a chain event of the translated
rectangle for the translated field. -/
theorem crossApprox_subset_add {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {a b : Fin 2 → ℝ} (i : Fin 2) (l : ℝ)
    (r : Fin 2 → ℚ) :
    crossApprox X a b i l
      ⊆ crossApprox (fun w ω => X (w - ratPoint r) ω)
          (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ)) i l := by
  intro ω hω
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hω
  refine Set.mem_iUnion.mpr ⟨⟨addChain r ch.1, goodChain_addChain r ch.2⟩, ?_⟩
  show ω ∈ pathEvent (fun w ω => X (w - ratPoint r) ω) l ((addChain r ch.1).1 + 1)
    (chainFun (addChain r ch.1))
  have hcongr : pathEvent (fun w ω => X (w - ratPoint r) ω) l (ch.1.1 + 1)
        (chainFun (addChain r ch.1))
      = pathEvent (fun w ω => X (w - ratPoint r) ω) l (ch.1.1 + 1)
        (fun j => chainFun ch.1 j + ratPoint r) :=
    pathEvent_congr _ _ _ _ _ fun j hj => chainFun_addChain r ch.1 j (by omega)
  rw [show (addChain r ch.1).1 = ch.1.1 from rfl, hcongr,
    pathEvent_add X (ratPoint r) l (ch.1.1 + 1) (chainFun ch.1)]
  exact hch

/-- The chain events are covariant under a rational translation: applying the
inclusion in both directions gives equality of the two events, as subsets of the
same probability space. -/
theorem crossApprox_add {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {a b : Fin 2 → ℝ} (i : Fin 2) (l : ℝ)
    (r : Fin 2 → ℚ) :
    crossApprox (fun w ω => X (w - ratPoint r) ω)
        (fun k => a k + (r k : ℝ)) (fun k => b k + (r k : ℝ)) i l
      = crossApprox X a b i l := by
  refine Set.Subset.antisymm ?_ (crossApprox_subset_add X i l r)
  have h := crossApprox_subset_add (fun w ω => X (w - ratPoint r) ω)
      (a := fun k => a k + (r k : ℝ)) (b := fun k => b k + (r k : ℝ)) i l (fun k => -(r k))
  have hpt : ratPoint (fun k => -(r k)) = -ratPoint r := by
    ext k
    simp [ratPoint]
  have hfield : (fun (w : Sandpile.Continuum.Space 2) (ω : Ω) =>
      X (w - ratPoint (fun k => -(r k)) - ratPoint r) ω) = X := by
    funext w ω
    rw [hpt]
    congr 1
    abel
  have hcorner : ∀ s : Fin 2 → ℝ, (fun k => s k + (r k : ℝ) + (((-(r k) : ℚ)) : ℝ)) = s := by
    intro s
    funext k
    push_cast
    ring
  rw [hfield, hcorner a, hcorner b] at h
  exact h

end Sandpile.Support
