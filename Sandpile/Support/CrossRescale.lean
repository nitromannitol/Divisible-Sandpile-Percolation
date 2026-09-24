/-
The change of variables of `eq:rescaled-crossing-estimate`
(`sandpile.tex:2404-2413`) carried out on the chain events.

  "Indeed, if `R = h/s`, then the event in `eq:rescaled-crossing-estimate` has
   the same probability as `H_{[-(a/h)R,(a/h)R]×[0,2R]}(Lh/R)`."

`Sandpile/Support/CrossDilate.lean` does the geometry: a crossing of a rectangle
is a crossing of the dilated rectangle by the dilated set.  That alone does not
compare the two probabilities, because a crossing event is not known to be
measurable and the scaling of the field is a scaling IN LAW.  The comparison has
to be made on the chain events of `Sandpile/Support/CrossUnion.lean`, which are
measurable and which bracket the crossing event at two levels.

The chain vocabulary is covariant under a RATIONAL dilation and only under one:
an admissible vertex has each coordinate rational or on a side of the rectangle,
and a rational dilation preserves both alternatives while an irrational one
destroys the first.  That is the reason `lem:finite-scale-extraction` takes its
scales rational.
-/
import Sandpile.Support.CrossDilate
import Sandpile.Support.CrossUnion
import Sandpile.Support.CrossLaw

open MeasureTheory Set

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- A point of a segment dilates with the segment. -/
theorem segPt_smul (c : ℝ) (v w : Sandpile.Continuum.Space 2) (t : ℝ) :
    segPt (c • v) (c • w) t = c • segPt v w t := by
  unfold segPt
  rw [← smul_sub, smul_comm t c, ← smul_add]

/-- A segment dilates to the segment between the dilated endpoints. -/
theorem segSet_smul (c : ℝ) (v w : Sandpile.Continuum.Space 2) :
    segSet (c • v) (c • w) = (fun z : Sandpile.Continuum.Space 2 => c • z) '' segSet v w := by
  unfold segSet
  rw [← Set.image_comp]
  refine Set.image_congr (fun t _ => ?_)
  exact segPt_smul c v w t

/-- A chain of segments dilates to the chain through the dilated vertices. -/
theorem pathSet_smul (c : ℝ) (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    pathSet n (fun j => c • v j) = (fun z : Sandpile.Continuum.Space 2 => c • z) '' pathSet n v := by
  unfold pathSet
  rw [Set.image_iUnion₂]
  exact Set.iUnion₂_congr fun j _ => segSet_smul c (v j) (v (j + 1))

/-- The chain event of the dilated chain for the dilated field is the chain
event of the chain for the field. -/
theorem pathEvent_smul {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {c : ℝ} (hc : c ≠ 0) (l : ℝ) (n : ℕ)
    (v : ℕ → Sandpile.Continuum.Space 2) :
    pathEvent (fun w ω => X (c⁻¹ • w) ω) l n (fun j => c • v j) = pathEvent X l n v := by
  unfold pathEvent
  ext ω
  constructor
  · intro h j q hj hq0 hq1
    have h1 := h j q hj hq0 hq1
    have h2 : l ≤ X (c⁻¹ • segPt (c • v j) (c • v (j + 1)) (q : ℝ)) ω := h1
    rwa [segPt_smul c (v j) (v (j + 1)) (q : ℝ), inv_smul_smul₀ hc] at h2
  · intro h j q hj hq0 hq1
    show l ≤ X (c⁻¹ • segPt (c • v j) (c • v (j + 1)) (q : ℝ)) ω
    rw [segPt_smul c (v j) (v (j + 1)) (q : ℝ), inv_smul_smul₀ hc]
    exact h j q hj hq0 hq1

/-- A RATIONAL dilation preserves admissibility of a vertex: a rational
coordinate stays rational and a coordinate on a side stays on the dilated side.
This is where the rationality of the scales of `lem:finite-scale-extraction`
is used; a dilation by an irrational number destroys the rational coordinates
and the chain vocabulary is not covariant under it. -/
theorem vertexOK_smul {a b : Fin 2 → ℝ} {p : Sandpile.Continuum.Space 2} (c : ℚ)
    (h : VertexOK a b p) :
    VertexOK (fun k => (c : ℝ) * a k) (fun k => (c : ℝ) * b k) ((c : ℝ) • p) := by
  intro k
  have hpk : ((c : ℝ) • p) k = (c : ℝ) * p k := rfl
  rcases h k with ⟨q, hq⟩ | hk | hk
  · exact Or.inl ⟨c * q, by rw [hpk, hq]; push_cast; ring⟩
  · exact Or.inr (Or.inl (by rw [hpk, hk]))
  · exact Or.inr (Or.inr (by rw [hpk, hk]))


/-- A rectangle dilates to the rectangle between the dilated corners. -/
theorem rectSet_smul {c : ℝ} (hc : 0 < c) (a b : Fin 2 → ℝ) :
    rectSet (fun k => c * a k) (fun k => c * b k)
      = (fun z : Sandpile.Continuum.Space 2 => c • z) '' rectSet a b := by
  ext w
  constructor
  · intro hw
    refine ⟨c⁻¹ • w, ?_, smul_inv_smul₀ (ne_of_gt hc) w⟩
    intro k
    have h := hw k
    have hk : (c⁻¹ • w) k = c⁻¹ * w k := rfl
    rw [hk]
    constructor
    · rw [le_inv_mul_iff₀ hc]; exact h.1
    · rw [inv_mul_le_iff₀ hc]; exact h.2
  · rintro ⟨z, hz, rfl⟩
    intro k
    have h := hz k
    have hk : (c • z) k = c * z k := rfl
    rw [hk]
    exact ⟨mul_le_mul_of_nonneg_left h.1 (le_of_lt hc),
      mul_le_mul_of_nonneg_left h.2 (le_of_lt hc)⟩

/-- The chain of dilated vertices, for a rational dilation. -/
noncomputable def smulChain {a b : Fin 2 → ℝ} (c : ℚ) (ch : VertexChain a b) :
    VertexChain (fun k => (c : ℝ) * a k) (fun k => (c : ℝ) * b k) :=
  ⟨ch.1, fun j => ⟨(c : ℝ) • (ch.2 j : Sandpile.Continuum.Space 2),
    vertexOK_smul c (ch.2 j).2⟩⟩

/-- The dilated chain reads as the dilate of the chain. -/
theorem chainFun_smulChain {a b : Fin 2 → ℝ} (c : ℚ) (ch : VertexChain a b) (j : ℕ) :
    chainFun (smulChain c ch) j = (c : ℝ) • chainFun ch j := by
  unfold chainFun smulChain
  by_cases h : j < ch.1 + 2
  · simp [h]
  · simp [h]


/-- A chain that crosses the rectangle dilates to a chain that crosses the
dilated rectangle. -/
theorem goodChain_smulChain {a b : Fin 2 → ℝ} {i : Fin 2} {c : ℚ} (hc : 0 < (c : ℝ))
    {ch : VertexChain a b} (h : GoodChain a b i ch) :
    GoodChain (fun k => (c : ℝ) * a k) (fun k => (c : ℝ) * b k) i (smulChain c ch) := by
  obtain ⟨hsub, h0, h1⟩ := h
  have hcf : chainFun (smulChain c ch) = fun j => (c : ℝ) • chainFun ch j :=
    funext (chainFun_smulChain c ch)
  refine ⟨?_, ?_, ?_⟩
  · have hps : pathSet ((smulChain c ch).1 + 1) (chainFun (smulChain c ch))
        = (fun z : Sandpile.Continuum.Space 2 => (c : ℝ) • z) '' pathSet (ch.1 + 1) (chainFun ch) := by
      rw [show (smulChain c ch).1 = ch.1 from rfl, hcf]
      exact pathSet_smul _ _ _
    rw [hps, rectSet_smul hc]
    exact Set.image_mono hsub
  · rw [chainFun_smulChain]
    show (c : ℝ) * chainFun ch 0 i = (c : ℝ) * a i
    rw [h0]
  · rw [show (smulChain c ch).1 = ch.1 from rfl, chainFun_smulChain]
    show (c : ℝ) * chainFun ch (ch.1 + 1) i = (c : ℝ) * b i
    rw [h1]

/-- Every chain event of the rectangle is a chain event of the dilated rectangle
for the dilated field. -/
theorem crossApprox_subset_smul {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {a b : Fin 2 → ℝ} (i : Fin 2) (l : ℝ)
    {c : ℚ} (hc : 0 < (c : ℝ)) :
    crossApprox X a b i l
      ⊆ crossApprox (fun w ω => X ((c : ℝ)⁻¹ • w) ω)
          (fun k => (c : ℝ) * a k) (fun k => (c : ℝ) * b k) i l := by
  intro ω hω
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hω
  refine Set.mem_iUnion.mpr ⟨⟨smulChain c ch.1, goodChain_smulChain hc ch.2⟩, ?_⟩
  have hcf : chainFun (smulChain c ch.1) = fun j => (c : ℝ) • chainFun ch.1 j :=
    funext (chainFun_smulChain c ch.1)
  show ω ∈ pathEvent (fun w ω => X ((c : ℝ)⁻¹ • w) ω) l ((smulChain c ch.1).1 + 1)
    (chainFun (smulChain c ch.1))
  rw [show (smulChain c ch.1).1 = ch.1.1 from rfl, hcf,
    pathEvent_smul X (ne_of_gt hc) l (ch.1.1 + 1) (chainFun ch.1)]
  exact hch


/-- The chain events are covariant under a rational dilation: applying the
inclusion in both directions gives equality of the two events, as subsets of the
same probability space. -/
theorem crossApprox_smul {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) {a b : Fin 2 → ℝ} (i : Fin 2) (l : ℝ)
    {c : ℚ} (hc : 0 < (c : ℝ)) :
    crossApprox (fun w ω => X ((c : ℝ)⁻¹ • w) ω)
        (fun k => (c : ℝ) * a k) (fun k => (c : ℝ) * b k) i l
      = crossApprox X a b i l := by
  refine Set.Subset.antisymm ?_ (crossApprox_subset_smul X i l hc)
  have hcne : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hcinv : (0 : ℝ) < ((c⁻¹ : ℚ) : ℝ) := by
    rw [Rat.cast_inv]; exact inv_pos.mpr hc
  have h := crossApprox_subset_smul (fun w ω => X ((c : ℝ)⁻¹ • w) ω)
      (a := fun k => (c : ℝ) * a k) (b := fun k => (c : ℝ) * b k) i l hcinv
  have hfield : (fun (w : Sandpile.Continuum.Space 2) (ω : Ω) =>
      X ((c : ℝ)⁻¹ • (((c⁻¹ : ℚ) : ℝ)⁻¹ • w)) ω) = X := by
    funext w ω
    rw [Rat.cast_inv, inv_inv, inv_smul_smul₀ hcne]
  have hcorner : ∀ r : Fin 2 → ℝ, (fun k => ((c⁻¹ : ℚ) : ℝ) * ((c : ℝ) * r k)) = r := by
    intro r
    funext k
    rw [Rat.cast_inv, inv_mul_cancel_left₀ hcne]
  rw [hfield, hcorner a, hcorner b] at h
  exact h


/-- Scaling the field by a positive constant divides the level. -/
theorem pathEvent_const_smul {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (l : ℝ) (n : ℕ)
    (v : ℕ → Sandpile.Continuum.Space 2) {σ : ℝ} (hσ : 0 < σ) :
    pathEvent (fun u ω => σ * X u ω) l n v = pathEvent X (l / σ) n v := by
  unfold pathEvent
  ext ω
  constructor
  · intro h j q hj hq0 hq1
    have h1 : l ≤ σ * X (segPt (v j) (v (j + 1)) (q : ℝ)) ω := h j q hj hq0 hq1
    rw [div_le_iff₀ hσ, mul_comm]
    exact h1
  · intro h j q hj hq0 hq1
    have h1 : l / σ ≤ X (segPt (v j) (v (j + 1)) (q : ℝ)) ω := h j q hj hq0 hq1
    show l ≤ σ * X (segPt (v j) (v (j + 1)) (q : ℝ)) ω
    rw [div_le_iff₀ hσ, mul_comm] at h1
    exact h1

/-- Scaling the field by a positive constant divides the level in the chain
events, the chains being the same. -/
theorem crossApprox_const_smul {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    crossApprox (fun u ω => σ * X u ω) a b i l = crossApprox X a b i (l / σ) := by
  unfold crossApprox
  exact Set.iUnion_congr fun ch => pathEvent_const_smul X l (ch.1.1 + 1) (chainFun ch.1) hσ


/-- `eq:rescaled-crossing-estimate` (`sandpile.tex:2404-2413`) at the level of
the chain events: for a rational scale `s`, the chain event of the rectangle for
`𝒳_s` at level `l` has the same probability as the chain event of the rectangle
dilated by `1/s` for `𝒳_1` at level `l/b`, where `b` is `s` in dimension two and
`√s` in dimension three.

The three ingredients are the covariance of the chain vocabulary under a
rational dilation, the scaling of the ball field in law
(`Sandpile.Frozen.FixedScaleCrossings.fieldLaw_ballField_smul`), and the fact
that the chain events depend on the field only through its law
(`Sandpile.Support.measure_crossApprox_eq_of_fieldLaw`), which holds because a
chain event, unlike a crossing event, is measurable. -/
theorem measure_crossApprox_ballField_scale
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℚ} (hs : 0 < (s : ℝ))
    (p q : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    P (crossApprox (ballField d W (s : ℝ)) p q i l)
      = P (crossApprox (ballField d W 1) (fun k => (s : ℝ)⁻¹ * p k) (fun k => (s : ℝ)⁻¹ * q k) i
            (l / (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)))) := by
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hσ : (0 : ℝ) < (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) := by
    by_cases h : d = 2
    · rw [if_pos h]; exact hs
    · rw [if_neg h]; exact Real.sqrt_pos.mpr hs
  have hinv : (0 : ℝ) < ((s⁻¹ : ℚ) : ℝ) := by rw [Rat.cast_inv]; exact inv_pos.mpr hs
  have hchain := crossApprox_smul (ballField d W (s : ℝ)) (a := p) (b := q) i l hinv
  have hfield : (fun (w : Sandpile.Continuum.Space 2) (ω : Ω) =>
      ballField d W (s : ℝ) ((((s⁻¹ : ℚ) : ℝ))⁻¹ • w) ω)
      = fun (w : Sandpile.Continuum.Space 2) (ω : Ω) =>
          ballField d W ((s : ℝ) * 1) ((s : ℝ) • w) ω := by
    funext w ω
    rw [Rat.cast_inv, inv_inv, mul_one]
  rw [hfield] at hchain
  have hcorner : ∀ r : Fin 2 → ℝ, (fun k => ((s⁻¹ : ℚ) : ℝ) * r k) = fun k => (s : ℝ)⁻¹ * r k := by
    intro r
    funext k
    rw [Rat.cast_inv]
  rw [hcorner p, hcorner q] at hchain
  rw [← hchain]
  have hmeasX : ∀ w : Sandpile.Continuum.Space 2,
      Measurable (fun ω => ballField d W ((s : ℝ) * 1) ((s : ℝ) • w) ω) :=
    fun w => hW.meas _ (memLp_ballKernel hd (by rw [mul_one]; exact hs) _)
  have hmeasY : ∀ w : Sandpile.Continuum.Space 2,
      Measurable (fun ω => (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * ballField d W 1 w ω) :=
    fun w => (hW.meas _ (memLp_ballKernel hd one_pos _)).const_mul _
  have hlaw := fieldLaw_ballField_smul hGauss hd hW hs (one_pos)
  have hstep := measure_crossApprox_eq_of_fieldLaw P P
    (fun w ω => ballField d W ((s : ℝ) * 1) ((s : ℝ) • w) ω)
    (fun w ω => (if d = 2 then (s : ℝ) else Real.sqrt (s : ℝ)) * ballField d W 1 w ω)
    hmeasX hmeasY hlaw (fun k => (s : ℝ)⁻¹ * p k) (fun k => (s : ℝ)⁻¹ * q k) i l
  rw [hstep, crossApprox_const_smul (ballField d W 1) _ _ i l hσ]

end Sandpile.Support
