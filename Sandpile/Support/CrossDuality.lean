import Sandpile.Support.CrossFieldSym
import Sandpile.Support.CrossLaw
import Sandpile.Support.CrossGrid

/-!
# The square crossing estimate from planar duality

The square estimate of `sandpile.tex:2235-2236`:

  "By sign symmetry and rotation invariance, `P(H_{[-R,R]^2}(0)) ≥ 1/2` uniformly in `R ≥ 1`."

The argument is planar duality together with the two symmetries. Duality, the deterministic
statement that for a continuous field either the superlevel set crosses the square left-right or
the sublevel set crosses it bottom-top, is `continuum_square_duality` of
`Sandpile/Support/CrossGrid.lean`, proved there by discretization onto a grid fine enough for the
field's modulus of continuity; it holds between the levels `-η` and `η` for every `η > 0`. The
rest is here (`square_half_crossApprox`, `square_half_crossing`, `square_half_translate`).

The sublevel bottom-top crossing is the superlevel left-right crossing of the field read through
the coordinate interchange and the sign flip, which is the field `Z = -X ∘ transpose`; the two
events are equal as subsets of the probability space. `Z` has the same law as `X`, since the
interchange composed with the sign flip is one of the symmetries of `IsSymmetricField`. Equality
in law does not compare the outer measures of the two crossing events, which are not known to be
measurable; what it does compare is the chain events of `Sandpile/Support/CrossLaw.lean`, and
those bracket the crossing probability from both sides at levels a distance `ε` apart. Running
the bracket through the union bound gives the estimate at the level `-ε`, for every `ε > 0`, and
on both sides for the CHAIN EVENT, which is measurable:

  `1 ≤ P*(X crosses at 0) + P*(-X ∘ transpose crosses at 0)`
    `≤ P(chain event of X at -ε) + P(chain event of -X ∘ transpose at -ε)`
    `= 2 P(chain event of X at -ε)`      (equal laws)

so `P(chain event of X at -ε) ≥ 1/2`, and the crossing form follows because the chain event is
contained in the crossing.

The loss of `ε` is an artefact of this route and not of the paper: it is the price of comparing
two crossing events of equal law through countably many values, together with the price of
sampling the field on a grid. It cannot be removed by letting `ε → 0` in the chain events alone:
they decrease, as `ε` does, to the set where SOME admissible chain works at every level `-ε`, and
the chain may change with `ε`, so that set is strictly larger than the chain event at the level
`0`. What closes the gap is the compactness of the crossings themselves: a Hausdorff limit of
compact connected crossings of `{X ≥ -1/n}` is a compact connected crossing of `{X ≥ 0}`. That
argument is not written here, and nothing downstream needs it: the level enters the fixed-scale
crossing estimate only through the level loss of Step 3, which compares two levels. For the same
reason the `η` of the duality costs nothing: it is absorbed into the `ε`, half of the budget
going to the grid and half to the chains.

`crossApprox_mono_field` and `crossingSet_swap` are the elementary facts about crossing events,
monotonicity in the field and the coordinate-swap symmetry, that the argument above uses.
-/

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The square estimate for the CHAIN EVENT, which is measurable: one half for
the chain event of the square at every level below zero, from planar duality and
the symmetry of the field.  Half of the level budget `ε` pays for the grid of
the duality and half for the chains. -/
theorem square_half_crossApprox
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    (1 : ℝ) / 2 ≤ P.real (crossApprox X ![0, 0] ![s, s] 0 (-ε)) := by
  classical
  set η : ℝ := ε / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hlt : -ε < -η := by rw [hηdef]; linarith
  set Z : Sandpile.Continuum.Space 2 → Ω → ℝ :=
    fun u ω => (-1 : ℝ) * X ((Sandpile.Continuum.PlaneSymmetry.transpose).toFun u) ω with hZ
  set E : Set Ω := crossApprox X ![0, 0] ![s, s] 0 (-ε) with hE
  have hmeasZ : ∀ u, Measurable (Z u) := fun u => (hmeas _).const_mul _
  have hcontZ : ∀ᵐ ω ∂P, Continuous fun u => Z u ω := by
    filter_upwards [hcont] with ω hω
    exact continuous_const.mul (hω.comp (continuous_planeSymmetry _))
  have hnull : P {ω | Continuous fun u => X u ω}ᶜ = 0 := by
    rw [← MeasureTheory.ae_iff.mp hcont]
    rfl
  have hcover : {ω | Continuous fun u => X u ω} ⊆
      {ω | Crosses ![0, 0] ![s, s] 0 {u | -η ≤ X u ω}} ∪
        {ω | Crosses ![0, 0] ![s, s] 1 {u | X u ω ≤ η}} := by
    intro ω hω
    rcases continuum_square_duality s η hs hη (fun u => X u ω) hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hone : (1 : ℝ≥0∞) ≤ P {ω | Crosses ![0, 0] ![s, s] 0 {u | -η ≤ X u ω}}
      + P {ω | Crosses ![0, 0] ![s, s] 1 {u | X u ω ≤ η}} := by
    have h := measure_le_inter_add_compl P Set.univ {ω | Continuous fun u => X u ω}
    rw [Set.univ_inter, hnull, add_zero, measure_univ] at h
    exact le_trans h (le_trans (measure_mono hcover) (measure_union_le _ _))
  have hs0 : (![(0 : ℝ), 0]) 0 < (![s, s]) 0 := by simpa using hs
  have hs1 : (![(0 : ℝ), 0]) 1 < (![s, s]) 1 := by simpa using hs
  have hAE : P {ω | Crosses ![0, 0] ![s, s] 0 {u | -η ≤ X u ω}} ≤ P E :=
    measure_crossing_le_of_lt (i := 0) P hs0 hs1 hlt hcont
  have hBB : {ω | Crosses ![0, 0] ![s, s] 1 {u | X u ω ≤ η}} ⊆
      {ω | Crosses ![0, 0] ![s, s] 0 {u | -η ≤ Z u ω}} := by
    intro ω hω
    have h : Crosses ![0, 0] ![s, s] 1 {u | X u ω ≤ η} := hω
    have hset : {u : Sandpile.Continuum.Space 2 | X u ω ≤ η}
        = swapPoint ⁻¹' {u | -η ≤ Z u ω} := by
      ext u
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hZ]
      rw [transpose_toFun_eq_swapPoint, swapPoint_swapPoint]
      constructor <;> intro h' <;> linarith
    rw [hset] at h
    have hsw := crosses_swap h
    have hA0 : (fun k => (![(0 : ℝ), 0]) (swapIdx k)) = ![0, 0] := by
      funext k; fin_cases k <;> rfl
    have hB0 : (fun k => (![s, s]) (swapIdx k)) = ![s, s] := by
      funext k; fin_cases k <;> rfl
    rw [hA0, hB0, swapIdx_one] at hsw
    exact hsw
  have hBcross : P {ω | Crosses ![0, 0] ![s, s] 0 {u | -η ≤ Z u ω}}
      ≤ P (crossApprox Z ![0, 0] ![s, s] 0 (-ε)) :=
    measure_crossing_le_of_lt (i := 0) P hs0 hs1 hlt hcontZ
  have hlawZ : Sandpile.Continuum.fieldLaw P Z = Sandpile.Continuum.fieldLaw P X :=
    hsym Sandpile.Continuum.PlaneSymmetry.transpose (-1) (Or.inr rfl)
  have hZX : P (crossApprox Z ![0, 0] ![s, s] 0 (-ε))
      = P (crossApprox X ![0, 0] ![s, s] 0 (-ε)) :=
    measure_crossApprox_eq_of_fieldLaw P P Z X hmeasZ hmeas hlawZ _ _ _ _
  have hBE : P {ω | Crosses ![0, 0] ![s, s] 1 {u | X u ω ≤ η}} ≤ P E := by
    refine le_trans (measure_mono hBB) ?_
    rw [hE, ← hZX]
    exact hBcross
  have hEsum : (1 : ℝ≥0∞) ≤ P E + P E := le_trans hone (add_le_add hAE hBE)
  have hfin : P E ≠ ⊤ := measure_ne_top P E
  have hsum_ne : P E + P E ≠ ⊤ := by
    simp [hfin]
  have h := ENNReal.toReal_mono hsum_ne hEsum
  rw [ENNReal.toReal_add hfin hfin, ENNReal.toReal_one] at h
  have hreal : P.real E = (P E).toReal := rfl
  rw [hreal]
  linarith

/-- The square estimate for the crossing itself, at every level below zero: the
chain event is contained in the crossing, up to the null set where the sample
path is not continuous. -/
theorem square_half_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    (1 : ℝ) / 2 ≤ P.real {ω | Crosses ![0, 0] ![s, s] 0 {u | -ε ≤ X u ω}} := by
  refine le_trans (square_half_crossApprox P X hmeas hcont hsym s ε hs hε) ?_
  exact ENNReal.toReal_mono (measure_ne_top P _)
    (measure_crossApprox_le_crossing (i := 0) (a := ![0, 0]) (b := ![s, s]) P hcont)

/-- The square estimate in the translated form the fixed-scale crossing estimate
asks for: for every square of side at least two and every translation of the
field, at every level below zero. -/
theorem square_half_translate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => X u ω)
    (hsym : Sandpile.Continuum.IsSymmetricField P X)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ (v : Sandpile.Continuum.Space 2) (s : ℝ), 1 ≤ s →
      (1 : ℝ) / 2 ≤ P.real {ω |
        Crosses ![0, 0] ![2 * s, 2 * s] 0 {u | -ε ≤ X (u + v) ω}} := by
  intro v s hs
  have hcontY : ∀ᵐ ω ∂P, Continuous fun u => X (u + v) ω := by
    filter_upwards [hcont] with ω hω
    exact hω.comp (continuous_id.add continuous_const)
  exact square_half_crossing P (fun u ω => X (u + v) ω) (fun u => hmeas _) hcontY
    (Sandpile.Continuum.isSymmetricField_translate hsym v) (2 * s) ε (by linarith) hε

/-- The chain event is increasing in the field: raising the field everywhere
keeps a chain.  This is the sense in which the crossing estimates are increasing
events of the field, and it is the form the association of the
finite-dimensional distributions is applied in. -/
theorem crossApprox_mono_field {Ω : Type*} [MeasurableSpace Ω]
    (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ)
    {ω ω' : Ω} (h : ∀ u, X u ω ≤ X u ω') (hω : ω ∈ crossApprox X a b i l) :
    ω' ∈ crossApprox X a b i l := by
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hω
  refine Set.mem_iUnion.mpr ⟨ch, ?_⟩
  intro j q hj hq0 hq1
  exact le_trans (hch j q hj hq0 hq1) (h _)

/-- The crossing of a rectangle by the field read through the coordinate
interchange is the crossing of the transposed rectangle, in the interchanged
direction, by the field itself: an equality of subsets of the probability space,
so it holds for the outer measure.  This is the field form of the coordinate
symmetry of `sandpile.tex:2103`. -/
theorem crossingSet_swap {Ω : Type*} (X : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    {ω | Crosses a b i {u | l ≤ X (swapPoint u) ω}}
      = {ω | Crosses (fun k => a (swapIdx k)) (fun k => b (swapIdx k)) (swapIdx i)
          {u | l ≤ X u ω}} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hX
    exact crosses_swap hX
  · intro hX
    have hback := crosses_swap (a := fun k => a (swapIdx k)) (b := fun k => b (swapIdx k))
      (i := swapIdx i) (S := swapPoint ⁻¹' {u | l ≤ X u ω})
      (by
        have hset : swapPoint ⁻¹' (swapPoint ⁻¹' {u | l ≤ X u ω}) = {u | l ≤ X u ω} := by
          ext u
          simp only [Set.mem_preimage, swapPoint_swapPoint]
        rw [hset]
        exact hX)
    have hA : (fun k => a (swapIdx (swapIdx k))) = a := by
      funext k; rw [swapIdx_swapIdx]
    have hB : (fun k => b (swapIdx (swapIdx k))) = b := by
      funext k; rw [swapIdx_swapIdx]
    rw [hA, hB, swapIdx_swapIdx] at hback
    exact hback

end Sandpile.Support
