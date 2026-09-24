/-
Step 3 of the dimension-four percolation proof in probability
(`sandpile.tex:4048-4065`): intersecting the crossing event of the ball field
with the future-height event of Step 1 and the time-truncation event of Step 2
on the sites of one block gives the good-block event of the block field
`𝓑_{2r,N} + Y_{2r}` at level `b₀ log(2r)/2`.
-/
import Sandpile.Support.D4CritBlock
import Sandpile.Support.D4CritTimeTail
import Sandpile.Support.D4PlaneEmbed

open MeasureTheory

noncomputable section
namespace Sandpile

/-- The good block of the block field fails only if the good block of the ball
field fails, or the future height is low somewhere in the block, or the
time truncation is large somewhere in the block. -/
theorem measure_not_blockGood_block_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Aex : ℕ) (Aloc b₀ : ℝ) (r : ℕ) (z : Site 2) (δ₁ δ₂ δ₃ : ENNReal)
    (h1 : LatticeProb.iidLaw 4 ν
      {ζ : Site 4 → ℝ | ¬ BlockGood r (fun u => ballGreenField (2 * r) ζ (planeEmbed u))
        (-(b₀ / 4 * Real.log ((2 * r : ℕ) : ℝ))) z} ≤ δ₁)
    (h2 : ∀ x : Site 4, LatticeProb.iidLaw 4 ν
      {ζ : Site 4 → ℝ | frExitValue Aex Aloc (2 * r) ζ x
        < b₀ * Real.log ((2 * r : ℕ) : ℝ)} ≤ δ₂)
    (h3 : ∀ x : Site 4, LatticeProb.iidLaw 4 ν
      {ζ : Site 4 → ℝ | b₀ * Real.log ((2 * r : ℕ) : ℝ) / 4 <
        |ballGreenField (2 * r) ζ x
          - frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ x|} ≤ δ₃) :
    LatticeProb.iidLaw 4 ν
        {ζ : Site 4 → ℝ | ¬ BlockGood r
          (fun u => frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ (planeEmbed u)
            + frExitValue Aex Aloc (2 * r) ζ (planeEmbed u))
          (b₀ * Real.log ((2 * r : ℕ) : ℝ) / 2) z}
      ≤ δ₁ + ((planeRectangle (4 * r) (4 * r)).card * δ₂
          + (planeRectangle (4 * r) (4 * r)).card * δ₃) := by
  classical
  set P := LatticeProb.iidLaw 4 ν with hP
  set L : ℝ := Real.log ((2 * r : ℕ) : ℝ) with hL
  set K : Finset (Site 2) := planeRectangle (4 * r) (4 * r) with hK
  set A1 : Set (Site 4 → ℝ) :=
    {ζ | ¬ BlockGood r (fun u => ballGreenField (2 * r) ζ (planeEmbed u)) (-(b₀ / 4 * L)) z}
    with hA1
  set S2 : Site 2 → Set (Site 4 → ℝ) := fun v =>
    {ζ | frExitValue Aex Aloc (2 * r) ζ (planeEmbed (blockShift r z v)) < b₀ * L} with hS2
  set S3 : Site 2 → Set (Site 4 → ℝ) := fun v =>
    {ζ | b₀ * L / 4 < |ballGreenField (2 * r) ζ (planeEmbed (blockShift r z v))
      - frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ (planeEmbed (blockShift r z v))|} with hS3
  have hsub : {ζ : Site 4 → ℝ | ¬ BlockGood r
        (fun u => frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ (planeEmbed u)
          + frExitValue Aex Aloc (2 * r) ζ (planeEmbed u)) (b₀ * L / 2) z}
      ⊆ A1 ∪ ((⋃ v ∈ K, S2 v) ∪ (⋃ v ∈ K, S3 v)) := by
    intro ζ hζ
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨hc1, hc2, hc3⟩ := hc
    have hc2' : ∀ v ∈ K, ζ ∉ S2 v := fun v hv hmem => hc2 (Set.mem_biUnion hv hmem)
    have hc3' : ∀ v ∈ K, ζ ∉ S3 v := fun v hv hmem => hc3 (Set.mem_biUnion hv hmem)
    apply hζ
    refine blockGood_block_of_ball_on r
      (fun u => ballGreenField (2 * r) ζ (planeEmbed u))
      (fun u => frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ (planeEmbed u))
      (fun u => frExitValue Aex Aloc (2 * r) ζ (planeEmbed u)) b₀ z ?_ ?_ ?_
    · intro v hv
      exact not_lt.mp (hc2' v hv)
    · intro v hv
      exact not_lt.mp (hc3' v hv)
    · simpa only [hA1, Set.mem_setOf_eq, not_not] using hc1
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine add_le_add h1 ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · exact measure_biUnion_card_le P K S2 δ₂ (fun v _ => h2 _)
  · exact measure_biUnion_card_le P K S3 δ₃ (fun v _ => h3 _)

end Sandpile
