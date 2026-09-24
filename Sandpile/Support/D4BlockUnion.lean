/-
The union bound of Step 3 of the dimension-four percolation proof: the good
block of a coarse site fails only if the low set of the field carries one of
the four blocking `∗`-crossings of `sandpile.tex:4051-4057`.
-/
import Sandpile.Support.D4BlockGood

open MeasureTheory

noncomputable section
namespace Sandpile


/-- Union bound for the good-block event: the block of a coarse site fails only
if the low set of the field has one of the four blocking `∗`-crossings. -/
theorem measure_not_blockGood_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (r : ℕ) (Fld : Ω → Site 4 → ℝ) (level : ℝ) (z : Site 2) :
    μ {ω | ¬ BlockGood r (fun u => Fld ω (planeEmbed u)) level z} ≤
      (μ {ω | HasStarTopBottomCrossing 1 (2 * r)
          (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld ω y ≤ level}} +
        μ {ω | HasStarTopBottomCrossing 1 (2 * r)
          (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
          {y | Fld ω (swapPlaneAbout
            (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level}}) +
      (μ {ω | HasStarTopBottomCrossing 2 (2 * r)
          (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) {y | Fld ω y ≤ level}} +
        μ {ω | HasStarTopBottomCrossing 2 (2 * r)
          (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
          {y | Fld ω (swapPlaneAbout
            (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]) y) ≤ level}}) := by
  classical
  set x : Site 4 := planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] with hx
  set A1 := {ω | HasStarTopBottomCrossing 1 (2 * r) x {y | Fld ω y ≤ level}} with hA1
  set A2 := {ω | HasStarTopBottomCrossing 1 (2 * r) x
    {y | Fld ω (swapPlaneAbout x y) ≤ level}} with hA2
  set A3 := {ω | HasStarTopBottomCrossing 2 (2 * r) x {y | Fld ω y ≤ level}} with hA3
  set A4 := {ω | HasStarTopBottomCrossing 2 (2 * r) x
    {y | Fld ω (swapPlaneAbout x y) ≤ level}} with hA4
  have hsub : {ω | ¬ BlockGood r (fun u => Fld ω (planeEmbed u)) level z} ⊆
      (A1 ∪ A2) ∪ (A3 ∪ A4) := by
    intro ω hω
    by_contra hc
    apply hω
    simp only [Set.mem_union, not_or] at hc
    exact blockGood_of_not_star r (Fld ω) level z hc.1.1 hc.1.2 hc.2.1 hc.2.2
  calc μ {ω | ¬ BlockGood r (fun u => Fld ω (planeEmbed u)) level z}
      ≤ μ ((A1 ∪ A2) ∪ (A3 ∪ A4)) := measure_mono hsub
    _ ≤ μ (A1 ∪ A2) + μ (A3 ∪ A4) := measure_union_le _ _
    _ ≤ (μ A1 + μ A2) + (μ A3 + μ A4) :=
        add_le_add (measure_union_le _ _) (measure_union_le _ _)

end Sandpile
