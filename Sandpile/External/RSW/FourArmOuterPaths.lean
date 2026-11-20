import Sandpile.External.RSW.TranslatedArmWalk
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# The outer paths of the four-arm event

The larger translated arms lie inside the vertical construction rectangle and connect
its top and bottom to the two central boundary lines.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The intermediate arm dimensions fit in the vertical construction rectangle. -/
theorem kstBaseScale_outer_arm_arithmetic (j : ℕ) :
    5 * kstBaseScale j / 2 + (5 * kstBaseScale j / 2) / 64 ≤
      3 * kstBaseScale j - 3 * (kstBaseScale j / 12) ∧
    5 * kstBaseScale j / 2 = 3 * kstBaseScale j / 2 + kstBaseScale j ∧
    3 * kstBaseScale j / 2 + 5 * kstBaseScale j / 2 = 4 * kstBaseScale j ∧
    (5 * kstBaseScale j / 2) / 64 ≤ 3 * (kstBaseScale j / 64) := by
  have hs := (kstBaseScale_intermediate j).1
  have ht := (kstBaseScale_intermediate j).2.1
  have ha := (kstBaseScale_intermediate_offsets j).1
  have hβ := (kstBaseScale_offsets j).2
  have hα := (kstBaseScale_offsets j).1
  dsimp only [kstBaseScale] at hs ht ha hβ hα ⊢
  constructor <;> [skip; constructor <;> [skip; constructor]] <;> omega

/-- The four-arm event contains open paths from the top and bottom of the vertical
rectangle to its two central lines, with endpoints in the central target interval. -/
theorem kstFourArmEvent_outer_paths (j : ℕ) {ω : Sym2 (Site 2) → Bool}
    (hω : ω ∈ kstFourArmEvent (kstBaseScale j)) :
    let m := kstBaseScale j
    let W := 3 * m - 3 * (m / 12)
    let Q := centeredPlaneRectangle W (4 * m)
    ∃ (a b c d : Q) (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d),
      p.IsPath ∧ IsBondOpenWalk ω p ∧ q.IsPath ∧ IsBondOpenWalk ω q ∧
      (a : Site 2) 1 = 4 * (m : ℤ) ∧ (b : Site 2) 1 = -(m : ℤ) ∧
      (c : Site 2) 1 = m ∧ (d : Site 2) 1 = -(4 * (m : ℤ)) ∧
      -((3 * (m / 64) : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧
      (a : Site 2) 0 ≤ ((3 * (m / 64) : ℕ) : ℤ) ∧
      -((3 * (m / 64) : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧
      (b : Site 2) 0 ≤ ((3 * (m / 64) : ℕ) : ℤ) ∧
      -((3 * (m / 64) : ℕ) : ℤ) ≤ (c : Site 2) 0 ∧
      (c : Site 2) 0 ≤ ((3 * (m / 64) : ℕ) : ℤ) ∧
      -((3 * (m / 64) : ℕ) : ℤ) ≤ (d : Site 2) 0 ∧
      (d : Site 2) 0 ≤ ((3 * (m / 64) : ℕ) : ℤ) ∧
      (∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1) ∧
      (∀ z ∈ q.support, (z : Site 2) 1 ≤ m) := by
  let m := kstBaseScale j
  let s := 5 * m / 2
  let t := 3 * m / 2
  let W := 3 * m - 3 * (m / 12)
  have ⟨hw, hdiff, hsum, hwidth⟩ := kstBaseScale_outer_arm_arithmetic j
  have hdiff' : (s : ℤ) = (t : ℤ) + m := by exact_mod_cast hdiff
  have hsum' : (t : ℤ) + s = 4 * (m : ℤ) := by exact_mod_cast hsum
  have hwidth' : ((s / 64 : ℕ) : ℤ) ≤ ((3 * (m / 64) : ℕ) : ℤ) := by exact_mod_cast hwidth
  obtain ⟨_, _, htop, hbottom⟩ := hω
  obtain ⟨a, b, p, hpath₁, hopen₁, hay, hby, haL, haR, hbL, hbR, hpBounds⟩ :=
    translated_kstArmEvent_exists_walk s W (4 * m) t hw (by push_cast; omega)
      (by push_cast; omega) htop
  obtain ⟨c, d, q, hpath₂, hopen₂, hcy, hdy, hcL, hcR, hdL, hdR, hqBounds⟩ :=
    translated_kstArmEvent_exists_walk s W (4 * m) (-t) hw (by push_cast; omega)
      (by push_cast; omega) hbottom
  refine ⟨a, b, c, d, p, q, hpath₁, hopen₁, hpath₂, hopen₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try omega
  · intro z hz
    have hh := hpBounds z hz
    omega
  · intro z hz
    have hh := hqBounds z hz
    omega

end Sandpile.External.RSW
