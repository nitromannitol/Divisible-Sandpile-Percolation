import Sandpile.Frozen.MeanLocalization
import Sandpile.Support.D23PlaneSite

/-!
# Localization boxes for the two- and three-dimensional percolation argument

This file introduces the sup-norm localization box `d23Box R x`, the discrete integer-radius
form of `Q(x, R)` from `eq:localized-odometer` (`sandpile.tex:2600-2604`), and records its
behaviour under translation (`d23Box_translate`). It also proves the two comparisons the block
scheme needs: a box about a site near a given centre sits inside a larger box about that centre
(`d23Box_subset`), and the boxes of two centres separated by more than twice the radius in some
coordinate are disjoint (`d23Box_disjoint`).
-/

noncomputable section
namespace Sandpile

variable {d : ℕ}

/-- The localization box `Q(x,R)` of `eq:localized-odometer` at an integer
radius. -/
def d23Box (R : ℕ) (x : Site d) : Set (Site d) := supBox x (R : ℝ)

/-- `y` belongs to `d23Box R x` exactly when every coordinate of `y - x` has absolute value at
most `R`. -/
lemma mem_d23Box (R : ℕ) (x y : Site d) :
    y ∈ d23Box R x ↔ ∀ i, |y i - x i| ≤ (R : ℤ) := by
  simp [d23Box, supBox]

/-- The centre `x` always belongs to its own box `d23Box R x`. -/
lemma self_mem_d23Box (R : ℕ) (x : Site d) : x ∈ d23Box R x := by
  rw [mem_d23Box]
  intro i
  simp

/-- The box about `x + y` seen from `y` is the box about `x`. -/
lemma d23Box_translate (R : ℕ) (x y : Site d) :
    {w : Site d | w + y ∈ d23Box R (x + y)} = d23Box R x := by
  ext w
  simp only [Set.mem_setOf_eq, mem_d23Box, Pi.add_apply]
  constructor
  · intro h i
    have hi := h i
    have heq : w i + y i - (x i + y i) = w i - x i := by ring
    rw [heq] at hi
    exact hi
  · intro h i
    have hi := h i
    have heq : w i + y i - (x i + y i) = w i - x i := by ring
    rw [heq]
    exact hi

/-- A box sits inside a larger box about a nearby centre. -/
lemma d23Box_subset {R M : ℕ} {x y : Site d} (h : ∀ i, |x i - y i| + (R : ℤ) ≤ (M : ℤ)) :
    d23Box R x ⊆ d23Box M y := by
  intro w hw
  rw [mem_d23Box] at hw ⊢
  intro i
  have h1 := hw i
  have h2 := h i
  have h3 : |w i - y i| ≤ |w i - x i| + |x i - y i| := abs_sub_le _ _ _
  linarith

/-- Two boxes with a large coordinate gap between their centres are disjoint. -/
lemma d23Box_disjoint {R : ℕ} {x y : Site d} (h : ∃ i, 2 * (R : ℤ) < |x i - y i|) :
    Disjoint (d23Box R x) (d23Box R y) := by
  obtain ⟨i, hi⟩ := h
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_d23Box] at hw hw'
  have h1 := hw i
  have h2 := hw' i
  have h3 : |x i - y i| ≤ |x i - w i| + |w i - y i| := abs_sub_le _ _ _
  rw [abs_sub_comm (x i) (w i)] at h3
  linarith

end Sandpile
