import Sandpile.Support.Dgt4ATailLip
import Sandpile.External.GreenBoundsHigh

/-!
The `j`-step tail of the heat kernel in the two forms the paper uses: the sum
`\sum_{r\geq j}p_r(0,z)` of `sandpile.tex:5063-5066` and the subtype sum
`Sandpile.External.tailKernel d j z` of `eq:dgt4-tail-kernel`
(`sandpile.tex:1305-1310`).
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `∑_{r≥j}p_r(0,z) = Sandpile.External.tailKernel d j z`. -/
theorem tsum_heatKernel_add_eq_tailKernel (j : ℕ) (z : Site d) :
    (∑' r : ℕ, heatKernel d (j + r) 0 z) = Sandpile.External.tailKernel d j z := by
  unfold Sandpile.External.tailKernel
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x : {x : {n : ℕ // j ≤ n} // heatKernel d (x.1 : ℕ) 0 z ≠ 0} => (x.1 : ℕ) - j)
    ?_ ?_ ?_
  · intro a b hab
    have ha : j ≤ (a.1 : ℕ) := a.1.2
    have hb : j ≤ (b.1 : ℕ) := b.1.2
    have : (a.1 : ℕ) = (b.1 : ℕ) := by
      have := hab
      simp only at this
      omega
    exact Subtype.ext (Subtype.ext this)
  · intro r hr
    refine ⟨⟨⟨j + r, Nat.le_add_right j r⟩, ?_⟩, ?_⟩
    · simpa using hr
    · simp
  · intro x
    have hx : j ≤ (x.1 : ℕ) := x.1.2
    congr 1
    omega
