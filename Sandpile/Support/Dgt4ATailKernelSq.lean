import Sandpile.External.GreenBoundsHigh

/-!
# Square summability of the tail kernel

The square summability of the tail kernel, `eq:dgt4-tail-kernel` of `sandpile.tex:1303-1306`, read
off the Green-bounds input.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `\sum_y (\sum_{r\geq m}p_r(0,y))^2<\infty` (`sandpile.tex:1303-1306`). -/
theorem summable_tailKernel_sq (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {m : ℕ} (hm : 1 ≤ m) : Summable fun y : Site d => Sandpile.External.tailKernel d m y ^ 2 := by
  obtain ⟨C, hC, htail⟩ := (hGH d hd).2.2.1
  exact (htail m hm).2.1

end Sandpile
