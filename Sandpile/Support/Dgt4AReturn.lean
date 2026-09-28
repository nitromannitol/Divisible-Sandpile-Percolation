import Sandpile.Support.LinEscape

/-!
The return probability of Step 3 of case (a): "Since
`\P_0(\tau_0^+\leq k_n)\to1-G(0,0)^{-1}`" (`sandpile.tex:5212`).

The event `\{\tau_0^+\leq m\}` is the complement of the event that the walk avoids
the origin at the times `1,\dots,m`, whose probability is `retProb d m`, and those
events decrease to the event that the walk never returns, whose probability is
`escProb d`.  The escape probability is `G(0,0)^{-1}` by `escProb_eq`, the one-step
decomposition of `Support/LinEscape.lean`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `\P_0(\tau_0^+\leq m)\to1-G(0,0)^{-1}` (`sandpile.tex:5207`). -/
theorem tendsto_one_sub_retProb [NeZero d] (hd : 3 ≤ d) :
    Tendsto (fun m : ℕ => 1 - retProb d m) atTop (𝓝 (1 - 1 / green d 0 0)) := by
  have h := tendsto_retProb (d := d)
  have h2 : Tendsto (fun m : ℕ => retProb d m) atTop (𝓝 (escProb d)) := by
    simpa using h.add_const (escProb d)
  rw [← escProb_eq hd]
  exact tendsto_const_nhds.sub h2

end Sandpile
