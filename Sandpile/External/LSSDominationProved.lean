import Sandpile.Support.LSSDependence
import Sandpile.Support.LSSPercolation

/-!
# Percolation of dense finite-range dependent fields

The LSS domination theorem and planar Bernoulli percolation imply the
finite-range percolation statement used in the critical-level arguments.
-/

namespace Sandpile.External

/-- Dense stationary finite-range dependent planar fields percolate almost surely. -/
theorem lssDomination : LSSDomination := by
  intro k
  obtain ⟨δ, hδ, h⟩ := Sandpile.percolation_of_lss_kDependent k
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P _ X hX _ hdep hmarg
  exact h Ω P X hX (Sandpile.law_kDependent P X hX k hdep) hmarg

end Sandpile.External
