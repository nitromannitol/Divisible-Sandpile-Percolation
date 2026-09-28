import Sandpile.Support.CrossUnion

/-!
# Coordinate barriers block crossings

A coordinate barrier on which the value is below the proposed crossing level
prevents a continuum crossing, by the intermediate value property of a
connected set. This applies even when the value has no continuity assumption.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal RealInnerProductSpace

/-- If every point of the rectangle `rectSet a b` on the coordinate hyperplane
`{u | u i = v}` has value `U u ≤ H`, then no connected crossing curve `Γ` of
the rectangle in coordinate `i` can lie entirely in `{u | H < U u}`: a
crossing curve must meet that hyperplane (by connectedness / the intermediate
value property), where its value is bounded by `H`, contradicting the strict
crossing condition. -/
theorem Sandpile.Support.not_crosses_of_coordinate_barrier
    {a b : Fin 2 → ℝ} {i : Fin 2} {v H : ℝ} {U : Space 2 → ℝ}
    (hv : a i ≤ v ∧ v ≤ b i)
    (hbarrier : ∀ u ∈ rectSet a b, u i = v → U u ≤ H) :
    ¬ Crosses a b i {u | H < U u} := by
  rintro ⟨Γ, hΓ, _, hΓc, ⟨x, hx, hxi⟩, ⟨y, hy, hyi⟩⟩
  have hcoord : Continuous (fun u : Space 2 => u i) := by fun_prop
  have hIv := hΓc.isPreconnected.intermediate_value hx hy hcoord.continuousOn
  have hv' : v ∈ Set.Icc (x i) (y i) := by simpa only [hxi, hyi, Set.mem_Icc] using hv
  obtain ⟨u, hu, hui⟩ := hIv hv'
  exact (not_lt_of_ge (hbarrier u (hΓ hu).2 hui)) (hΓ hu).1
