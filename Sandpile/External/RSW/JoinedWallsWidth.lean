import Sandpile.External.RSW.JoinedWallsQuasiCrossing

/-!
# Joined walls with a transported rectangle width

The joined-wall construction can be applied with an equal rectangle width.
-/

namespace Sandpile.External.RSW

/-- Joined vertical walls and two spanning side walks yield a quasi-crossing. -/
theorem kstQuasiCrossing_of_joined_vertical_walls_width (n m M W : ℕ)
    (hM : 0 < M) (hW : W = n + 3 * (n / 12))
    {ω : Sym2 (Site 2) → Bool}
    {a b x top c d y bottom left leftEnd right rightEnd :
      centeredPlaneRectangle W n}
    (upper : (rectangleGraph (centeredPlaneRectangle W n)).Walk a b)
    (upperLink : (rectangleGraph (centeredPlaneRectangle W n)).Walk x top)
    (lower : (rectangleGraph (centeredPlaneRectangle W n)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle W n)).Walk y bottom)
    (leftWalk : (rectangleGraph (centeredPlaneRectangle W n)).Walk left leftEnd)
    (rightWalk : (rectangleGraph (centeredPlaneRectangle W n)).Walk right rightEnd)
    (hp : IsKSTPath m upper) (hq : IsKSTPath m lower)
    (hx : x ∈ upper.support) (hy : y ∈ lower.support)
    (hpOpen : IsBondOpenWalk ω upper) (huOpen : IsBondOpenWalk ω upperLink)
    (hqOpen : IsBondOpenWalk ω lower) (hvOpen : IsBondOpenWalk ω lowerLink)
    (hlOpen : IsBondOpenWalk ω leftWalk) (hrOpen : IsBondOpenWalk ω rightWalk)
    (hleft : (left : Site 2) 0 = -((n + 3 * (n / 12) : ℕ) : ℤ))
    (hright : (right : Site 2) 0 = ((n + 3 * (n / 12) : ℕ) : ℤ))
    (hleftStart : (left : Site 2) 0 ≤ -(M : ℤ))
    (hleftEnd : (M : ℤ) ≤ (leftEnd : Site 2) 0)
    (hrightStart : (M : ℤ) ≤ (right : Site 2) 0)
    (hrightEnd : (rightEnd : Site 2) 0 ≤ -(M : ℤ))
    (htop : (top : Site 2) 1 = n) (hbottom : (bottom : Site 2) 1 = -(n : ℤ))
    (hupper : ∀ z, (z ∈ upper.support ∨ z ∈ upperLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M n)
    (hlower : ∀ z, (z ∈ lower.support ∨ z ∈ lowerLink.support) →
      (z : Site 2) ∈ centeredPlaneRectangle M n)
    (hjoin : ∃ z, (z ∈ upper.support ∨ z ∈ upperLink.support) ∧
      (z ∈ lower.support ∨ z ∈ lowerLink.support)) :
    ω ∈ kstQuasiCrossingEvent n m := by
  subst W
  exact kstQuasiCrossing_of_joined_vertical_walls n m M hM upper upperLink lower
    lowerLink leftWalk rightWalk hp hq hx hy hpOpen huOpen hqOpen hvOpen hlOpen hrOpen
    hleft hright hleftStart hleftEnd hrightStart hrightEnd htop hbottom hupper hlower hjoin

end Sandpile.External.RSW
