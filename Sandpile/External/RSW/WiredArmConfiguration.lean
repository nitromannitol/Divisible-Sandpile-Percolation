import Sandpile.External.RSW.WiredArm

/-!
# Wired boundary configurations for arms

The added boundary rows are wired through their respective arm targets, while
bonds with both endpoints in the original strip retain their states.
-/

namespace Sandpile.External.RSW

/-- The boundary constraints on a bond of the enlarged arm rectangle. -/
def wiredArmAllowed (m : ℕ) (e : Sym2 (Site 2)) : Prop :=
  (∀ x ∈ e, x 1 = (m : ℤ) + 1 → ∀ y ∈ e, y 1 ≠ (m : ℤ) + 1 →
    y 1 = m ∧ -((m / 64 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ m / 64) ∧
  (∀ y ∈ e, y 1 = -((m : ℤ) + 1) → ∀ x ∈ e, x 1 ≠ -((m : ℤ) + 1) →
    x 1 = -(m : ℤ) ∧ -((m / 64 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ m / 64)

/-- Preserve the original bonds in the arm strip and wire the added rows to the targets. -/
noncomputable def wiredArmConfig (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (e : Sym2 (Site 2)) : Bool := by
  classical
  exact if ∀ z ∈ e, -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m then ω e
    else decide (wiredArmAllowed m e)

/-- Interior bonds retain their original states after wiring. -/
theorem wiredArmConfig_eq_of_interior (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (e : Sym2 (Site 2)) (he : ∀ z ∈ e, -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) :
    wiredArmConfig m ω e = ω e := by
  classical
  simp only [wiredArmConfig, ite_eq_left he]

/-- An open bond leaving the upper wired row enters the upper arm target. -/
theorem wiredArmConfig_upper_entrance (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (m : ℤ) + 1) (hy : y 1 ≠ (m : ℤ) + 1)
    (he : wiredArmConfig m ω s(x, y) = true) :
    y 1 = m ∧ -((m / 64 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ m / 64 := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  have ha : wiredArmAllowed m s(x, y) := by
    simpa only [wiredArmConfig, ite_eq_right hn, decide_eq_true_eq] using he
  exact ha.1 x (by simp only [Sym2.mem_iff, true_or]) hx y
    (by simp only [Sym2.mem_iff, or_true]) hy

/-- An open bond leaving the lower wired row enters the lower arm target. -/
theorem wiredArmConfig_lower_entrance (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hy : y 1 = -((m : ℤ) + 1)) (hx : x 1 ≠ -((m : ℤ) + 1))
    (he : wiredArmConfig m ω s(x, y) = true) :
    x 1 = -(m : ℤ) ∧ -((m / 64 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ m / 64 := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h y (by simp only [Sym2.mem_iff, or_true])
    omega
  have ha : wiredArmAllowed m s(x, y) := by
    simpa only [wiredArmConfig, ite_eq_right hn, decide_eq_true_eq] using he
  exact ha.2 y (by simp only [Sym2.mem_iff, or_true]) hy x
    (by simp only [Sym2.mem_iff, true_or]) hx

/-- Every bond along the upper added row is open. -/
theorem wiredArmConfig_upper_row (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (m : ℤ) + 1) (hy : y 1 = (m : ℤ) + 1) :
    wiredArmConfig m ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredArmConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredArmAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- Every bond along the lower added row is open. -/
theorem wiredArmConfig_lower_row (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = -((m : ℤ) + 1)) (hy : y 1 = -((m : ℤ) + 1)) :
    wiredArmConfig m ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredArmConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredArmAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- A bond from the upper added row to the upper target is open. -/
theorem wiredArmConfig_upper_connector (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (m : ℤ) + 1) (hy : y 1 = m)
    (hl : -((m / 64 : ℕ) : ℤ) ≤ y 0) (hr : y 0 ≤ m / 64) :
    wiredArmConfig m ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredArmConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredArmAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- A bond from the lower target to the lower added row is open. -/
theorem wiredArmConfig_lower_connector (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hy : y 1 = -((m : ℤ) + 1)) (hx : x 1 = -(m : ℤ))
    (hl : -((m / 64 : ℕ) : ℤ) ≤ x 0) (hr : x 0 ≤ m / 64) :
    wiredArmConfig m ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m) := by
    intro h
    have h' := h y (by simp only [Sym2.mem_iff, or_true])
    omega
  rw [wiredArmConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredArmAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- A crossing of the wired rectangle yields the original arm. -/
theorem kstArmEvent_of_canonical_wired_crossing (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool)
    (hcross : ∃ (a b : centeredPlaneRectangle (m + m / 64) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64) (m + 1))).Walk a b),
      (a : Site 2) 1 = (m : ℤ) + 1 ∧ (b : Site 2) 1 = -((m : ℤ) + 1) ∧
      IsBondOpenWalk (wiredArmConfig m ω) p) : ω ∈ kstArmEvent m := by
  apply kstArmEvent_of_wired_crossing m hm ω (wiredArmConfig m ω) ?_ ?_ ?_ hcross
  · intro x y hx hy _ he
    exact (wiredArmConfig_upper_entrance m ω x y hx hy he).2
  · intro x y hy hx _ he
    exact (wiredArmConfig_lower_entrance m ω x y hy hx he).2
  · intro e he hopen
    have hi : ∀ z ∈ Sym2.map Subtype.val e, -(m : ℤ) ≤ z 1 ∧ z 1 ≤ m := by
      intro z hz
      induction e using Sym2.ind with
      | _ x y =>
        simp only [Sym2.map_mk, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · have h := (mem_centeredPlaneRectangle _ _ _).mp (he x (by simp))
          exact h.2.2
        · have h := (mem_centeredPlaneRectangle _ _ _).mp (he y (by simp))
          exact h.2.2
    rwa [wiredArmConfig_eq_of_interior m ω _ hi] at hopen

end Sandpile.External.RSW
