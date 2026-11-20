import Sandpile.External.RSW.WiredKSTPath

/-!
# Wired bond configurations for scale paths

The boundary rows are connected to the central KST targets, while all bonds
inside the scale rectangle keep their original states.
-/

namespace Sandpile.External.RSW

/-- The permitted bonds joining the added rows to the scale rectangle. -/
def wiredKSTAllowed (k : ℕ) (edge : Sym2 (Site 2)) : Prop :=
  (∀ x ∈ edge, x 1 = (k : ℤ) + 1 → ∀ y ∈ edge, y 1 ≠ (k : ℤ) + 1 →
    y 1 = k ∧ -((k / 12 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ k / 12) ∧
  (∀ y ∈ edge, y 1 = -((k : ℤ) + 1) → ∀ x ∈ edge, x 1 ≠ -((k : ℤ) + 1) →
    x 1 = -(k : ℤ) ∧ -((k / 12 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ k / 12)

/-- Preserve bonds inside the strip and wire the two boundary rows to the targets. -/
noncomputable def wiredKSTConfig (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (edge : Sym2 (Site 2)) : Bool := by
  classical
  exact if ∀ z ∈ edge, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k then ω edge
    else decide (wiredKSTAllowed k edge)

/-- The configuration preserves every bond inside the original strip. -/
theorem wiredKSTConfig_eq_of_interior (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (edge : Sym2 (Site 2)) (h : ∀ z ∈ edge, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) :
    wiredKSTConfig k ω edge = ω edge := by
  classical
  simp only [wiredKSTConfig, ite_eq_left h]

/-- An open bond entering from the upper row meets the upper KST target. -/
theorem wiredKSTConfig_upper_entrance (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (k : ℤ) + 1) (hy : y 1 ≠ (k : ℤ) + 1)
    (he : wiredKSTConfig k ω s(x, y) = true) :
    y 1 = k ∧ -((k / 12 : ℕ) : ℤ) ≤ y 0 ∧ y 0 ≤ k / 12 := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  have ha : wiredKSTAllowed k s(x, y) := by
    simpa only [wiredKSTConfig, ite_eq_right hn, decide_eq_true_eq] using he
  exact ha.1 x (by simp only [Sym2.mem_iff, true_or]) hx y
    (by simp only [Sym2.mem_iff, or_true]) hy

/-- An open bond entering from the lower row meets the lower KST target. -/
theorem wiredKSTConfig_lower_entrance (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hy : y 1 = -((k : ℤ) + 1)) (hx : x 1 ≠ -((k : ℤ) + 1))
    (he : wiredKSTConfig k ω s(x, y) = true) :
    x 1 = -(k : ℤ) ∧ -((k / 12 : ℕ) : ℤ) ≤ x 0 ∧ x 0 ≤ k / 12 := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h y (by simp only [Sym2.mem_iff, or_true])
    omega
  have ha : wiredKSTAllowed k s(x, y) := by
    simpa only [wiredKSTConfig, ite_eq_right hn, decide_eq_true_eq] using he
  exact ha.2 y (by simp only [Sym2.mem_iff, or_true]) hy x
    (by simp only [Sym2.mem_iff, true_or]) hx

/-- Bonds along the upper wired row are open. -/
theorem wiredKSTConfig_upper_row (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (k : ℤ) + 1) (hy : y 1 = (k : ℤ) + 1) :
    wiredKSTConfig k ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredKSTConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredKSTAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- Bonds along the lower wired row are open. -/
theorem wiredKSTConfig_lower_row (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = -((k : ℤ) + 1)) (hy : y 1 = -((k : ℤ) + 1)) :
    wiredKSTConfig k ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredKSTConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredKSTAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- Bonds connecting the upper wired row to its target are open. -/
theorem wiredKSTConfig_upper_connector (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hx : x 1 = (k : ℤ) + 1) (hy : y 1 = k)
    (hl : -((k / 12 : ℕ) : ℤ) ≤ y 0) (hr : y 0 ≤ k / 12) :
    wiredKSTConfig k ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h x (by simp only [Sym2.mem_iff, true_or])
    omega
  rw [wiredKSTConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredKSTAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- Bonds connecting the lower wired row to its target are open. -/
theorem wiredKSTConfig_lower_connector (k : ℕ) (ω : Sym2 (Site 2) → Bool)
    (x y : Site 2) (hy : y 1 = -((k : ℤ) + 1)) (hx : x 1 = -(k : ℤ))
    (hl : -((k / 12 : ℕ) : ℤ) ≤ x 0) (hr : x 0 ≤ k / 12) :
    wiredKSTConfig k ω s(x, y) = true := by
  classical
  have hn : ¬ (∀ z ∈ s(x, y), -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) := by
    intro h
    have h' := h y (by simp only [Sym2.mem_iff, or_true])
    omega
  rw [wiredKSTConfig, ite_eq_right hn]
  simp only [decide_eq_true_eq, wiredKSTAllowed, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  omega

/-- A crossing of the wired rectangle yields an open scale path. -/
theorem exists_kstPath_of_canonical_wired_crossing (k : ℕ) (hk : 0 < k)
    (ω : Sym2 (Site 2) → Bool)
    (hcross : ∃ (a b : centeredPlaneRectangle (k + k / 12) (k + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Walk a b),
      (a : Site 2) 1 = (k : ℤ) + 1 ∧ (b : Site 2) 1 = -((k : ℤ) + 1) ∧
      IsBondOpenWalk (wiredKSTConfig k ω) p) :
    ∃ (a b : centeredPlaneRectangle (k + k / 12) (k + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (k + k / 12) (k + 1))).Walk a b),
      IsKSTPath k p ∧ IsBondOpenWalk ω p := by
  apply exists_kstPath_of_wired_crossing k hk ω (wiredKSTConfig k ω)
  · intro x y hx hy hxy he
    exact (wiredKSTConfig_upper_entrance k ω x y hx hy he).2
  · intro x y hy hx hxy he
    exact (wiredKSTConfig_lower_entrance k ω x y hy hx he).2
  · intro edge hedge he
    rw [wiredKSTConfig_eq_of_interior k ω _] at he
    · exact he
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Sym2.mem_map.mp hz
      have h := (mem_centeredPlaneRectangle _ _ _).mp (hedge z' hz')
      exact ⟨h.2.2.1, h.2.2.2⟩
  · exact hcross

end Sandpile.External.RSW
