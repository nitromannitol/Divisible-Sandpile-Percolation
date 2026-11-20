import Sandpile.External.RSW.WiredDualInterior

/-!
# Boundary constraints for wired dual walks

An open dual walk confined to either wired target row cannot cross the left
endpoint of the target interval.
-/

namespace Sandpile.External.RSW

/-- An open upper-row dual edge cannot cross the left target connector. -/
theorem wired_dual_upper_stays_left (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = m) (hy : y 1 = m)
    (hop : dualBondConfig (wiredArmConfig m ω) s(x, y) = true)
    (hleft : x 0 < -((m / 64 : ℕ) : ℤ)) :
    y 0 < -((m / 64 : ℕ) : ℤ) := by
  by_contra hn
  have hadj := lattice_two_adj_cases hxy
  have hy0 : y 0 = -((m / 64 : ℕ) : ℤ) := by omega
  have he : x = y - Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp <;> omega
  have hclosed := dualBondConfig_wiredArm_upper_connector m ω y hy (by omega) (by omega)
  rw [he, hclosed] at hop
  contradiction

/-- An open lower-row dual edge cannot cross the left target connector. -/
theorem wired_dual_lower_stays_left (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = -((m : ℤ) + 1)) (hy : y 1 = -((m : ℤ) + 1))
    (hop : dualBondConfig (wiredArmConfig m ω) s(x, y) = true)
    (hleft : x 0 < -((m / 64 : ℕ) : ℤ)) :
    y 0 < -((m / 64 : ℕ) : ℤ) := by
  by_contra hn
  have hadj := lattice_two_adj_cases hxy
  have hy0 : y 0 = -((m / 64 : ℕ) : ℤ) := by omega
  have he : x = y - Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp <;> omega
  have hclosed := dualBondConfig_wiredArm_lower_connector m ω y hy (by omega) (by omega)
  rw [he, hclosed] at hop
  contradiction

/-- An open upper-row dual edge cannot cross the right target connector. -/
theorem wired_dual_upper_stays_right (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = m) (hy : y 1 = m)
    (hop : dualBondConfig (wiredArmConfig m ω) s(x, y) = true)
    (hright : ((m / 64 : ℕ) : ℤ) ≤ x 0) :
    ((m / 64 : ℕ) : ℤ) ≤ y 0 := by
  by_contra hn
  have hadj := lattice_two_adj_cases hxy
  have hx0 : x 0 = ((m / 64 : ℕ) : ℤ) := by omega
  have he : y = x - Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp <;> omega
  have hclosed := dualBondConfig_wiredArm_upper_connector m ω x hx (by omega) (by omega)
  rw [Sym2.eq_swap, he, hclosed] at hop
  contradiction

/-- An open lower-row dual edge cannot cross the right target connector. -/
theorem wired_dual_lower_stays_right (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = -((m : ℤ) + 1)) (hy : y 1 = -((m : ℤ) + 1))
    (hop : dualBondConfig (wiredArmConfig m ω) s(x, y) = true)
    (hright : ((m / 64 : ℕ) : ℤ) ≤ x 0) :
    ((m / 64 : ℕ) : ℤ) ≤ y 0 := by
  by_contra hn
  have hadj := lattice_two_adj_cases hxy
  have hx0 : x 0 = ((m / 64 : ℕ) : ℤ) := by omega
  have he : y = x - Pi.single 0 1 := by
    ext i
    fin_cases i <;> simp <;> omega
  have hclosed := dualBondConfig_wiredArm_lower_connector m ω x hx (by omega) (by omega)
  rw [Sym2.eq_swap, he, hclosed] at hop
  contradiction

/-- An open walk on the upper target row remains left of the connector. -/
theorem IsBondOpenWalk.wired_dual_upper_support_left (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, (z : Site 2) 1 = m)
    (ha : (a : Site 2) 0 < -((m / 64 : ℕ) : ℤ)) :
    ∀ z ∈ p.support, (z : Site 2) 0 < -((m / 64 : ℕ) : ℤ) := by
  induction p with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact ha
  | @cons a b c hab p ih =>
    have hs' : ∀ z ∈ p.support, (z : Site 2) 1 = m :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have ha' := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have hb' := hs' b p.start_mem_support
    have hb := wired_dual_upper_stays_left m ω hab ha' hb' hp.1 ha
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hp.2 hs' hb z hz

/-- An open walk on the lower target row remains left of the connector. -/
theorem IsBondOpenWalk.wired_dual_lower_support_left (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, (z : Site 2) 1 = -((m : ℤ) + 1))
    (ha : (a : Site 2) 0 < -((m / 64 : ℕ) : ℤ)) :
    ∀ z ∈ p.support, (z : Site 2) 0 < -((m / 64 : ℕ) : ℤ) := by
  induction p with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact ha
  | @cons a b c hab p ih =>
    have hs' : ∀ z ∈ p.support, (z : Site 2) 1 = -((m : ℤ) + 1) :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have ha' := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have hb' := hs' b p.start_mem_support
    have hb := wired_dual_lower_stays_left m ω hab ha' hb' hp.1 ha
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hp.2 hs' hb z hz

/-- An open walk on the upper target row remains right of the connector. -/
theorem IsBondOpenWalk.wired_dual_upper_support_right (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, (z : Site 2) 1 = m)
    (ha : ((m / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0) :
    ∀ z ∈ p.support, ((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 := by
  induction p with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact ha
  | @cons a b c hab p ih =>
    have hs' : ∀ z ∈ p.support, (z : Site 2) 1 = m :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have ha' := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have hb' := hs' b p.start_mem_support
    have hb := wired_dual_upper_stays_right m ω hab ha' hb' hp.1 ha
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hp.2 hs' hb z hz

/-- An open walk on the lower target row remains right of the connector. -/
theorem IsBondOpenWalk.wired_dual_lower_support_right (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, (z : Site 2) 1 = -((m : ℤ) + 1))
    (ha : ((m / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0) :
    ∀ z ∈ p.support, ((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 := by
  induction p with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact ha
  | @cons a b c hab p ih =>
    have hs' : ∀ z ∈ p.support, (z : Site 2) 1 = -((m : ℤ) + 1) :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have ha' := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have hb' := hs' b p.start_mem_support
    have hb := wired_dual_lower_stays_right m ω hab ha' hb' hp.1 ha
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hp.2 hs' hb z hz

end Sandpile.External.RSW
