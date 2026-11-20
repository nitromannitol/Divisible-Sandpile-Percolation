import Sandpile.External.RSW.RefinedLatticeWalk
import Sandpile.External.RSW.WiredKSTDualEdges

/-!
# Refined dual connectors

A refined dual path can meet the point immediately above a primal vertex only
through the horizontal dual edge crossing the associated vertical bond.
-/

namespace Sandpile.External.RSW

/-- A refined dual walk through the upper neighbor of a primal vertex uses its crossing edge. -/
theorem horizontal_edge_of_refined_dual_upper_neighbor {a b : Site 2}
    (q : (lattice 2).Walk a b) (x : Site 2)
    (h : refinedVertex 0 x + Pi.single 1 1 ∈
      (refinedLatticeWalk (fun _ => 1) q).support) :
    s(x - Pi.single 0 1, x) ∈ q.edges := by
  change refinedVertex 0 x + Pi.single 1 1 ∈
    (subdividedWalk (G := lattice 2) (H := lattice 2)
      (refinedVertex (fun _ => 1)) (refinedMidpoint (fun _ => 1)) _ _ q).support at h
  rw [mem_subdividedWalk_support_iff] at h
  rcases h with ⟨y, hy, he⟩ | ⟨e, he, hm⟩
  · have h0 := congrFun he 0
    simp only [refinedVertex, Pi.zero_apply, Pi.add_apply, Pi.single_eq_of_ne
      (by decide : (0 : Fin 2) ≠ 1), add_zero] at h0
    omega
  · revert he hm
    refine Sym2.inductionOn e ?_
    intro y z he hm
    have h0 := congrFun hm 0
    have h1 := congrFun hm 1
    simp only [refinedMidpoint, Sym2.lift_mk, refinedVertex, Pi.zero_apply,
      Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Pi.single_eq_same, add_zero] at h0 h1
    have hadj := q.adj_of_mem_edges he
    obtain hc | hc | hc | hc := lattice_two_adj_cases hadj
    · have hy : y = x - Pi.single 0 1 := by
        ext i
        fin_cases i <;> simp <;> omega
      have hz : z = x := by
        ext i
        fin_cases i <;> simp <;> omega
      simpa only [hy, hz] using he
    · have hy : y = x := by
        ext i
        fin_cases i <;> simp <;> omega
      have hz : z = x - Pi.single 0 1 := by
        ext i
        fin_cases i <;> simp <;> omega
      rw [hy, hz, Sym2.eq_swap] at he
      exact he
    · omega
    · omega

/-- A wired-open dual walk avoids the refined upper connector endpoint. -/
theorem refined_wired_dual_avoids_upper_connector (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) {a b : Site 2} (q : (lattice 2).Walk a b)
    (hq : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true)
    (x : Site 2) (hx : x 1 = k)
    (hl : -((k / 12 : ℕ) : ℤ) ≤ x 0) (hu : x 0 ≤ k / 12) :
    refinedVertex 0 x + Pi.single 1 1 ∉
      (refinedLatticeWalk (fun _ => 1) q).support := by
  intro h
  have he := horizontal_edge_of_refined_dual_upper_neighbor q x h
  have hopen := hq _ he
  rw [dualBondConfig_wiredKST_upper_connector k ω x hx hl hu] at hopen
  contradiction

/-- A wired-open dual walk avoids the refined lower connector endpoint. -/
theorem refined_wired_dual_avoids_lower_connector (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) {a b : Site 2} (q : (lattice 2).Walk a b)
    (hq : ∀ f ∈ q.edges, dualBondConfig (wiredKSTConfig k ω) f = true)
    (x : Site 2) (hx : x 1 = -(k : ℤ))
    (hl : -((k / 12 : ℕ) : ℤ) ≤ x 0) (hu : x 0 ≤ k / 12) :
    refinedVertex 0 x - Pi.single 1 1 ∉
      (refinedLatticeWalk (fun _ => 1) q).support := by
  let y : Site 2 := x - Pi.single 1 1
  have hy0 : y 0 = x 0 := by simp [y]
  have hy1 : y 1 = -((k : ℤ) + 1) := by
    simp only [y, Pi.sub_apply, Pi.single_eq_same, hx]
    omega
  have heq : refinedVertex 0 y + Pi.single 1 1 =
      refinedVertex 0 x - Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [refinedVertex, y] <;> omega
  intro h
  have he := horizontal_edge_of_refined_dual_upper_neighbor q y (heq ▸ h)
  have hopen := hq _ he
  have hc := dualBondConfig_wiredKST_lower_connector k ω y hy1 (by omega) (by omega)
  rw [hc] at hopen
  contradiction

end Sandpile.External.RSW
