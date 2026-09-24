/-
Replacement of star steps by one or two nearest-neighbor steps in a rectangle.
The inserted corner loses at most the largest nearest-neighbor increment,
independently of the length of the original walk.
-/
import Sandpile.Support.RectangleIncrement
import Sandpile.Support.StarCrossings

open scoped BigOperators
noncomputable section
namespace Sandpile

lemma walk_replace_edges {V : Type*} (G H : SimpleGraph V) (F : V → ℝ)
    {level loss : ℝ} (hloss : 0 ≤ loss)
    (hstep : ∀ x y, G.Adj x y → level ≤ F x → level ≤ F y →
      ∃ q : H.Walk x y, ∀ z ∈ q.support, level - loss ≤ F z)
    {a b : V} (p : G.Walk a b) (hp : ∀ z ∈ p.support, level ≤ F z) :
    ∃ q : H.Walk a b, ∀ z ∈ q.support, level - loss ≤ F z := by
  induction p with
  | nil =>
    refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro z hz
    have hh := hp z hz
    linarith
  | @cons a b c hab p ih =>
    have ha : level ≤ F a := hp a (by simp)
    have ht (z : V) (hz : z ∈ p.support) : level ≤ F z := hp z (by simp [hz])
    obtain ⟨q, hq⟩ := hstep a b hab ha (ht b p.start_mem_support)
    obtain ⟨q', hq'⟩ := ih ht
    refine ⟨q.append q', ?_⟩
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff q q').mp hz with hz | hz
    · exact hq z hz
    · exact hq' z hz

lemma lattice_adj_of_one_coordinate {d : ℕ} {z w : Site d} (i : Fin d)
    (hsame : ∀ j, j ≠ i → w j = z j) (hstep : |w i - z i| = 1) : (lattice d).Adj z w := by
  rcases le_total (z i) (w i) with hi | hi
  · rw [abs_of_nonneg (sub_nonneg.mpr hi)] at hstep
    refine ⟨i, Or.inl ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj, add_zero]
      exact hsame j hj
  · rw [abs_of_nonpos (sub_nonpos.mpr hi)] at hstep
    refine ⟨i, Or.inr ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Pi.add_apply, unit, Pi.single_eq_same]
      omega
    · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj, add_zero]
      exact (hsame j hj).symm

lemma rectangle_corner_mem {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q) (z w : Q) :
    (![w.val 0, z.val 1] : Site 2) ∈ Q := by
  obtain ⟨lo, hi, hQ⟩ := hQ
  apply (hQ _).mpr
  intro i
  fin_cases i
  · exact (hQ w).mp w.property 0
  · exact (hQ z).mp z.property 1

lemma rectangle_star_adj_one_or_two_steps {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    {z w : Q} (hzw : ((starLatticeGraph 2).induce (Q : Set (Site 2))).Adj z w) :
    (rectangleGraph Q).Adj z w ∨ ∃ m : Q, (rectangleGraph Q).Adj z m ∧ (rectangleGraph Q).Adj m w := by
  have hdiff (i : Fin 2) : |(w : Site 2) i - (z : Site 2) i| ≤ 1 := by
    have hh : (((z : Site 2) i - (w : Site 2) i).natAbs : ℤ) ≤ 1 := by
      exact_mod_cast hzw.2 i
    simpa only [Int.natCast_natAbs, abs_sub_comm] using hh
  have hne : (z : Site 2) ≠ (w : Site 2) := hzw.1
  by_cases h0 : (z : Site 2) 0 = (w : Site 2) 0
  · left
    have h1 : (z : Site 2) 1 ≠ (w : Site 2) 1 := by
      intro hh
      apply hne
      funext i
      fin_cases i <;> assumption
    apply lattice_adj_of_one_coordinate (i := (1 : Fin 2))
    · intro j hj
      fin_cases j
      · exact h0.symm
      · exact (hj rfl).elim
    · change |(w : Site 2) 1 - (z : Site 2) 1| = 1
      have hh := hdiff 1
      have hn : (w : Site 2) 1 - (z : Site 2) 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have hp : 0 < |(w : Site 2) 1 - (z : Site 2) 1| := abs_pos.mpr hn
      omega
  · by_cases h1 : (z : Site 2) 1 = (w : Site 2) 1
    · left
      apply lattice_adj_of_one_coordinate (i := (0 : Fin 2))
      · intro j hj
        fin_cases j
        · exact (hj rfl).elim
        · exact h1.symm
      · change |(w : Site 2) 0 - (z : Site 2) 0| = 1
        have hh := hdiff 0
        have hn : (w : Site 2) 0 - (z : Site 2) 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
        have hp : 0 < |(w : Site 2) 0 - (z : Site 2) 0| := abs_pos.mpr hn
        omega
    · right
      let m : Q := ⟨![w.val 0, z.val 1], rectangle_corner_mem hQ z w⟩
      refine ⟨m, ?_, ?_⟩
      · apply lattice_adj_of_one_coordinate (i := (0 : Fin 2))
        · intro j hj
          fin_cases j
          · exact (hj rfl).elim
          · rfl
        · change |(w : Site 2) 0 - (z : Site 2) 0| = 1
          have hh := hdiff 0
          have hn : (w : Site 2) 0 - (z : Site 2) 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h0)
          have hp : 0 < |(w : Site 2) 0 - (z : Site 2) 0| := abs_pos.mpr hn
          omega
      · apply lattice_adj_of_one_coordinate (i := (1 : Fin 2))
        · intro j hj
          fin_cases j
          · rfl
          · exact (hj rfl).elim
        · change |(w : Site 2) 1 - (z : Site 2) 1| = 1
          have hh := hdiff 1
          have hn : (w : Site 2) 1 - (z : Site 2) 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
          have hp : 0 < |(w : Site 2) 1 - (z : Site 2) 1| := abs_pos.mpr hn
          omega

lemma rectangle_star_walk_to_nn {Q : Finset (Site 2)} [Nonempty Q] (hQ : IsLatticeRectangle Q)
    (F : Q → ℝ) {level : ℝ} {a b : Q}
    (p : ((starLatticeGraph 2).induce (Q : Set (Site 2))).Walk a b)
    (hp : ∀ z ∈ p.support, level ≤ F z) :
    ∃ q : (rectangleGraph Q).Walk a b,
      ∀ z ∈ q.support, level - edgeOscillation (rectangleGraph Q) F ≤ F z := by
  apply walk_replace_edges _ _ F (edgeOscillation_nonneg _ _) ?_ p hp
  intro z w hzw hz hw
  have hnonneg := edgeOscillation_nonneg (rectangleGraph Q) F
  rcases rectangle_star_adj_one_or_two_steps hQ hzw with hzw | ⟨m, hzm, hmw⟩
  · refine ⟨SimpleGraph.Walk.cons hzw SimpleGraph.Walk.nil, ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> linarith
  · have hm : level - edgeOscillation (rectangleGraph Q) F ≤ F m := by
      have hh := abs_sub_le_edgeOscillation (rectangleGraph Q) F hzm
      have hh' := (abs_le.mp hh).2
      linarith
    refine ⟨SimpleGraph.Walk.cons hzm (SimpleGraph.Walk.cons hmw SimpleGraph.Walk.nil), ?_⟩
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> linarith

end Sandpile
