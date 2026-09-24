/-
Compactness of connected crossing witnesses and passage to an increasing limit
of closed superlevel sets.
-/
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.Separation.Regular

open Set Topology TopologicalSpace

namespace Sandpile.Support.CrossCompact

/-- Preconnected compact sets form a closed subset of the Vietoris space. -/
theorem isClosed_preconnected_compacts {X : Type*} [TopologicalSpace X]
    [T2Space X] [NormalSpace X] :
    IsClosed {K : Compacts X | IsPreconnected (K : Set X)} := by
  apply isClosed_of_closure_subset
  intro K hK
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed K.isCompact.isClosed).2
  intro u v hu hv hcover huv
  by_contra h
  push Not at h
  obtain ⟨x, hxK, hxu⟩ := Set.not_subset.mp h.1
  obtain ⟨y, hyK, hyv⟩ := Set.not_subset.mp h.2
  have hxv : x ∈ v := (hcover hxK).resolve_left hxu
  have hyu : y ∈ u := (hcover hyK).resolve_right hyv
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := normal_separation hu hv huv
  let O : Set (Compacts X) := {L | (L : Set X) ⊆ U ∪ V} ∩
    {L | ((L : Set X) ∩ U).Nonempty} ∩ {L | ((L : Set X) ∩ V).Nonempty}
  have hO : IsOpen O :=
    ((Compacts.isOpen_subsets_of_isOpen (hU.union hV)).inter
      (Compacts.isOpen_inter_nonempty_of_isOpen hU)).inter
      (Compacts.isOpen_inter_nonempty_of_isOpen hV)
  have hKO : K ∈ O :=
    ⟨⟨hcover.trans (union_subset_union huU hvV), ⟨y, hyK, huU hyu⟩⟩,
      ⟨x, hxK, hvV hxv⟩⟩
  obtain ⟨L, hLO, hL⟩ := (mem_closure_iff.1 hK) O hO hKO
  obtain ⟨z, _, hzU, hzV⟩ := hL U V hU hV hLO.1.1 hLO.1.2 hLO.2
  exact Set.disjoint_left.1 hUV hzU hzV

/-- Connected compact witnesses meeting two closed sets survive a decreasing
intersection inside a fixed compact set. -/
theorem exists_connected_compact_iInter {X : Type*} [TopologicalSpace X]
    [T2Space X] [NormalSpace X] {K A B : Set X} (hK : IsCompact K)
    (hA : IsClosed A) (hB : IsClosed B) (S : ℕ → Set X)
    (hS : ∀ n, IsClosed (S n)) (hmono : Antitone S)
    (hw : ∀ n, ∃ C : Set X, C ⊆ K ∩ S n ∧ IsCompact C ∧ IsConnected C ∧
      (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty) :
    ∃ C : Set X, C ⊆ K ∩ ⋂ n, S n ∧ IsCompact C ∧ IsConnected C ∧
      (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty := by
  let F : ℕ → Set (Compacts X) := fun n =>
    {C | (C : Set X) ⊆ K ∩ S n} ∩ {C | IsPreconnected (C : Set X)} ∩
      {C | ((C : Set X) ∩ A).Nonempty} ∩ {C | ((C : Set X) ∩ B).Nonempty}
  have hclosed : ∀ n, IsClosed (F n) := fun n =>
    (((Compacts.isClosed_subsets_of_isClosed (hK.isClosed.inter (hS n))).inter
      isClosed_preconnected_compacts).inter
      (Compacts.isClosed_inter_nonempty_of_isClosed hA)).inter
      (Compacts.isClosed_inter_nonempty_of_isClosed hB)
  have hcompact : IsCompact (F 0) :=
    (Compacts.isCompact_subsets_of_isCompact hK).of_isClosed_subset (hclosed 0)
      (fun _ h => h.1.1.1.trans inter_subset_left)
  have hnonempty : ∀ n, (F n).Nonempty := by
    intro n
    obtain ⟨C, hsub, hcomp, hconn, hCA, hCB⟩ := hw n
    exact ⟨⟨C, hcomp⟩, ⟨⟨⟨hsub, hconn.2⟩, hCA⟩, hCB⟩⟩
  have hdecr : ∀ n, F (n + 1) ⊆ F n := by
    intro n C hC
    exact ⟨⟨⟨hC.1.1.1.trans (inter_subset_inter_right K (hmono (Nat.le_succ n))),
      hC.1.1.2⟩, hC.1.2⟩, hC.2⟩
  obtain ⟨C, hC⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hdecr hnonempty hcompact hclosed
  have hall : ∀ n, C ∈ F n := Set.mem_iInter.mp hC
  refine ⟨C, ?_, C.isCompact, ⟨?_, (hall 0).1.1.2⟩, (hall 0).1.2, (hall 0).2⟩
  · intro x hx
    exact ⟨((hall 0).1.1.1 hx).1,
      Set.mem_iInter.mpr fun n => ((hall n).1.1.1 hx).2⟩
  · exact (hall 0).1.2.mono inter_subset_left

end Sandpile.Support.CrossCompact
