import Sandpile.External.RSW.CorridorCascade
import Sandpile.External.RSW.FirstRectangleExit
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.CenteredBridgeSymmetry

/-!
# A wall gives a translated bridge

A path connected to the side of the wider rectangle gives a bridge in a rectangle
shifted toward that side. A first-visit argument clips the connecting walk.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- An open walk from the left side to the central top target gives a left-shifted bridge. -/
theorem translated_kstBridgeEvent_of_left_walk (m : ℕ) (hm : 0 < m)
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (m + 3 * (m / 12)) m}
    (p : (rectangleGraph (centeredPlaneRectangle (m + 3 * (m / 12)) m)).Walk a b)
    (hp : IsBondOpenWalk ω p)
    (ha : (a : Site 2) 0 = -((m + 3 * (m / 12) : ℕ) : ℤ))
    (hbY : (b : Site 2) 1 = m)
    (hbX : -((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0) :
    ω ∈ translatedKSTBridgeEvent m (-kstCorridorShift m) := by
  let Q := centeredPlaneRectangle (m + 3 * (m / 12)) m
  let R := centeredPlaneRectangle (m + m / 12) m
  let v : Site 2 := -kstCorridorShift m
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 := ⟨Subtype.val, fun h => by
    rw [← lattice_eq_zdGraph]
    exact h⟩
  let P := p.map f
  let c : ℤ := (m : ℤ) - ((m / 12 : ℕ) : ℤ)
  have hc : (a : Site 2) 0 ≤ c := by
    dsimp [c] at *
    omega
  have hpbox : ∀ z ∈ P.support, z ∈ Q := by
    intro z hz
    change z ∈ (p.map f).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    exact z.property
  have hpopen : ∀ e ∈ P.edges, e ∈ openPlaneBonds ω := by
    intro e he
    have hmem : e ∈ (lattice 2).edgeSet := by
      rw [lattice_eq_zdGraph]
      exact SimpleGraph.Walk.edges_subset_edgeSet P he
    change e ∈ (p.map f).edges at he
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨hmem, (isBondOpenWalk_iff_local_edges ω p).mp hp e' he'⟩
  have hclip : ∃ (z : Site 2) (q : (LatticeModels.zdGraph 2).Walk (a : Site 2) z),
      (z 0 = c ∨ (z = b)) ∧ (∀ x ∈ q.support, x ∈ Q ∧ x 0 ≤ c) ∧
      ∀ e ∈ q.edges, e ∈ openPlaneBonds ω := by
    by_cases hhit : ∃ z ∈ P.support, z 0 = c
    · obtain ⟨z, hz, q, hqs, hqe, hqd⟩ :=
        exists_prefix_first_mem (O := {z : Site 2 | z 0 = c}) P hhit
      refine ⟨z, q, Or.inl hz, ?_, fun e he => hpopen e (hqe e he)⟩
      intro x hx
      exact ⟨hpbox x (hqs x hx), apply_le_of_darts q 0 c hc hqd x hx⟩
    · refine ⟨b, P, Or.inr rfl, ?_, hpopen⟩
      intro x hx
      refine ⟨hpbox x hx, ?_⟩
      apply apply_le_of_darts P 0 c hc (fun d hd he => ?_) x hx
      exact hhit ⟨d.fst, P.dart_fst_mem_support_of_mem_darts hd, he⟩
  obtain ⟨z, q, hz, hqbox, hqopen⟩ := hclip
  have hqR : ∀ x ∈ q.support, x - v ∈ R := by
    intro x hx
    have hx' := hqbox x hx
    have hQ := (mem_centeredPlaneRectangle _ _ x).mp hx'.1
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [Pi.sub_apply, v, kstCorridorShift, Pi.neg_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_zero, sub_zero]
    dsimp [c] at hx'
    push_cast at *
    omega
  let q' := q.induce {x : Site 2 | x - v ∈ R} hqR
  let g : ((LatticeModels.zdGraph 2).induce {x : Site 2 | x - v ∈ R}) →g
      rectangleGraph R := ⟨fun x => ⟨x.val - v, x.property⟩, fun h => by
        change (lattice 2).Adj (_ - v) (_ - v)
        apply lattice_adj_translate (-v)
        rw [lattice_eq_zdGraph]
        exact h⟩
  let s := q'.map g
  change (ω ∘ Sym2.map (fun x => x + v)) ∈ kstBridgeEvent m
  refine ⟨g ⟨a, hqR _ q.start_mem_support⟩, g ⟨z, hqR _ q.end_mem_support⟩, s, ?_, ?_, ?_⟩
  · left
    change (a : Site 2) 0 - v 0 = -((m + m / 12 : ℕ) : ℤ)
    simp only [v, kstCorridorShift, Pi.neg_apply, Matrix.cons_val_zero]
    push_cast at *
    omega
  · rcases hz with hz | rfl
    · left
      change z 0 - v 0 = ((m + m / 12 : ℕ) : ℤ)
      simp only [v, kstCorridorShift, Pi.neg_apply, Matrix.cons_val_zero]
      dsimp [c] at hz
      push_cast at *
      omega
    · right
      change ((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 - v 0 ∧
        ((b : Site 2) 1 - v 1 = -(m : ℤ) ∨ (b : Site 2) 1 - v 1 = m)
      simp only [v, kstCorridorShift, Pi.neg_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_zero, sub_zero]
      push_cast at *
      exact ⟨by omega, Or.inr hbY⟩
  · apply (isBondOpenWalk_iff_local_edges _ s).mpr
    intro e he
    change e ∈ (q'.map g).edges at he
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    have heq : Sym2.map Subtype.val e' ∈ q.edges := by
      have hh : Sym2.map Subtype.val e' ∈
          (q'.map (SimpleGraph.Embedding.induce {x : Site 2 | x - v ∈ R}).toHom).edges := by
        rw [SimpleGraph.Walk.edges_map]
        exact List.mem_map.mpr ⟨e', he', rfl⟩
      rw [SimpleGraph.Walk.map_induce] at hh
      exact hh
    have hw := (hqopen _ heq).2
    convert hw using 1
    induction e' using Sym2.ind with
    | _ x y =>
      change ω s((x.val - v) + v, (y.val - v) + v) = ω s(x.val, y.val)
      rw [sub_add_cancel, sub_add_cancel]

/-- A left wall at scale `m` yields the bridge shifted toward the left side. -/
theorem kstWallEvent_left_subset_translated_bridge (m : ℕ) (hm : 0 < m) :
    kstWallEvent m m true ⊆ translatedKSTBridgeEvent m (-kstCorridorShift m) := by
  intro ω hω
  obtain ⟨a, b, x, c, p, q, hp, hx, hc, hpo, hqo⟩ := hω
  obtain ⟨r, hr, _⟩ := exists_openWalk_of_mem_support p hpo hx p.start_mem_support
  apply translated_kstBridgeEvent_of_left_walk m hm (q.reverse.append r) (hqo.reverse.append hr)
  · simpa only [Bool.true_eq, ↓reduceIte] using hc
  · exact hp.2.1
  · exact hp.2.2.2.1

/-- Reflection exchanges the left- and right-shifted bridge events. -/
theorem translated_kstBridgeEvent_of_reflect_x (m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    (h : (ω ∘ Sym2.map (reflectPlaneCoordinates true false)) ∈
      translatedKSTBridgeEvent m (-kstCorridorShift m)) :
    ω ∈ translatedKSTBridgeEvent m (kstCorridorShift m) := by
  let F := reflectPlaneCoordinates true false
  let v := kstCorridorShift m
  let f := reflectBridgeRectangle m true false
  change ((ω ∘ Sym2.map F) ∘ Sym2.map (fun z => z + (-v))) ∈ kstBridgeEvent m at h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  change (ω ∘ Sym2.map (fun z => z + v)) ∈ kstBridgeEvent m
  refine ⟨f b, f a, p.reverse.map f, ?_, ?_, ?_⟩
  · change kstBridgeRight m b at hb
    change kstBridgeLeft m (f b)
    simp [kstBridgeLeft, kstBridgeRight, f, reflectBridgeRectangle,
      reflectPlaneCoordinates] at hb ⊢
    omega
  · change kstBridgeLeft m a at ha
    change kstBridgeRight m (f a)
    simp [kstBridgeLeft, kstBridgeRight, f, reflectBridgeRectangle,
      reflectPlaneCoordinates] at ha ⊢
    omega
  · apply (isBondOpenWalk_map F f (fun _ => rfl) (ω ∘ Sym2.map (fun z => z + v))
      p.reverse).mpr
    have he : (ω ∘ Sym2.map (fun z => z + v)) ∘ Sym2.map F =
        (ω ∘ Sym2.map F) ∘ Sym2.map (fun z => z + (-v)) := by
      funext e
      induction e using Sym2.ind with
      | _ x y =>
        have ht (z : Site 2) : F z + v = F (z + (-v)) := by
          ext i
          fin_cases i <;>
            simp [F, reflectPlaneCoordinates, v, kstCorridorShift, Matrix.vecHead, Matrix.vecTail]
          all_goals ring
        simp only [Function.comp_apply, Sym2.map_mk, ht]
    rw [he]
    exact hp.reverse

/-- A right wall at scale `m` yields the bridge shifted toward the right side. -/
theorem kstWallEvent_right_subset_translated_bridge (m : ℕ) (hm : 0 < m) :
    kstWallEvent m m false ⊆ translatedKSTBridgeEvent m (kstCorridorShift m) := by
  intro ω hω
  apply translated_kstBridgeEvent_of_reflect_x m
  obtain ⟨a, b, x, c, p, q, hp, hx, hc, hpo, hqo⟩ := hω
  obtain ⟨r, hr, _⟩ := exists_openWalk_of_mem_support p hpo hx p.start_mem_support
  let f := reflectCenteredBridgeRectangle m (3 * (m / 12)) true false
  have hro : IsBondOpenWalk ω (q.reverse.append r) := hqo.reverse.append hr
  apply translated_kstBridgeEvent_of_left_walk m hm ((q.reverse.append r).map f)
    hro.map_reflectCenteredBridgeRectangle
  · change -(c : Site 2) 0 = -((m + 3 * (m / 12) : ℕ) : ℤ)
    simp only [Bool.false_eq_true, ↓reduceIte] at hc
    omega
  · change (a : Site 2) 1 = m
    exact hp.2.1
  · change -((m / 12 : ℕ) : ℤ) ≤ -(a : Site 2) 0
    have hh := hp.2.2.2.2.1
    omega

/-- A corridor inclusion into the two wall events gives the translated bridge cover. -/
theorem kstCorridorBridgeCover_of_wall_cover (n m k : ℕ) (hm : 0 < m)
    (h : kstExceptionalPathEvent n m k ∩ kstQuasiCrossingEvent m k ⊆
      kstWallEvent m m true ∪ kstWallEvent m m false) :
    KSTCorridorBridgeCover n m k := by
  intro ω hω
  rcases h hω with hl | hr
  · exact Or.inl (kstWallEvent_left_subset_translated_bridge m hm hl)
  · exact Or.inr (kstWallEvent_right_subset_translated_bridge m hm hr)

end Sandpile.External.RSW
