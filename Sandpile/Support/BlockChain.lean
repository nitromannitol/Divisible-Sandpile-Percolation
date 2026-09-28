import Sandpile.Support.BlockVerticalWalk
import Sandpile.Support.BlockGeometry
import Sandpile.Support.BlockSubwalk
import Sandpile.Support.BlockStarIntersect
import Sandpile.Support.PercSquareToWide
import Sandpile.Support.PercAbsHom
import Sandpile.Support.BlockRouteAdj

/-!
# Deterministic block-chaining infrastructure

Deterministic block-chaining infrastructure for the critical level-set percolation
theorem: disjointness of far-apart coarse blocks, connectivity of the level superlevel
set inside one good block, one routing step between two adjacent good blocks, and the
induction that chains a coarse walk of good blocks into a single fine walk of the
level superlevel set (`block_chain`).
-/

set_option maxHeartbeats 1000000
open scoped NNReal
noncomputable section
namespace Sandpile

/-- Distinct coarse sites at sup-norm distance at least three have disjoint
blocks: a site cannot lie in two blocks `2r·z + [0,2r]²` whose anchors differ
in some coordinate by at least `3`. -/
theorem block_disjoint_far (r : ℕ) (hr : 1 ≤ r) (z z' : Site 2) (u : Site 2)
    (hu : ∀ i, |u i - 2 * r * z i| ≤ 2 * r)
    (hu' : ∀ i, |u i - 2 * r * z' i| ≤ 2 * r)
    (hfar : ∃ i, 3 ≤ |z i - z' i|) :
    False := by
  obtain ⟨i, hi⟩ := hfar
  have h1 := hu i
  have h2 := hu' i
  have h3 : (3:ℤ) ≤ |z' i - z i| := by rw [← abs_sub_comm]; exact hi
  have hkey : |2 * r * (z' i - z i)| ≤ 4 * r := by
    have hAB : (u i - 2 * r * z i) - (u i - 2 * r * z' i) = 2 * r * (z' i - z i) := by ring
    have hstep : |2 * r * (z' i - z i)|
        = |(u i - 2 * r * z i) - (u i - 2 * r * z' i)| := by rw [hAB]
    calc |2 * r * (z' i - z i)| = |(u i - 2 * r * z i) - (u i - 2 * r * z' i)| := hstep
      _ ≤ |u i - 2 * r * z i| + |u i - 2 * r * z' i| := abs_sub _ _
      _ ≤ 2 * r + 2 * r := by gcongr
      _ = 4 * r := by ring
  have hlow : 6 * r ≤ |2 * r * (z' i - z i)| := by
    have hne : r ≠ 0 := by omega
    · have hpos : (0:ℤ) < 2 * r := by nlinarith [hne]
      have hsplit : |2 * r * (z' i - z i)| = 2 * r * |z' i - z i| := by
        rw [abs_mul, abs_of_pos hpos]
      rw [hsplit]
      have h6 : (6:ℤ) ≤ 2 * |z' i - z i| := by omega
      have habs : (0:ℤ) ≤ |z' i - z i| := abs_nonneg _
      have hrz : (0:ℤ) ≤ r := by exact_mod_cast Nat.cast_nonneg r
      nlinarith
  omega

/-- Within one good block, the starts of any two bottom-top crossing walks of
the block's square are joined by a nearest-neighbour walk whose every site
has field value at least the level: route through the block's left-right
crossing, which meets both. -/
theorem block_tb_connect {r : ℕ} (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (h : BlockGood r F ℓ z)
    (c₁ d₁ : planeRectangle (2 * r) (2 * r))
    (q₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁)
    (hq₁ : ∀ u ∈ q₁.support, ℓ ≤ F (blockShift r z u))
    (hc₁ : (c₁ : Site 2) 1 = 0) (hd₁ : (d₁ : Site 2) 1 = ↑(2 * r))
    (c₂ d₂ : planeRectangle (2 * r) (2 * r))
    (q₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂)
    (hq₂ : ∀ u ∈ q₂.support, ℓ ≤ F (blockShift r z u))
    (hc₂ : (c₂ : Site 2) 1 = 0) (hd₂ : (d₂ : Site 2) 1 = ↑(2 * r)) :
    ∃ p : (lattice 2).Walk (blockShift r z (c₁ : Site 2)) (blockShift r z (c₂ : Site 2)),
      ∀ u ∈ p.support, ℓ ≤ F u := by
  -- the left-right crossing of the block's square
  simp only [BlockGood] at h
  obtain ⟨a₀, b₀, p₀, ha₀, hb₀, hp₀⟩ :=
    exists_lr_walk_of_le_crossingValue
      (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r z w)) h.1
  -- both bottom-top walks meet the left-right crossing
  obtain ⟨u, hu₁, hu₁'⟩ := nn_lr_tb_intersect p₀ q₁ ha₀ hb₀ hc₁ hd₁
  obtain ⟨u', hu'₁, hu'₂⟩ := nn_lr_tb_intersect p₀ q₂ ha₀ hb₀ hc₂ hd₂
  -- unwrap the intersection sites to elements of the walks
  rw [List.mem_map] at hu₁
  obtain ⟨v₁, hv₁, rfl⟩ := hu₁
  obtain ⟨t₁, ht₁, hut₁⟩ := List.mem_map.mp hu₁'
  have hutw : (v₁ : Site 2) = (t₁ : Site 2) := hut₁.symm
  rw [List.mem_map] at hu'₁
  obtain ⟨v₂, hv₂, rfl⟩ := hu'₁
  obtain ⟨t₂, ht₂, hut₂⟩ := List.mem_map.mp hu'₂
  have hutw' : (v₂ : Site 2) = (t₂ : Site 2) := hut₂.symm
  -- the three subwalks
  obtain ⟨A, hAs⟩ := exists_subwalk q₁ q₁.start_mem_support ht₁
  obtain ⟨B, hBs⟩ := exists_subwalk p₀ hv₁ hv₂
  obtain ⟨C, hCs⟩ := exists_subwalk q₂ ht₂ q₂.start_mem_support
  -- map to the absolute lattice
  have hA : ∀ u ∈ (A.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hq₁ v (hAs v hv)
  have hB : ∀ u ∈ (B.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hp₀ v (hBs v hv)
  have hC : ∀ u ∈ (C.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hq₂ v (hCs v hv)
  -- endpoint matching
  have e1 : blockShift r z (t₁ : Site 2) = blockShift r z (v₁ : Site 2) := by rw [hutw]
  have e2 : blockShift r z (v₂ : Site 2) = blockShift r z (t₂ : Site 2) := by rw [hutw']
  -- concatenate
  refine ⟨SimpleGraph.Walk.append
      (SimpleGraph.Walk.copy (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) A) rfl e1)
      (SimpleGraph.Walk.append
        (SimpleGraph.Walk.copy
          (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) B) rfl e2)
        (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) C)),
    ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_copy] at hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact hA u hu
  · have hu' := List.mem_of_mem_tail hu
    rw [List.mem_append] at hu'
    rcases hu' with hu' | hu'
    · exact hB u hu'
    · exact hC u (List.mem_of_mem_tail hu')

/-- Within one good block, the start of a bottom-top crossing walk and the
start of a left-right crossing walk of the block's square are joined by a
nearest-neighbour walk whose every site has field value at least the level. -/
theorem block_tb_lr_connect {r : ℕ} (F : Site 2 → ℝ) (ℓ : ℝ) (z : Site 2)
    (c₁ d₁ : planeRectangle (2 * r) (2 * r))
    (q₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁)
    (hq₁ : ∀ u ∈ q₁.support, ℓ ≤ F (blockShift r z u))
    (hc₁ : (c₁ : Site 2) 1 = 0) (hd₁ : (d₁ : Site 2) 1 = ↑(2 * r))
    (c₂ d₂ : planeRectangle (2 * r) (2 * r))
    (q₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂)
    (hq₂ : ∀ u ∈ q₂.support, ℓ ≤ F (blockShift r z u))
    (hc₂ : (c₂ : Site 2) 0 = 0) (hd₂ : (d₂ : Site 2) 0 = ↑(2 * r)) :
    ∃ p : (lattice 2).Walk (blockShift r z (c₁ : Site 2)) (blockShift r z (c₂ : Site 2)),
      ∀ u ∈ p.support, ℓ ≤ F u := by
  obtain ⟨u, hu₁, hu₁'⟩ := nn_lr_tb_intersect q₂ q₁
    (show c₂ ∈ rectangleLeft (planeRectangle (2 * r) (2 * r)) by
      exact (mem_rectangleLeft_planeRectangle _).mpr hc₂)
    (show d₂ ∈ rectangleRight (planeRectangle (2 * r) (2 * r)) by
      exact (mem_rectangleRight_planeRectangle _).mpr hd₂)
    hc₁ hd₁
  rw [List.mem_map] at hu₁
  obtain ⟨v₂, hv₂, rfl⟩ := hu₁
  obtain ⟨t₁, ht₁, hut₁⟩ := List.mem_map.mp hu₁'
  have hutw : (v₂ : Site 2) = (t₁ : Site 2) := hut₁.symm
  obtain ⟨A, hAs⟩ := exists_subwalk q₁ q₁.start_mem_support ht₁
  obtain ⟨B, hBs⟩ := exists_subwalk q₂ hv₂ q₂.start_mem_support
  have hA : ∀ u ∈ (A.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hq₁ v (hAs v hv)
  have hB : ∀ u ∈ (B.map (rectAbsHom r z (2 * r) (2 * r))).support, ℓ ≤ F u := by
    intro u hu
    rw [SimpleGraph.Walk.support_map] at hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    exact hq₂ v (hBs v hv)
  have e1 : blockShift r z (t₁ : Site 2) = blockShift r z (v₂ : Site 2) := by rw [hutw]
  refine ⟨SimpleGraph.Walk.append
      (SimpleGraph.Walk.copy (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) A) rfl e1)
      (SimpleGraph.Walk.map (rectAbsHom r z (2 * r) (2 * r)) B),
    ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy] at hu
  rw [List.mem_append] at hu
  rcases hu with hu | hu
  · exact hA u hu
  · exact hB u (List.mem_of_mem_tail hu)

/-- One routing step: for adjacent good blocks, a bottom-top crossing witness
of the first block extends, through the level superlevel set, to a bottom-top
crossing witness of the second block. -/
theorem block_route_step {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) (u v : Site 2)
    (hadj : (lattice 2).Adj u v)
    (hu : BlockGood r F ℓ u) (hv : BlockGood r F ℓ v)
    (c₁ d₁ : planeRectangle (2 * r) (2 * r))
    (q₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁)
    (hq₁ : ∀ w ∈ q₁.support, ℓ ≤ F (blockShift r u w))
    (hc₁ : (c₁ : Site 2) 1 = 0) (hd₁ : (d₁ : Site 2) 1 = ↑(2 * r)) :
    ∃ (c₂ d₂ : planeRectangle (2 * r) (2 * r)),
    ∃ q₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂,
    ∃ p : (lattice 2).Walk (blockShift r u (c₁ : Site 2))
        (blockShift r v (c₂ : Site 2)),
      (∀ w ∈ p.support, ℓ ≤ F w) ∧
      (∀ w ∈ q₂.support, ℓ ≤ F (blockShift r v w)) ∧
      (c₂ : Site 2) 1 = 0 ∧ (d₂ : Site 2) 1 = ↑(2 * r) := by
  have hv' : ℓ ≤ verticalCrossingValue (2 * r) (2 * r)
      (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r v w)) ∧
      ℓ ≤ crossingValue (planeRectangle (2 * r) (2 * r))
      (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r v w)) := by
    simpa only [BlockGood] using ⟨hv.2.1, hv.1⟩
  have hu' : ℓ ≤ crossingValue (planeRectangle (2 * r) (2 * r))
      (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r u w)) := by
    simpa only [BlockGood] using hu.1
  obtain ⟨i, hdir | hdir⟩ := hadj
  · -- v = u + unit i
    fin_cases i
    · -- v = u + e₀ : direct route
      have hunit : (unit : Fin 2 → Site 2) (⟨0, by omega⟩ : Fin 2)
          = ![(1 : ℤ), (0 : ℤ)] := by funext k; fin_cases k <;> simp [unit]
      beta_reduce at hdir
      rw [hunit] at hdir
      subst hdir
      obtain ⟨c₂, d₂, TB₂, hc₂, hd₂, hTB₂⟩ :=
        exists_tb_walk_of_le_verticalCrossingValue
          (fun w : planeRectangle (2 * r) (2 * r) =>
            F (blockShift r (u + ![(1 : ℤ), (0 : ℤ)]) w)) hv'.1
      obtain ⟨a, b, p, ha, hb, hp⟩ := block_route_adj_e0 hr F ℓ u hu c₁ d₁ q₁ hc₁ hd₁ hq₁
        c₂ d₂ TB₂ hc₂ hd₂ hTB₂
      refine ⟨c₂, d₂, TB₂, p.copy ha hb, ?_, hTB₂, hc₂, hd₂⟩
      intro w hw
      rw [SimpleGraph.Walk.support_copy] at hw
      exact hp w hw
    · -- v = u + e₁ : route through left-right witnesses, with connectors
      have hunit : (unit : Fin 2 → Site 2) (⟨1, by omega⟩ : Fin 2)
          = ![(0 : ℤ), (1 : ℤ)] := by funext k; fin_cases k <;> simp [unit]
      beta_reduce at hdir
      rw [hunit] at hdir
      subst hdir
      obtain ⟨a₁, b₁, LR₁, ha₁, hb₁, hLR₁⟩ :=
        exists_lr_walk_of_le_crossingValue
          (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r u w)) hu'
      obtain ⟨a₂, b₂, LR₂, ha₂, hb₂, hLR₂⟩ :=
        exists_lr_walk_of_le_crossingValue
          (fun w : planeRectangle (2 * r) (2 * r) =>
            F (blockShift r (u + ![(0 : ℤ), (1 : ℤ)]) w)) hv'.2
      obtain ⟨c₂, d₂, TB₂, hc₂, hd₂, hTB₂⟩ :=
        exists_tb_walk_of_le_verticalCrossingValue
          (fun w : planeRectangle (2 * r) (2 * r) =>
            F (blockShift r (u + ![(0 : ℤ), (1 : ℤ)]) w)) hv'.1
      obtain ⟨pconn₁, hpconn₁⟩ := block_tb_lr_connect F ℓ u c₁ d₁ q₁ hq₁ hc₁ hd₁
        a₁ b₁ LR₁ hLR₁ ((mem_rectangleLeft_planeRectangle a₁).mp ha₁)
        ((mem_rectangleRight_planeRectangle b₁).mp hb₁)
      obtain ⟨a, b, proute, ha, hb, hproute⟩ :=
        block_route_adj_e1 hr F ℓ u hu
          a₁ b₁ LR₁ ((mem_rectangleLeft_planeRectangle a₁).mp ha₁)
          ((mem_rectangleRight_planeRectangle b₁).mp hb₁) hLR₁
          a₂ b₂ LR₂ ((mem_rectangleLeft_planeRectangle a₂).mp ha₂)
          ((mem_rectangleRight_planeRectangle b₂).mp hb₂) hLR₂
      obtain ⟨pconn₂, hpconn₂⟩ := block_tb_lr_connect F ℓ
        (u + ![(0 : ℤ), (1 : ℤ)]) c₂ d₂ TB₂ hTB₂ hc₂ hd₂ a₂ b₂ LR₂ hLR₂
        ((mem_rectangleLeft_planeRectangle a₂).mp ha₂)
        ((mem_rectangleRight_planeRectangle b₂).mp hb₂)
      refine ⟨c₂, d₂, TB₂,
        (pconn₁.append (proute.copy ha hb)).append pconn₂.reverse, ?_, hTB₂, hc₂, hd₂⟩
      intro w hw
      rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] at hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact hpconn₁ w hw
        · exact hproute w (List.mem_of_mem_tail hw)
      · exact hpconn₂ w (List.mem_reverse.mp (List.mem_of_mem_tail hw))
  · -- u = v + unit i
    fin_cases i
    · -- u = v + e₀ : route at (v, u), reversed
      have hunit : (unit : Fin 2 → Site 2) (⟨0, by omega⟩ : Fin 2)
          = ![(1 : ℤ), (0 : ℤ)] := by funext k; fin_cases k <;> simp [unit]
      beta_reduce at hdir
      rw [hunit] at hdir
      subst hdir
      obtain ⟨c₂, d₂, TB₂, hc₂, hd₂, hTB₂⟩ :=
        exists_tb_walk_of_le_verticalCrossingValue
          (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r v w)) hv'.1
      obtain ⟨a, b, p, ha, hb, hp⟩ := block_route_adj_e0 hr F ℓ v hv c₂ d₂ TB₂ hc₂ hd₂ hTB₂
        c₁ d₁ q₁ hc₁ hd₁ hq₁
      refine ⟨c₂, d₂, TB₂, (p.copy ha hb).reverse, ?_, hTB₂, hc₂, hd₂⟩
      intro w hw
      rw [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] at hw
      exact hp w (by simpa using hw)
    · -- u = v + e₁ : route at (v, u) through left-right witnesses, reversed
      have hunit : (unit : Fin 2 → Site 2) (⟨1, by omega⟩ : Fin 2)
          = ![(0 : ℤ), (1 : ℤ)] := by funext k; fin_cases k <;> simp [unit]
      beta_reduce at hdir
      rw [hunit] at hdir
      subst hdir
      obtain ⟨a₁, b₁, LR₁, ha₁, hb₁, hLR₁⟩ :=
        exists_lr_walk_of_le_crossingValue
          (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r v w)) hv'.2
      obtain ⟨a₂, b₂, LR₂, ha₂, hb₂, hLR₂⟩ :=
        exists_lr_walk_of_le_crossingValue
          (fun w : planeRectangle (2 * r) (2 * r) =>
            F (blockShift r (v + ![(0 : ℤ), (1 : ℤ)]) w)) hu'
      obtain ⟨c₂, d₂, TB₂, hc₂, hd₂, hTB₂⟩ :=
        exists_tb_walk_of_le_verticalCrossingValue
          (fun w : planeRectangle (2 * r) (2 * r) => F (blockShift r v w)) hv'.1
      obtain ⟨pconn₁, hpconn₁⟩ := block_tb_lr_connect F ℓ
        (v + ![(0 : ℤ), (1 : ℤ)]) c₁ d₁ q₁ hq₁ hc₁ hd₁ a₂ b₂ LR₂ hLR₂
        ((mem_rectangleLeft_planeRectangle a₂).mp ha₂)
        ((mem_rectangleRight_planeRectangle b₂).mp hb₂)
      obtain ⟨a, b, proute, ha, hb, hproute⟩ :=
        block_route_adj_e1 hr F ℓ v hv
          a₁ b₁ LR₁ ((mem_rectangleLeft_planeRectangle a₁).mp ha₁)
          ((mem_rectangleRight_planeRectangle b₁).mp hb₁) hLR₁
          a₂ b₂ LR₂ ((mem_rectangleLeft_planeRectangle a₂).mp ha₂)
          ((mem_rectangleRight_planeRectangle b₂).mp hb₂) hLR₂
      obtain ⟨pconn₂, hpconn₂⟩ := block_tb_lr_connect F ℓ v c₂ d₂ TB₂ hTB₂ hc₂ hd₂
        a₁ b₁ LR₁ hLR₁ ((mem_rectangleLeft_planeRectangle a₁).mp ha₁)
        ((mem_rectangleRight_planeRectangle b₁).mp hb₁)
      refine ⟨c₂, d₂, TB₂,
        pconn₁.append ((proute.copy ha hb).reverse.append pconn₂.reverse), ?_,
        hTB₂, hc₂, hd₂⟩
      intro w hw
      rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_reverse,
        SimpleGraph.Walk.support_copy] at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hpconn₁ w hw
      · rcases List.mem_append.mp (List.mem_of_mem_tail hw) with hw | hw
        · exact hproute w (List.mem_reverse.mp hw)
        · exact hpconn₂ w (List.mem_reverse.mp (List.mem_of_mem_tail hw))

/-- A coarse walk through good blocks lifts to a fine walk of the level
superlevel set, from the start of a bottom-top crossing witness of the first
block to the start of a bottom-top crossing witness of the last block. -/
theorem block_chain {r : ℕ} (hr : 1 ≤ r) (F : Site 2 → ℝ) (ℓ : ℝ) :
    ∀ (z z' : Site 2) (Q : (lattice 2).Walk z z'),
    (∀ w ∈ Q.support, BlockGood r F ℓ w) →
    ∀ (c₁ d₁ : planeRectangle (2 * r) (2 * r))
      (q₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁),
    (∀ w ∈ q₁.support, ℓ ≤ F (blockShift r z w)) →
    (c₁ : Site 2) 1 = 0 → (d₁ : Site 2) 1 = ↑(2 * r) →
    ∃ (c₂ d₂ : planeRectangle (2 * r) (2 * r)),
    ∃ q₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂,
    ∃ p : (lattice 2).Walk (blockShift r z (c₁ : Site 2))
        (blockShift r z' (c₂ : Site 2)),
      (∀ w ∈ p.support, ℓ ≤ F w) ∧
      (∀ w ∈ q₂.support, ℓ ≤ F (blockShift r z' w)) ∧
      (c₂ : Site 2) 1 = 0 ∧ (d₂ : Site 2) 1 = ↑(2 * r) := by
  intro z z' Q
  refine SimpleGraph.Walk.rec
    (motive := fun a b Q => (∀ w ∈ Q.support, BlockGood r F ℓ w) →
      ∀ (c₁ d₁ : planeRectangle (2 * r) (2 * r))
        (q₁ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₁ d₁),
      (∀ w ∈ q₁.support, ℓ ≤ F (blockShift r a w)) →
      (c₁ : Site 2) 1 = 0 → (d₁ : Site 2) 1 = ↑(2 * r) →
      ∃ (c₂ d₂ : planeRectangle (2 * r) (2 * r)),
      ∃ q₂ : (rectangleGraph (planeRectangle (2 * r) (2 * r))).Walk c₂ d₂,
      ∃ p : (lattice 2).Walk (blockShift r a (c₁ : Site 2))
          (blockShift r b (c₂ : Site 2)),
        (∀ w ∈ p.support, ℓ ≤ F w) ∧
        (∀ w ∈ q₂.support, ℓ ≤ F (blockShift r b w)) ∧
        (c₂ : Site 2) 1 = 0 ∧ (d₂ : Site 2) 1 = ↑(2 * r)) ?_ ?_ Q
  · intro u hQ c₁ d₁ q₁ hq₁ hc₁ hd₁
    refine ⟨c₁, d₁, q₁, SimpleGraph.Walk.nil, ?_, hq₁, hc₁, hd₁⟩
    intro v hv
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    rw [hv]
    exact hq₁ c₁ q₁.start_mem_support
  · intro u v w hadj Q' ih hQ c₁ d₁ q₁ hq₁ hc₁ hd₁
    -- the head block is good, and so are all blocks along Q'
    have hu : BlockGood r F ℓ u := hQ u (by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inl trivial)
    have hQ' : ∀ x ∈ Q'.support, BlockGood r F ℓ x := fun x hx => hQ x (by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr hx)
    have hv : BlockGood r F ℓ v := hQ' v Q'.start_mem_support
    -- route one step from u to v
    obtain ⟨c₂, d₂, q₂, p₁, hp₁, hq₂, hc₂, hd₂⟩ :=
      block_route_step hr F ℓ u v hadj hu hv c₁ d₁ q₁ hq₁ hc₁ hd₁
    -- chain along Q'
    obtain ⟨c₃, d₃, q₃, p₂, hp₂, hq₃, hc₃, hd₃⟩ :=
      ih hQ' c₂ d₂ q₂ hq₂ hc₂ hd₂
    refine ⟨c₃, d₃, q₃, ?_, ?_, hq₃, hc₃, hd₃⟩
    · exact p₁.append p₂
    · intro x hx
      rw [SimpleGraph.Walk.support_append] at hx
      obtain hx | hx := List.mem_append.mp hx
      · exact hp₁ x hx
      · exact hp₂ x (List.mem_of_mem_tail hx)

end Sandpile
