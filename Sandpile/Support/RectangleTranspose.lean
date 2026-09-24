/-
Coordinate transposition of rectangle paths and vertical crossing values.
-/
import Sandpile.Support.CrossingWitness
import Sandpile.Support.KernelPermutation
import Sandpile.Support.PlaneRectangle

noncomputable section
namespace Sandpile

lemma lattice_adj_permute {d : ℕ} (e : Fin d ≃ Fin d) {z w : Site d}
    (hzw : (lattice d).Adj z w) : (lattice d).Adj (permuteSite e z) (permuteSite e w) := by
  obtain ⟨i, hi | hi⟩ := hzw
  · refine ⟨e.symm i, Or.inl ?_⟩
    rw [hi, map_add, permuteSite_unit]
  · refine ⟨e.symm i, Or.inr ?_⟩
    rw [hi, map_add, permuteSite_unit]

lemma planeRectangle_nonempty (w h : ℕ) : (planeRectangle w h).Nonempty := by
  refine ⟨0, (mem_planeRectangle w h 0).mpr ?_⟩
  simp

lemma mem_rectangleLeft_planeRectangle {w h : ℕ} (z : planeRectangle w h) :
    z ∈ rectangleLeft (planeRectangle w h) ↔ (z : Site 2) 0 = 0 := by
  classical
  simp only [rectangleLeft, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    have hh := hz 0 ((mem_planeRectangle w h 0).mpr (by simp))
    have hn := (mem_planeRectangle w h z).mp z.property
    change (z : Site 2) 0 ≤ 0 at hh
    omega
  · intro hz y hy
    rw [hz]
    exact ((mem_planeRectangle w h y).mp hy).1

lemma mem_rectangleRight_planeRectangle {w h : ℕ} (z : planeRectangle w h) :
    z ∈ rectangleRight (planeRectangle w h) ↔ (z : Site 2) 0 = w := by
  classical
  simp only [rectangleRight, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    have hh := hz (![w, 0]) ((mem_planeRectangle w h _).mpr (by simp))
    have hn := (mem_planeRectangle w h z).mp z.property
    change (w : ℤ) ≤ (z : Site 2) 0 at hh
    omega
  · intro hz y hy
    rw [hz]
    exact ((mem_planeRectangle w h y).mp hy).2.1

lemma permuteSite_swap_plane (z : Site 2) :
    permuteSite (Equiv.swap (0 : Fin 2) 1) z = ![z 1, z 0] := by
  ext i
  fin_cases i <;> simp [permuteSite]

def transposeRectangle (w h : ℕ) : planeRectangle w h ≃ planeRectangle h w where
  toFun z := ⟨permuteSite (Equiv.swap (0 : Fin 2) 1) z, by
    rw [permuteSite_swap_plane, mem_planeRectangle]
    have hz := (mem_planeRectangle w h z).mp z.property
    exact ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩⟩
  invFun z := ⟨permuteSite (Equiv.swap (0 : Fin 2) 1) z, by
    rw [permuteSite_swap_plane, mem_planeRectangle]
    have hz := (mem_planeRectangle h w z).mp z.property
    exact ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩⟩
  left_inv z := by
    apply Subtype.ext
    change permuteSite (Equiv.swap (0 : Fin 2) 1) (permuteSite (Equiv.swap (0 : Fin 2) 1) (z : Site 2)) = z
    rw [permuteSite_swap_plane, permuteSite_swap_plane]
    ext i
    fin_cases i <;> rfl
  right_inv z := by
    apply Subtype.ext
    change permuteSite (Equiv.swap (0 : Fin 2) 1) (permuteSite (Equiv.swap (0 : Fin 2) 1) (z : Site 2)) = z
    rw [permuteSite_swap_plane, permuteSite_swap_plane]
    ext i
    fin_cases i <;> rfl

lemma transposeRectangle_transpose (w h : ℕ) (z : planeRectangle w h) :
    transposeRectangle h w (transposeRectangle w h z) = z := (transposeRectangle w h).symm_apply_apply z

lemma transposeRectangle_coord_zero (w h : ℕ) (z : planeRectangle w h) :
    ((transposeRectangle w h z : planeRectangle h w) : Site 2) 0 = (z : Site 2) 1 := by
  change (permuteSite (Equiv.swap (0 : Fin 2) 1) (z : Site 2)) 0 = _
  rw [permuteSite_swap_plane]
  rfl

def rectangleTransposeHom (w h : ℕ) : rectangleGraph (planeRectangle w h) →g rectangleGraph (planeRectangle h w) where
  toFun := transposeRectangle w h
  map_rel' hz := lattice_adj_permute (Equiv.swap (0 : Fin 2) 1) hz

def verticalCrossingValue (w h : ℕ) (F : planeRectangle w h → ℝ) : ℝ :=
  crossingValue (planeRectangle h w) (fun z => F (transposeRectangle h w z))

lemma le_verticalCrossingValue_of_walk {w h : ℕ} (F : planeRectangle w h → ℝ)
    {a b : planeRectangle w h} (p : (rectangleGraph (planeRectangle w h)).Walk a b)
    (ha : (a : Site 2) 1 = 0) (hb : (b : Site 2) 1 = h) {level : ℝ}
    (hp : ∀ z ∈ p.support, level ≤ F z) : level ≤ verticalCrossingValue w h F := by
  apply le_crossingValue_of_walk (isLatticeRectangle_planeRectangle h w)
    (p.map (rectangleTransposeHom w h))
  · apply (mem_rectangleLeft_planeRectangle _).mpr
    exact (transposeRectangle_coord_zero w h a).trans ha
  · apply (mem_rectangleRight_planeRectangle _).mpr
    exact (transposeRectangle_coord_zero w h b).trans hb
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    change level ≤ F (transposeRectangle h w (transposeRectangle w h y))
    rw [transposeRectangle_transpose]
    exact hp y hy

end Sandpile
