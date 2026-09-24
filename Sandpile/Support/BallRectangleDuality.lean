/-
From star crossings in translated four-dimensional rectangles to planar crossing values.
-/
import Sandpile.Support.RectangleIntersection
import Sandpile.Support.NearFarCrossing

noncomputable section
namespace Sandpile

def planeUntranslate (x z : Site 4) : Site 2 := ![z 0 - x 0, z 1 - x 1]

lemma planeUntranslate_planeTranslate (x : Site 4) (u : Site 2) :
    planeUntranslate x (planeTranslate x u) = u := by
  ext i
  fin_cases i <;> simp [planeUntranslate, planeTranslate]

lemma planeUntranslate_mem_rectangle {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4)
    {z : Site 4} (hz : z ∈ ballRect ϑ r x) :
    planeUntranslate x z ∈ planeRectangle ⌊ϑ * r⌋₊ r := by
  rw [ballRect_eq_image_planeRectangle hϑ r x] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  rw [planeUntranslate_planeTranslate]
  exact hu

lemma planeTranslate_planeUntranslate {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4)
    {z : Site 4} (hz : z ∈ ballRect ϑ r x) : planeTranslate x (planeUntranslate x z) = z := by
  rw [ballRect_eq_image_planeRectangle hϑ r x] at hz
  obtain ⟨u, _, rfl⟩ := hz
  rw [planeUntranslate_planeTranslate]

def ballRectanglePoint {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4)
    (z : ballRect ϑ r x) : planeRectangle ⌊ϑ * r⌋₊ r :=
  ⟨planeUntranslate x z, planeUntranslate_mem_rectangle hϑ r x z.property⟩

lemma ballRectanglePoint_translate {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4)
    (z : ballRect ϑ r x) : planeTranslate x (ballRectanglePoint hϑ r x z) = (z : Site 4) :=
  planeTranslate_planeUntranslate hϑ r x z.property

lemma planeUntranslate_star_coord {z w : Site 4} (hzw : starGraph.Adj z w) (x : Site 4) (i : Fin 2) :
    ((planeUntranslate x z) i - (planeUntranslate x w) i).natAbs ≤ 1 := by
  have hcoord (j : Fin 4) : ((z j - x j) - (w j - x j)).natAbs ≤ 1 := by
    rw [show (z j - x j) - (w j - x j) = z j - w j by ring]
    have hh : ((z j - w j).natAbs : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using hzw.2.1 j
    exact_mod_cast hh
  fin_cases i
  · exact hcoord 0
  · exact hcoord 1

def ballRectangleStarHom {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4) :
    starGraph.induce (ballRect ϑ r x) →g
      (starLatticeGraph 2).induce ((planeRectangle ⌊ϑ * r⌋₊ r) : Set (Site 2)) where
  toFun := ballRectanglePoint hϑ r x
  map_rel' := by
    intro z w hzw
    have hh : starGraph.Adj (z : Site 4) (w : Site 4) := hzw
    refine ⟨?_, fun i => planeUntranslate_star_coord hh x i⟩
    intro he
    have he' := congrArg (planeTranslate x) he
    change planeTranslate x (ballRectanglePoint hϑ r x z) = planeTranslate x (ballRectanglePoint hϑ r x w) at he'
    rw [ballRectanglePoint_translate, ballRectanglePoint_translate] at he'
    exact hh.1 he'

lemma crossingValue_le_of_hasStarTopBottomCrossing {ϑ : ℝ} (hϑ : 0 ≤ ϑ)
    (r : ℕ) (x : Site 4) (F : Site 4 → ℝ) {level : ℝ}
    (hc : HasStarTopBottomCrossing ϑ r x {z | F z ≤ level}) :
    crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun z => F (planeTranslate x z)) ≤ level := by
  obtain ⟨Γ, hΓ, hmem, hchain, hhead, hlast⟩ := hc
  let p := SimpleGraph.Walk.ofSupport Γ hΓ hchain
  have hp : p.support = Γ := SimpleGraph.Walk.support_ofSupport hΓ hchain
  have hpR : ∀ z ∈ p.support, z ∈ ballRect ϑ r x := fun z hz => (hmem z (hp ▸ hz)).2
  let p' := p.induce (ballRect ϑ r x) hpR
  let f := ballRectangleStarHom hϑ r x
  let q := p'.map f
  have htop : (Γ.head hΓ) 1 = x 1 + (r : ℤ) :=
    hhead _ (by simp [List.head?_eq_some_head hΓ])
  have hbot : (Γ.getLast hΓ) 1 = x 1 :=
    hlast _ (by simp [List.getLast?_eq_getLast_of_ne_nil hΓ])
  apply crossingValue_le_of_low_star_walk (fun z => F (planeTranslate x z)) q.reverse
  · change (Γ.getLast hΓ) 1 - x 1 = 0
    omega
  · change (Γ.head hΓ) 1 - x 1 = r
    omega
  · intro z hz
    have hz' : z ∈ (p'.map f).support := by simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    rw [SimpleGraph.Walk.support_map] at hz'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz'
    change F (planeTranslate x (ballRectanglePoint hϑ r x y)) ≤ level
    rw [ballRectanglePoint_translate]
    have hymap : (y : Site 4) ∈ (p'.map (SimpleGraph.Embedding.induce (ballRect ϑ r x)).toHom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨y, hy, rfl⟩
    have hyorig : (y : Site 4) ∈ p.support := by
      change (y : Site 4) ∈ ((p.induce (ballRect ϑ r x) hpR).map (SimpleGraph.Embedding.induce (ballRect ϑ r x)).toHom).support at hymap
      rw [SimpleGraph.Walk.map_induce] at hymap
      exact hymap
    exact (hmem y (hp ▸ hyorig)).1

end Sandpile
