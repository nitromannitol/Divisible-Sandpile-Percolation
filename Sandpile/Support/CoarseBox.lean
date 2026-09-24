/-
Closed planar coarse boxes, finite-range scenery regions and their
separation under a finite residue coloring.
-/
import Sandpile.Support.NearBox

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace Sandpile

def planeBox (x : Site 4) (L : ℕ) : Finset (Site 4) :=
  (planeRectangle L L).image (planeTranslate x)

lemma card_planeBox_le (x : Site 4) (L : ℕ) : (planeBox x L).card ≤ (L + 1) ^ 2 := by
  calc
    _ ≤ (planeRectangle L L).card := Finset.card_image_le
    _ = _ := by rw [card_planeRectangle]; ring

lemma planeBox_subset_boxFinset (x : Site 4) (L : ℕ) : planeBox x L ⊆ boxFinset x L := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hu0, huL0, hu1, huL1⟩ := (mem_planeRectangle L L u).mp hu
  have h0 : |(u 0 : ℝ)| ≤ L := by
    rw [abs_of_nonneg (by exact_mod_cast hu0)]
    exact_mod_cast huL0
  have h1 : |(u 1 : ℝ)| ≤ L := by
    rw [abs_of_nonneg (by exact_mod_cast hu1)]
    exact_mod_cast huL1
  apply mem_boxFinset
  apply (boxDist_le_iff_real_coords x _ L).mpr
  intro i
  fin_cases i
  · simpa [planeTranslate] using h0
  · simpa [planeTranslate] using h1
  · simp [planeTranslate]
  · simp [planeTranslate]

lemma boxDist_zero_sub {d : ℕ} (y z : Site d) : boxDist 0 (y - z) = boxDist z y := by
  unfold boxDist
  congr 1
  funext i
  simp

lemma nearKernel_planeBox_coordinates (r L : ℕ) (hL : 0 < L)
    {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) (x : Site 4)
    (z : Site 4) (hz : z ∈ planeBox x L) (y : Site 4) (hy : y ∉ boxFinset x (3 * L)) :
    nearKernel r L φ (y - z) = 0 := by
  apply nearKernel_eq_zero_of_notMem_near_box r L hL hφ
  intro hnear
  apply hy
  have hxz : boxDist x z ≤ L := mem_boxFinset_iff.mp (planeBox_subset_boxFinset x L hz)
  have hzy : boxDist z y ≤ 2 * L := by
    rw [← boxDist_zero_sub]
    exact mem_boxFinset_iff.mp hnear
  exact mem_boxFinset ((boxDist_trans x z y).trans (by omega))

def coarsePlaneCenter (x : Site 4) (L : ℕ) (a : Site 2) : Site 4 :=
  planeTranslate x (fun i => (L : ℤ) * a i)

lemma coarsePlaneCenter_coord (x : Site 4) (L : ℕ) (a : Site 2) (i : Fin 2) :
    coarsePlaneCenter x L a (Fin.castLE (by decide : 2 ≤ 4) i) =
      x (Fin.castLE (by decide : 2 ≤ 4) i) + (L : ℤ) * a i := by
  fin_cases i <;> simp [coarsePlaneCenter, planeTranslate]

def coarsePlaneColor (a : Site 2) : Fin 2 → Fin 7 :=
  fun i => ⟨(a i % 7).toNat, by omega⟩

lemma coarsePlaneColor_separation {a b : Site 2} (hne : a ≠ b)
    (hc : coarsePlaneColor a = coarsePlaneColor b) : ∃ i : Fin 2, 7 ≤ |a i - b i| := by
  have hi : ∃ i, a i ≠ b i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hi
  have he := congrArg (fun f : Fin 2 → Fin 7 => (f i).val) hc
  dsimp [coarsePlaneColor] at he
  have he' : a i % 7 = b i % 7 := by omega
  refine ⟨i, ?_⟩
  rcases le_total (a i) (b i) with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    omega
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    omega

lemma disjoint_coarsePlane_coordinates (x : Site 4) (L : ℕ) (hL : 0 < L)
    {a b : Site 2} (hne : a ≠ b) (hc : coarsePlaneColor a = coarsePlaneColor b) :
    Disjoint (boxFinset (coarsePlaneCenter x L a) (3 * L) : Set (Site 4))
      (boxFinset (coarsePlaneCenter x L b) (3 * L) : Set (Site 4)) := by
  obtain ⟨i, hi⟩ := coarsePlaneColor_separation hne hc
  apply Set.disjoint_left.mpr
  intro y hya hyb
  let j := Fin.castLE (by decide : 2 ≤ 4) i
  have hA := (boxDist_le_iff_real_coords (coarsePlaneCenter x L a) y (3 * L)).mp
    (mem_boxFinset_iff.mp hya) j
  have hB := (boxDist_le_iff_real_coords (coarsePlaneCenter x L b) y (3 * L)).mp
    (mem_boxFinset_iff.mp hyb) j
  have hdist : |((coarsePlaneCenter x L a j : ℝ) - (coarsePlaneCenter x L b j : ℝ))| ≤ 6 * (L : ℝ) := by
    have hh := abs_sub_le (coarsePlaneCenter x L a j : ℝ) (y j : ℝ) (coarsePlaneCenter x L b j : ℝ)
    rw [abs_sub_comm (coarsePlaneCenter x L a j : ℝ) (y j : ℝ)] at hh
    push_cast at hA hB
    linarith
  have he : |((coarsePlaneCenter x L a j : ℝ) - (coarsePlaneCenter x L b j : ℝ))| =
      (L : ℝ) * |((a i : ℝ) - (b i : ℝ))| := by
    rw [coarsePlaneCenter_coord, coarsePlaneCenter_coord]
    push_cast
    rw [show (x j : ℝ) + (L : ℝ) * (a i : ℝ) - ((x j : ℝ) + (L : ℝ) * (b i : ℝ)) =
      (L : ℝ) * ((a i : ℝ) - (b i : ℝ)) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
  have hgap : (7 : ℝ) ≤ |((a i : ℝ) - (b i : ℝ))| := by exact_mod_cast hi
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [he] at hdist
  nlinarith [mul_le_mul_of_nonneg_left hgap hLpos.le]

end Sandpile
