/-
Joint near-field bad-box bounds from finite-range independence and
a finite residue coloring of the coarse plane.
-/
import Sandpile.Support.KernelBlocks
import Sandpile.Support.CoarseBox

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

lemma near_boxes_same_color_joint_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) (hL : 0 < L) {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ)
    (x : Site 4) (T : Finset (Site 2)) (c : Fin 2 → Fin 7)
    (hcolor : ∀ a ∈ T, coarsePlaneColor a = c) (level : ℝ) {p : ℝ≥0∞}
    (hp : ∀ a ∈ T, (LatticeProb.iidLaw 4 μ)
      (kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L a) L) level) ≤ p) :
    (LatticeProb.iidLaw 4 μ) {ζ | ∀ a ∈ T,
      ζ ∈ kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L a) L) level} ≤ p ^ T.card := by
  let S (a : T) := planeBox (coarsePlaneCenter x L a) L
  let A (a : T) := boxFinset (coarsePlaneCenter x L a) (3 * L)
  have hdisj : Pairwise (Function.onFun Disjoint (fun a : T => (A a : Set (Site 4)))) := by
    intro a b hab
    exact disjoint_coarsePlane_coordinates x L hL (fun he => hab (Subtype.ext he))
      ((hcolor a a.property).trans (hcolor b b.property).symm)
  have hA : ∀ (a : T) z, z ∈ S a → ∀ y ∉ A a, nearKernel r L φ (y - z) = 0 := by
    intro a z hz y hy
    exact nearKernel_planeBox_coordinates r L hL hφ (coarsePlaneCenter x L a) z hz y hy
  have hh := kernelLowEvent_inter_le_pow μ (nearKernel r L φ) S A hdisj hA level Finset.univ
    (fun a _ => hp a a.property)
  have he : {ζ | ∀ a ∈ T, ζ ∈ kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L a) L) level} =
      {ζ | ∀ a : T, ∀ _ha : a ∈ (Finset.univ : Finset T), ζ ∈ kernelLowEvent (nearKernel r L φ) (S a) level} := by
    ext ζ
    simp only [mem_setOf_eq, Finset.mem_univ, forall_const, Subtype.forall, S]
  rw [he]
  simpa only [Finset.card_univ, Fintype.card_coe] using hh

lemma exists_monochromatic_subset {V C : Type*} [Fintype C] [Nonempty C]
    (color : V → C) (T : Finset V) {m : ℕ} (hsize : Fintype.card C * m ≤ T.card) :
    ∃ c : C, ∃ U : Finset V, U ⊆ T ∧ U.card = m ∧ ∀ a ∈ U, color a = c := by
  classical
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := T) (t := Finset.univ) (f := color) (fun _ _ => Finset.mem_univ _)
    Finset.univ_nonempty (by simpa only [Finset.card_univ] using hsize)
  obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq hc
  exact ⟨c, U, fun a ha => (Finset.mem_filter.mp (hU ha)).1, hcard,
    fun a ha => (Finset.mem_filter.mp (hU ha)).2⟩

lemma near_boxes_joint_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) (hL : 0 < L) {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ)
    (x : Site 4) (T : Finset (Site 2)) (m : ℕ) (hsize : 49 * m ≤ T.card)
    (level : ℝ) {p : ℝ≥0∞}
    (hp : ∀ a ∈ T, (LatticeProb.iidLaw 4 μ)
      (kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L a) L) level) ≤ p) :
    (LatticeProb.iidLaw 4 μ) {ζ | ∀ a ∈ T,
      ζ ∈ kernelLowEvent (nearKernel r L φ) (planeBox (coarsePlaneCenter x L a) L) level} ≤ p ^ m := by
  have hsize' : Fintype.card (Fin 2 → Fin 7) * m ≤ T.card := by simpa using hsize
  obtain ⟨c, U, hUT, hUcard, hcolor⟩ := exists_monochromatic_subset coarsePlaneColor T hsize'
  have hh := near_boxes_same_color_joint_bound μ r L hL hφ x U c hcolor level
    (fun a ha => hp a (hUT ha))
  rw [hUcard] at hh
  exact (measure_mono (fun ζ (hζ : ∀ a ∈ T, ζ ∈ kernelLowEvent (nearKernel r L φ)
    (planeBox (coarsePlaneCenter x L a) L) level) a ha => hζ a (hUT ha))).trans hh

lemma exists_near_many_boxes_bound (hBall : External.BallGreenBounds)
    (θ K η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ α b C : ℝ, 0 < α ∧ α < 1 ∧ 0 < b ∧ 0 < C ∧ ∃ r₀ : ℕ, 2 ≤ r₀ ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
          ∀ (x : Site 4) (m : ℕ) (T : Finset (Site 2)), 49 * m ≤ T.card →
            (LatticeProb.iidLaw 4 μ) {ζ | ∀ a ∈ T,
              ζ ∈ kernelLowEvent (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ)
                (planeBox (coarsePlaneCenter x ⌊(r : ℝ) ^ α⌋₊ a) ⌊(r : ℝ) ^ α⌋₊) (-η * Real.log r)} ≤
              ENNReal.ofReal (C ^ m * (r : ℝ) ^ (-b * (m : ℝ))) := by
  obtain ⟨α, b, C, hα, hα1, hb, hC, r₀, hr₀, hbox⟩ := exists_near_bad_box_bound hBall θ K η hθ hη
  refine ⟨α, b, C, hα, hα1, hb, hC, r₀, hr₀, ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ x m T hsize
  letI : IsProbabilityMeasure μ := hμ
  have hr2 : 2 ≤ r := hr₀.trans hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hpow : 1 ≤ (r : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ r)) hα.le
  have hL : 0 < ⌊(r : ℝ) ^ α⌋₊ := by
    have hh : 1 ≤ ⌊(r : ℝ) ^ α⌋₊ := (Nat.le_floor_iff (Real.rpow_nonneg hrpos.le α)).mpr (by simpa using hpow)
    omega
  have hp (a : Site 2) : (LatticeProb.iidLaw 4 μ)
      (kernelLowEvent (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ)
        (planeBox (coarsePlaneCenter x ⌊(r : ℝ) ^ α⌋₊ a) ⌊(r : ℝ) ^ α⌋₊) (-η * Real.log r)) ≤
      ENNReal.ofReal (C * (r : ℝ) ^ (-b)) :=
    hbox μ hμ hexp hK hmean r hr φ hφ _ (card_planeBox_le _ _)
  have hh := near_boxes_joint_bound μ r ⌊(r : ℝ) ^ α⌋₊ hL hφ x T m hsize (-η * Real.log r) (fun a _ => hp a)
  have he : (ENNReal.ofReal (C * (r : ℝ) ^ (-b))) ^ m =
      ENNReal.ofReal (C ^ m * (r : ℝ) ^ (-b * (m : ℝ))) := by
    rw [← ENNReal.ofReal_pow (by positivity), mul_pow]
    congr 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]
  exact hh.trans_eq he

end Sandpile
