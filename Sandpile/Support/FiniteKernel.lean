/-
Finite-coordinate representations of translated finite kernels, product-law
transport and cubic coefficient overlaps for the cut-off Green field.
-/
import Sandpile.Support.FiniteRange
import Sandpile.Support.FiniteLindeberg
import Sandpile.External.BallGreenBounds
import LatticeProb.Prob.FiniteMarginal

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace Sandpile

lemma killedGreen_eq_zero_of_target_notMem {d : ℕ} (D : Set (Site d)) {y : Site d}
    (hy : y ∉ D) (x : Site d) : killedGreen D x y = 0 := by
  simp only [killedGreen, killedKernel_eq_zero_of_target_notMem D hy, tsum_zero]

lemma sum_abs_translate_cube_le_tsum {d : ℕ} {h : Site d → ℝ}
    (hh : Summable (fun u => |h u| ^ 3)) (s : Finset (Site d)) (z : Site d) :
    ∑ y : s, |h ((y : Site d) - z)| ^ 3 ≤ ∑' u, |h u| ^ 3 := by
  classical
  have hs : Summable (fun y : Site d => |h (y - z)| ^ 3) := hh.comp_injective (Equiv.subRight z).injective
  calc
    _ = ∑ y ∈ s, |h (y - z)| ^ 3 := Finset.sum_coe_sort s (fun y => |h (y - z)| ^ 3)
    _ ≤ ∑' y : Site d, |h (y - z)| ^ 3 := hs.sum_le_tsum s (fun _ _ => by positivity)
    _ = _ := (Equiv.subRight z).tsum_eq (fun u => |h u| ^ 3)

lemma sum_abs_translate_triple_le_cube_bound {d : ℕ} {h : Site d → ℝ}
    (hh : Summable (fun u => |h u| ^ 3)) {Q : ℝ} (hQ : (∑' u, |h u| ^ 3) ≤ Q)
    (s : Finset (Site d)) (z w y : Site d) :
    ∑ i : s, |h ((i : Site d) - z) * h ((i : Site d) - w) * h ((i : Site d) - y)| ≤ Q :=
  sum_abs_triple_le_cube_bound (fun z (i : s) => h ((i : Site d) - z))
    (fun z => (sum_abs_translate_cube_le_tsum hh s z).trans hQ) z w y

def finiteKernelField {d : ℕ} (h : Site d → ℝ) (ζ : Site d → ℝ) (z : Site d) : ℝ :=
  ∑' u : Site d, h u * ζ (z + u)

lemma finiteKernelField_eq_sum {d : ℕ} {h : Site d → ℝ} (s : Finset (Site d))
    (hs : ∀ u ∉ s, h u = 0) (ζ : Site d → ℝ) (z : Site d) :
    finiteKernelField h ζ z = ∑ u ∈ s, h u * ζ (z + u) :=
  tsum_eq_sum (fun u hu => by rw [hs u hu, zero_mul])

lemma finiteKernelField_eq_linearField {d : ℕ} {V : Type*} [Fintype V]
    (h : Site d → ℝ) (z : V → Site d) (s : Finset (Site d))
    (hs : ∀ v y, y ∉ s → h (y - z v) = 0) (ζ : Site d → ℝ) :
    (fun v => finiteKernelField h ζ (z v)) =
      linearField (fun v (i : s) => h ((i : Site d) - z v)) (s.restrict ζ) := by
  classical
  funext v
  calc
    _ = ∑' y : Site d, h (y - z v) * ζ y := by
      have he := (Equiv.subRight (z v)).tsum_eq (fun u => h u * ζ (z v + u))
      simpa only [finiteKernelField, Equiv.subRight_apply, add_sub_cancel] using he.symm
    _ = ∑ y ∈ s, h (y - z v) * ζ y := tsum_eq_sum (fun y hy => by rw [hs v y hy, zero_mul])
    _ = _ := (Finset.sum_coe_sort s (fun y => h (y - z v) * ζ y)).symm

lemma exists_finiteKernelField_coordinates {d : ℕ} {V : Type*} [Fintype V]
    {h : Site d → ℝ} (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (z : V → Site d) :
    ∃ s : Finset (Site d), ∀ v y, y ∉ s → h (y - z v) = 0 := by
  classical
  refine ⟨Finset.univ.biUnion (fun v : V => t.image (fun u => z v + u)), ?_⟩
  intro v y hy
  apply ht
  intro hm
  apply hy
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, Finset.mem_image.mpr
    ⟨y - z v, hm, by abel⟩⟩

lemma measurePreserving_finite_restrict {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset (Site d)) :
    MeasurePreserving s.restrict (LatticeProb.iidLaw d μ) (Measure.pi (fun _ : s => μ)) :=
  ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (i : Site d)), LatticeProb.iidLaw_map_restrict d μ s⟩

lemma finiteKernelField_sublevel_measure {d : ℕ} {V : Type*} [Fintype V]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : Site d → ℝ) (z : V → Site d)
    (s : Finset (Site d)) (hs : ∀ v y, y ∉ s → h (y - z v) = 0)
    (value : (V → ℝ) → ℝ) (hv : Measurable value) (level : ℝ) :
    (LatticeProb.iidLaw d μ).real {ζ | value (fun v => finiteKernelField h ζ (z v)) ≤ level} =
      (Measure.pi (fun _ : s => μ)).real
        {x | value (linearField (fun v (i : s) => h ((i : Site d) - z v)) x) ≤ level} := by
  have hm : MeasurableSet {x | value (linearField (fun v (i : s) => h ((i : Site d) - z v)) x) ≤ level} :=
    measurableSet_le (hv.comp (continuous_linearField _).measurable) measurable_const
  have hh := (measurePreserving_finite_restrict μ s).measure_preimage hm.nullMeasurableSet
  have he : {ζ | value (fun v => finiteKernelField h ζ (z v)) ≤ level} =
      s.restrict ⁻¹' {x | value (linearField (fun v (i : s) => h ((i : Site d) - z v)) x) ≤ level} := by
    ext ζ
    simp only [mem_preimage, mem_setOf_eq, finiteKernelField_eq_linearField h z s hs]
  change ENNReal.toReal _ = ENNReal.toReal _
  rw [he]
  exact congrArg ENNReal.toReal hh

lemma cutField_eq_zero_of_notMem_boxFinset (r L : ℕ) (φ : ℝ → ℝ) {u : Site 4}
    (hu : u ∉ boxFinset 0 r) : External.BallGreen.cutField r L φ u = 0 := by
  have hout : u ∉ External.BallGreen.box r := by
    intro hb
    apply hu
    apply mem_boxFinset
    apply Finset.sup_le
    intro i _
    simpa only [Pi.zero_apply, zero_sub, Int.natAbs_neg] using hb i
  rw [External.BallGreen.cutField, killedGreen_eq_zero_of_target_notMem _ hout, zero_mul]

lemma cutField_nonneg (r L : ℕ) {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) (u : Site 4) :
    0 ≤ External.BallGreen.cutField r L φ u := by
  apply mul_nonneg
  · exact tsum_nonneg (fun n => killedKernel_nonneg _ n _ _)
  · exact (hφ.1 _ (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))).1

lemma summable_abs_cutField_cube (r L : ℕ) (φ : ℝ → ℝ) :
    Summable (fun u => |External.BallGreen.cutField r L φ u| ^ 3) := by
  apply summable_of_ne_finset_zero (s := boxFinset 0 r)
  intro u hu
  simp only [cutField_eq_zero_of_notMem_boxFinset r L φ hu, abs_zero, zero_pow (by decide : 3 ≠ 0)]

lemma cutField_finite_coefficients (hBall : External.BallGreenBounds) :
    ∃ C > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
        (∀ u, |External.BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
        ∀ (s : Finset (Site 4)) (z w y : Site 4),
          ∑ i : s, |External.BallGreen.cutField r L φ ((i : Site 4) - z) *
            External.BallGreen.cutField r L φ ((i : Site 4) - w) *
            External.BallGreen.cutField r L φ ((i : Site 4) - y)| ≤ C / (L : ℝ) ^ 2 := by
  obtain ⟨C, c, hC, _, h⟩ := hBall
  refine ⟨C, hC, ?_⟩
  intro r hr L hL φ hφ
  obtain ⟨ha, hc, _⟩ := (h r hr).2.2.2.2.1 L hL φ hφ
  refine ⟨ha, ?_⟩
  intro s z w y
  apply sum_abs_translate_triple_le_cube_bound (summable_abs_cutField_cube r L φ) _ s z w y
  simpa only [abs_of_nonneg (cutField_nonneg r L hφ _)] using hc

end Sandpile
