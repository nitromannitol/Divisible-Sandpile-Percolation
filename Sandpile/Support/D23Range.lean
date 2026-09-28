import Sandpile.Support.D23LSS
import Sandpile.Support.D4CritRange

/-!
# Finite dependence range of the dimension-two and dimension-three block process

The finite dependence range of the good-block process of the dimension-two and
dimension-three percolation argument (`sandpile.tex:2585-2590`): the localized
odometer at a plane site reads only the scenery in the box `Q(x,R)` about that
site, so the good block at a coarse site reads only the scenery in one box about
the block, and blocks more than ten apart in the coarse lattice read disjoint
boxes.
-/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

open scoped Classical

variable {d : ℕ}

/-- The anchor of the block at the coarse site `z`, at block scale `R`. -/
def d23Anchor (R : ℕ) (z : Site 2) : Site 2 := ![2 * (R : ℤ) * z 0, 2 * (R : ℤ) * z 1]

/-- The box of scenery sites the good block at the coarse site `z` reads. -/
def d23CritBox (R : ℕ) (z : Site 2) : Set (Site d) :=
  d23Box (5 * R) (planeSite (d := d) (d23Anchor R z))

/-- A site of the block is within `4R` of the block anchor. -/
theorem abs_blockShift_sub_anchor (R : ℕ) (z v : Site 2)
    (hv : v ∈ planeRectangle (4 * R) (4 * R)) (j : Fin 2) :
    |blockShift R z v j - d23Anchor R z j| ≤ 4 * (R : ℤ) := by
  rw [mem_planeRectangle] at hv
  fin_cases j
  · show |v 0 + 2 * (R : ℤ) * z 0 - 2 * (R : ℤ) * z 0| ≤ 4 * (R : ℤ)
    have h1 : v 0 + 2 * (R : ℤ) * z 0 - 2 * (R : ℤ) * z 0 = v 0 := by ring
    rw [h1, abs_le]
    have h2 : v 0 ≤ ((4 * R : ℕ) : ℤ) := hv.2.1
    push_cast at h2
    exact ⟨by linarith [hv.1], by linarith⟩
  · show |v 1 + 2 * (R : ℤ) * z 1 - 2 * (R : ℤ) * z 1| ≤ 4 * (R : ℤ)
    have h1 : v 1 + 2 * (R : ℤ) * z 1 - 2 * (R : ℤ) * z 1 = v 1 := by ring
    rw [h1, abs_le]
    have h2 : v 1 ≤ ((4 * R : ℕ) : ℤ) := hv.2.2.2
    push_cast at h2
    exact ⟨by linarith [hv.2.2.1], by linarith⟩

/-- The localization box of a site of the block sits inside the block box. -/
theorem d23Box_blockShift_subset (R : ℕ) (z : Site 2) {v : Site 2}
    (hv : v ∈ planeRectangle (4 * R) (4 * R)) :
    d23Box R (planeSite (d := d) (blockShift R z v)) ⊆ d23CritBox (d := d) R z := by
  refine d23Box_subset fun i => ?_
  by_cases hi : (i : ℕ) < 2
  · rw [planeSite_apply_lt _ _ hi, planeSite_apply_lt _ _ hi]
    have h := abs_blockShift_sub_anchor R z v hv ⟨(i : ℕ), hi⟩
    push_cast
    linarith
  · rw [planeSite_apply_ge _ _ hi, planeSite_apply_ge _ _ hi]
    push_cast
    simp only [abs_zero]
    have : (0 : ℤ) ≤ (R : ℤ) := Int.natCast_nonneg R
    linarith

/-- Blocks far apart in the coarse lattice read disjoint boxes of the scenery. -/
theorem d23CritBox_disjoint_of_dist (hd2 : 2 ≤ d) (R : ℕ) (hR : 1 ≤ R) (k : ℝ) (hk : 10 ≤ k)
    (z z' : Site 2) (hdist : k < Sandpile.External.latticeDist z z') :
    Disjoint (d23CritBox (d := d) R z) (d23CritBox (d := d) R z') := by
  have hsum := latticeDist_le_sum_coord z z'
  have hks : k < |((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)| :=
    lt_of_lt_of_le hdist hsum
  have hgap : ∃ i : Fin 2, (5 : ℝ) < |((z i - z' i : ℤ) : ℝ)| := by
    rcases le_total |((z 0 - z' 0 : ℤ) : ℝ)| |((z 1 - z' 1 : ℤ) : ℝ)| with hle | hle
    · exact ⟨1, by linarith⟩
    · exact ⟨0, by linarith⟩
  obtain ⟨i, hi⟩ := hgap
  have hiZ : (6 : ℤ) ≤ |z i - z' i| := by
    have h : (5 : ℝ) < ((|z i - z' i| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
      push_cast
      push_cast at hi
      exact hi
    have h' : (5 : ℤ) < |z i - z' i| := by exact_mod_cast h
    omega
  refine d23Box_disjoint ⟨⟨(i : ℕ), by have := i.isLt; omega⟩, ?_⟩
  have hcoord : |planeSite (d := d) (d23Anchor R z) ⟨(i : ℕ), by have := i.isLt; omega⟩
      - planeSite (d := d) (d23Anchor R z') ⟨(i : ℕ), by have := i.isLt; omega⟩|
      = 2 * (R : ℤ) * |z i - z' i| := by
    rw [planeSite_apply_lt _ _ (by have := i.isLt; omega),
      planeSite_apply_lt _ _ (by have := i.isLt; omega)]
    have he : d23Anchor R z ⟨(i : ℕ), by have := i.isLt; omega⟩
        - d23Anchor R z' ⟨(i : ℕ), by have := i.isLt; omega⟩
        = 2 * (R : ℤ) * (z i - z' i) := by
      fin_cases i
      · show 2 * (R : ℤ) * z 0 - 2 * (R : ℤ) * z' 0 = 2 * (R : ℤ) * (z 0 - z' 0)
        ring
      · show 2 * (R : ℤ) * z 1 - 2 * (R : ℤ) * z' 1 = 2 * (R : ℤ) * (z 1 - z' 1)
        ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 2 * (R : ℤ))]
  rw [hcoord]
  have hR' : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  push_cast
  nlinarith [hiZ, hR']

/-- The good block at a coarse site reads only the scenery in its block box. -/
theorem measurableSet_blockGood_comap_d23 (hd : 1 ≤ d) (R t : ℕ) (ℓ : ℝ) (z : Site 2) :
    MeasurableSet[MeasurableSpace.comap
        (fun ζ : Site d → ℝ => Set.restrict (d23CritBox (d := d) R z) ζ) inferInstance]
      {ζ : Site d → ℝ | BlockGood R (d23Field d R t ζ) ℓ z} := by
  set m := MeasurableSpace.comap
    (fun ζ : Site d → ℝ => Set.restrict (d23CritBox (d := d) R z) ζ) inferInstance with hm
  have hfield : ∀ v : Site 2, v ∈ planeRectangle (4 * R) (4 * R) →
      Measurable[m] (fun ζ : Site d → ℝ => d23Field d R t ζ (blockShift R z v)) :=
    fun v hv => (measurable_comap_d23Field hd R t (blockShift R z v)).mono
      (comap_restrict_mono (d23Box_blockShift_subset R z hv)) le_rfl
  have hcross : ∀ (Q : Finset (Site 2)), IsLatticeRectangle Q → Q.Nonempty →
      ∀ g : Q → Site 2, (∀ u : Q, g u ∈ planeRectangle (4 * R) (4 * R)) →
      MeasurableSet[m] {ζ : Site d → ℝ | ℓ ≤ crossingValue Q
        (fun u : Q => d23Field d R t ζ (blockShift R z (g u)))} := by
    intro Q hQ hN g hg
    exact measurableSet_le measurable_const
      ((measurable_crossingValue hQ hN).comp
        (measurable_pi_lambda _ fun u => hfield (g u) (hg u)))
  have h1 := hcross (planeRectangle (2 * R) (2 * R))
    (isLatticeRectangle_planeRectangle (2 * R) (2 * R))
    (planeRectangle_nonempty (2 * R) (2 * R)) (fun u => (u : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega) u.2)
  have h2 := hcross (planeRectangle (2 * R) (2 * R))
    (isLatticeRectangle_planeRectangle (2 * R) (2 * R))
    (planeRectangle_nonempty (2 * R) (2 * R))
    (fun u => ((transposeRectangle (2 * R) (2 * R) u : planeRectangle (2 * R) (2 * R)) : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega)
      (transposeRectangle (2 * R) (2 * R) u).2)
  have h3 := hcross (planeRectangle (4 * R) (2 * R))
    (isLatticeRectangle_planeRectangle (4 * R) (2 * R))
    (planeRectangle_nonempty (4 * R) (2 * R)) (fun u => (u : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega) u.2)
  have h4 := hcross (planeRectangle (4 * R) (2 * R))
    (isLatticeRectangle_planeRectangle (4 * R) (2 * R))
    (planeRectangle_nonempty (4 * R) (2 * R))
    (fun u => ((transposeRectangle (4 * R) (2 * R) u : planeRectangle (2 * R) (4 * R)) : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega)
      (transposeRectangle (4 * R) (2 * R) u).2)
  exact h1.inter (h2.inter (h3.inter h4))

/-- Finite-range dependence of the good-block process: blocks more than ten
apart in the coarse lattice generate independent sigma-algebras. -/
theorem indep_blockGood_d23_of_dist (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (hd2 : 2 ≤ d) (R t : ℕ) (hR : 1 ≤ R) (ℓ k : ℝ) (hk : 10 ≤ k)
    (S W : Set (Site 2)) (hdist : ∀ s ∈ S, ∀ w ∈ W, k < Sandpile.External.latticeDist s w) :
    Indep
      (MeasurableSpace.generateFrom (S.image fun s => {ζ : Site d → ℝ |
        decide (BlockGood R (d23Field d R t ζ) ℓ s) = true}))
      (MeasurableSpace.generateFrom (W.image fun w => {ζ : Site d → ℝ |
        decide (BlockGood R (d23Field d R t ζ) ℓ w) = true}))
      (LatticeProb.iidLaw d ν) := by
  classical
  set US : Set (Site d) := ⋃ s ∈ S, d23CritBox (d := d) R s with hUS
  set UT : Set (Site d) := ⋃ w ∈ W, d23CritBox (d := d) R w with hUT
  have hdisj : Disjoint US UT := by
    rw [Set.disjoint_left]
    intro y hy hy'
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.mp hy
    obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.mp hy'
    exact Set.disjoint_left.mp
      (d23CritBox_disjoint_of_dist hd2 R hR k hk s w (hdist s hs w hw)) hys hyw
  set A : Bool → Set (Site d) := fun b => if b then US else UT with hA
  have hApair : Pairwise (Function.onFun Disjoint A) := by
    intro a b hab
    match a, b with
    | true, false => exact hdisj
    | false, true => exact hdisj.symm
    | true, true => exact absurd rfl hab
    | false, false => exact absurd rfl hab
  have hind := (LatticeProb.iIndep_comap_of_pairwise_disjoint ν A hApair).indep
    (show (true : Bool) ≠ false by decide)
  refine indep_of_indep_of_le hind ?_ ?_
  · refine MeasurableSpace.generateFrom_le ?_
    rintro E ⟨s, hs, rfl⟩
    have hset : (fun s => {ζ : Site d → ℝ |
        decide (BlockGood R (d23Field d R t ζ) ℓ s) = true}) s
        = {ζ : Site d → ℝ | BlockGood R (d23Field d R t ζ) ℓ s} := by
      ext ζ; simp
    rw [hset]
    refine comap_restrict_mono (A := A true) ?_ _
      (measurableSet_blockGood_comap_d23 hd R t ℓ s)
    exact fun y hy => Set.mem_biUnion hs hy
  · refine MeasurableSpace.generateFrom_le ?_
    rintro E ⟨w, hw, rfl⟩
    have hset : (fun w => {ζ : Site d → ℝ |
        decide (BlockGood R (d23Field d R t ζ) ℓ w) = true}) w
        = {ζ : Site d → ℝ | BlockGood R (d23Field d R t ζ) ℓ w} := by
      ext ζ; simp
    rw [hset]
    refine comap_restrict_mono (A := A false) ?_ _
      (measurableSet_blockGood_comap_d23 hd R t ℓ w)
    exact fun y hy => Set.mem_biUnion hw hy

end Sandpile
