/-
The finite dependence range of the good-block process of the dimension-four
percolation argument (`sandpile.tex:3989-3995`): by
`lem:d4-finite-range-lower-bound` the block field at a site is measurable with
respect to the scenery in a box of radius proportional to `r` about that site,
so the good block at a coarse site reads only the scenery in one box about the
block, and blocks far apart in the coarse lattice read disjoint boxes.
-/
import Sandpile.Support.D4CritLSS
import LatticeProb.Prob.Blocks

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

open scoped Classical

/-- Reading a smaller block of coordinates is measurable for the larger block. -/
theorem comap_restrict_mono {d : ℕ} {B A : Set (Site d)} (h : B ⊆ A) :
    MeasurableSpace.comap (fun ζ : Site d → ℝ => Set.restrict B ζ) inferInstance
      ≤ MeasurableSpace.comap (fun ζ : Site d → ℝ => Set.restrict A ζ) inferInstance := by
  rintro s ⟨t, ht, rfl⟩
  exact ⟨(fun ρ : A → ℝ => fun i : B => ρ ⟨(i : Site d), h i.2⟩) ⁻¹' t,
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) ht, rfl⟩

/-- A cube sits inside a larger cube about a nearby centre. -/
theorem frCube_subset {x y : Site 4} {L M : ℝ}
    (h : ∀ i : Fin 4, |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| + L ≤ M) :
    frCube x L ⊆ frCube y M := by
  intro w hw i
  have h1 : |((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| ≤ L := hw i
  have h2 := h i
  have h3 : |((w i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)|
      ≤ |((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ)| + |((x i : ℤ) : ℝ) - ((y i : ℤ) : ℝ)| :=
    abs_sub_le _ _ _
  linarith

/-- The box of scenery sites the good block at the coarse site `z` reads. -/
def critBox (Aloc : ℝ) (R r : ℕ) (z : Site 2) : Set (Site 4) :=
  frCube (planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1])
    ((Aloc + 3) * R + 4 * r)

/-- The localization box of a site of the block sits inside the block box. -/
theorem frCube_blockShift_subset (Aloc : ℝ) (R r : ℕ) (z : Site 2)
    {v : Site 2} (hv : v ∈ planeRectangle (4 * r) (4 * r)) :
    frCube (planeEmbed (blockShift r z v)) ((Aloc + 3) * R) ⊆ critBox Aloc R r z := by
  rw [mem_planeRectangle] at hv
  refine frCube_subset fun i => ?_
  have hb : |((planeEmbed (blockShift r z v) i : ℤ) : ℝ)
      - ((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] i : ℤ) : ℝ)| ≤ 4 * r := by
    have h0 : (0 : ℝ) ≤ 4 * (r : ℝ) := by positivity
    fin_cases i
    · show |((v 0 + 2 * (r : ℤ) * z 0 : ℤ) : ℝ) - ((2 * (r : ℤ) * z 0 : ℤ) : ℝ)| ≤ 4 * r
      have h1 : ((v 0 + 2 * (r : ℤ) * z 0 : ℤ) : ℝ) - ((2 * (r : ℤ) * z 0 : ℤ) : ℝ)
          = ((v 0 : ℤ) : ℝ) := by push_cast; ring
      rw [h1, abs_le]
      constructor
      · have : (0 : ℝ) ≤ ((v 0 : ℤ) : ℝ) := by exact_mod_cast hv.1
        linarith
      · have : ((v 0 : ℤ) : ℝ) ≤ ((4 * r : ℕ) : ℝ) := by exact_mod_cast hv.2.1
        push_cast at this
        linarith
    · show |((v 1 + 2 * (r : ℤ) * z 1 : ℤ) : ℝ) - ((2 * (r : ℤ) * z 1 : ℤ) : ℝ)| ≤ 4 * r
      have h1 : ((v 1 + 2 * (r : ℤ) * z 1 : ℤ) : ℝ) - ((2 * (r : ℤ) * z 1 : ℤ) : ℝ)
          = ((v 1 : ℤ) : ℝ) := by push_cast; ring
      rw [h1, abs_le]
      constructor
      · have : (0 : ℝ) ≤ ((v 1 : ℤ) : ℝ) := by exact_mod_cast hv.2.2.1
        linarith
      · have : ((v 1 : ℤ) : ℝ) ≤ ((4 * r : ℕ) : ℝ) := by exact_mod_cast hv.2.2.2
        push_cast at this
        linarith
    · show |((0 : ℤ) : ℝ) - ((0 : ℤ) : ℝ)| ≤ 4 * r
      simp
    · show |((0 : ℤ) : ℝ) - ((0 : ℤ) : ℝ)| ≤ 4 * r
      simp
  linarith [hb]

/-- Two block boxes with a large coordinate gap between their centres are
disjoint. -/
theorem critBox_disjoint (Aloc : ℝ) (R r : ℕ) (z z' : Site 2)
    (h : ∃ j : Fin 4, 2 * ((Aloc + 3) * R + 4 * r)
      < |((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] j : ℤ) : ℝ)
        - ((planeEmbed ![2 * (r : ℤ) * z' 0, 2 * (r : ℤ) * z' 1] j : ℤ) : ℝ)|) :
    Disjoint (critBox Aloc R r z) (critBox Aloc R r z') := by
  obtain ⟨j, hj⟩ := h
  rw [Set.disjoint_left]
  intro w hw hw'
  have h1 : |((w j : ℤ) : ℝ)
      - ((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] j : ℤ) : ℝ)|
      ≤ (Aloc + 3) * R + 4 * r := hw j
  have h2 : |((w j : ℤ) : ℝ)
      - ((planeEmbed ![2 * (r : ℤ) * z' 0, 2 * (r : ℤ) * z' 1] j : ℤ) : ℝ)|
      ≤ (Aloc + 3) * R + 4 * r := hw' j
  have h3 : |((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] j : ℤ) : ℝ)
      - ((planeEmbed ![2 * (r : ℤ) * z' 0, 2 * (r : ℤ) * z' 1] j : ℤ) : ℝ)|
      ≤ |((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] j : ℤ) : ℝ) - ((w j : ℤ) : ℝ)|
        + |((w j : ℤ) : ℝ)
          - ((planeEmbed ![2 * (r : ℤ) * z' 0, 2 * (r : ℤ) * z' 1] j : ℤ) : ℝ)| :=
    abs_sub_le _ _ _
  rw [abs_sub_comm] at h1
  linarith

/-- The Euclidean distance in the plane is at most the sum of the coordinate
gaps. -/
theorem latticeDist_le_sum_coord (z z' : Site 2) :
    Sandpile.External.latticeDist z z'
      ≤ |((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)| := by
  unfold Sandpile.External.latticeDist
  rw [Fin.sum_univ_two]
  have ha := abs_nonneg ((z 0 - z' 0 : ℤ) : ℝ)
  have hb := abs_nonneg ((z 1 - z' 1 : ℤ) : ℝ)
  have h : ((z 0 - z' 0 : ℤ) : ℝ) ^ 2 + ((z 1 - z' 1 : ℤ) : ℝ) ^ 2
      ≤ (|((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)|) ^ 2 := by
    nlinarith [sq_abs ((z 0 - z' 0 : ℤ) : ℝ), sq_abs ((z 1 - z' 1 : ℤ) : ℝ),
      mul_nonneg ha hb]
  calc Real.sqrt (((z 0 - z' 0 : ℤ) : ℝ) ^ 2 + ((z 1 - z' 1 : ℤ) : ℝ) ^ 2)
      ≤ Real.sqrt ((|((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)|) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = |((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)| :=
        Real.sqrt_sq (by positivity)

/-- Blocks far apart in the coarse lattice read disjoint boxes of the scenery. -/
theorem critBox_disjoint_of_dist (Aloc : ℝ) (r : ℕ) (hr : 1 ≤ r)
    (k : ℝ) (hk : 4 * Aloc + 20 ≤ k) (z z' : Site 2)
    (hd : k < Sandpile.External.latticeDist z z') :
    Disjoint (critBox Aloc (2 * r) r z) (critBox Aloc (2 * r) r z') := by
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hsum := latticeDist_le_sum_coord z z'
  have hks : k < |((z 0 - z' 0 : ℤ) : ℝ)| + |((z 1 - z' 1 : ℤ) : ℝ)| := lt_of_lt_of_le hd hsum
  have hgap : ∃ i : Fin 2, k / 2 < |((z i - z' i : ℤ) : ℝ)| := by
    rcases le_total |((z 0 - z' 0 : ℤ) : ℝ)| |((z 1 - z' 1 : ℤ) : ℝ)| with hle | hle
    · exact ⟨1, by linarith⟩
    · exact ⟨0, by linarith⟩
  obtain ⟨i, hi⟩ := hgap
  refine critBox_disjoint Aloc (2 * r) r z z' ⟨⟨(i : ℕ), by have := i.isLt; omega⟩, ?_⟩
  have hcoord : |((planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1]
        (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin 4) : ℤ) : ℝ)
      - ((planeEmbed ![2 * (r : ℤ) * z' 0, 2 * (r : ℤ) * z' 1]
        (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin 4) : ℤ) : ℝ)|
      = 2 * (r : ℝ) * |((z i - z' i : ℤ) : ℝ)| := by
    fin_cases i
    · show |((2 * (r : ℤ) * z 0 : ℤ) : ℝ) - ((2 * (r : ℤ) * z' 0 : ℤ) : ℝ)|
        = 2 * (r : ℝ) * |((z 0 - z' 0 : ℤ) : ℝ)|
      have he : ((2 * (r : ℤ) * z 0 : ℤ) : ℝ) - ((2 * (r : ℤ) * z' 0 : ℤ) : ℝ)
          = 2 * (r : ℝ) * ((z 0 - z' 0 : ℤ) : ℝ) := by push_cast; ring
      rw [he, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (r : ℝ))]
    · show |((2 * (r : ℤ) * z 1 : ℤ) : ℝ) - ((2 * (r : ℤ) * z' 1 : ℤ) : ℝ)|
        = 2 * (r : ℝ) * |((z 1 - z' 1 : ℤ) : ℝ)|
      have he : ((2 * (r : ℤ) * z 1 : ℤ) : ℝ) - ((2 * (r : ℤ) * z' 1 : ℤ) : ℝ)
          = 2 * (r : ℝ) * ((z 1 - z' 1 : ℤ) : ℝ) := by push_cast; ring
      rw [he, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (r : ℝ))]
  rw [hcoord]
  have hRcast : (((2 * r : ℕ)) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
  rw [hRcast]
  nlinarith [hi, hr0, hk]

/-- The good block at a coarse site reads only the scenery in its block box. -/
theorem measurableSet_blockGood_comap (Aex : ℕ) (Aloc : ℝ) (R r : ℕ) (ℓ : ℝ) (z : Site 2)
    (hmeas : ∀ x : Site 4,
      Measurable[MeasurableSpace.comap
        (fun ζ : Site 4 → ℝ => Set.restrict (frCube x ((Aloc + 3) * R)) ζ) inferInstance]
        (fun ζ : Site 4 → ℝ =>
          frGreenFieldTime R (Aex * R ^ 2) ζ x + frExitValue Aex Aloc R ζ x)) :
    MeasurableSet[MeasurableSpace.comap
        (fun ζ : Site 4 → ℝ => Set.restrict (critBox Aloc R r z) ζ) inferInstance]
      {ζ : Site 4 → ℝ | BlockGood r (frBlockField Aex Aloc R ζ) ℓ z} := by
  set m := MeasurableSpace.comap
    (fun ζ : Site 4 → ℝ => Set.restrict (critBox Aloc R r z) ζ) inferInstance with hm
  have hfield : ∀ v : Site 2, v ∈ planeRectangle (4 * r) (4 * r) →
      Measurable[m] (fun ζ : Site 4 → ℝ => frBlockField Aex Aloc R ζ (blockShift r z v)) :=
    fun v hv => (hmeas (planeEmbed (blockShift r z v))).mono
      (comap_restrict_mono (frCube_blockShift_subset Aloc R r z hv)) le_rfl
  have hcross : ∀ (Q : Finset (Site 2)) (hQ : IsLatticeRectangle Q) (hN : Q.Nonempty)
      (g : Q → Site 2), (∀ u : Q, g u ∈ planeRectangle (4 * r) (4 * r)) →
      MeasurableSet[m] {ζ : Site 4 → ℝ | ℓ ≤ crossingValue Q
        (fun u : Q => frBlockField Aex Aloc R ζ (blockShift r z (g u)))} := by
    intro Q hQ hN g hg
    exact measurableSet_le measurable_const
      ((measurable_crossingValue hQ hN).comp
        (measurable_pi_lambda _ fun u => hfield (g u) (hg u)))
  have h1 := hcross (planeRectangle (2 * r) (2 * r))
    (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
    (planeRectangle_nonempty (2 * r) (2 * r)) (fun u => (u : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega) u.2)
  have h2 := hcross (planeRectangle (2 * r) (2 * r))
    (isLatticeRectangle_planeRectangle (2 * r) (2 * r))
    (planeRectangle_nonempty (2 * r) (2 * r))
    (fun u => ((transposeRectangle (2 * r) (2 * r) u : planeRectangle (2 * r) (2 * r)) : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega)
      (transposeRectangle (2 * r) (2 * r) u).2)
  have h3 := hcross (planeRectangle (4 * r) (2 * r))
    (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
    (planeRectangle_nonempty (4 * r) (2 * r)) (fun u => (u : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega) u.2)
  have h4 := hcross (planeRectangle (4 * r) (2 * r))
    (isLatticeRectangle_planeRectangle (4 * r) (2 * r))
    (planeRectangle_nonempty (4 * r) (2 * r))
    (fun u => ((transposeRectangle (4 * r) (2 * r) u : planeRectangle (2 * r) (4 * r)) : Site 2))
    (fun u => planeRectangle_subset (by omega) (by omega)
      (transposeRectangle (4 * r) (2 * r) u).2)
  exact h1.inter (h2.inter (h3.inter h4))

/-- Finite-range dependence of the good-block process: blocks far apart in the
coarse lattice generate independent sigma-algebras. -/
theorem indep_blockGood_of_dist (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (hr : 1 ≤ r) (ℓ k : ℝ) (hk : 4 * Aloc + 20 ≤ k)
    (hmeas : ∀ x : Site 4,
      Measurable[MeasurableSpace.comap
        (fun ζ : Site 4 → ℝ => Set.restrict (frCube x ((Aloc + 3) * ((2 * r : ℕ) : ℝ))) ζ)
        inferInstance]
        (fun ζ : Site 4 → ℝ =>
          frGreenFieldTime (2 * r) (Aex * (2 * r) ^ 2) ζ x
            + frExitValue Aex Aloc (2 * r) ζ x))
    (S T : Set (Site 2)) (hdist : ∀ s ∈ S, ∀ t ∈ T, k < Sandpile.External.latticeDist s t) :
    Indep
      (MeasurableSpace.generateFrom (S.image fun s => {ζ : Site 4 → ℝ |
        decide (BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ s) = true}))
      (MeasurableSpace.generateFrom (T.image fun t => {ζ : Site 4 → ℝ |
        decide (BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ t) = true}))
      (LatticeProb.iidLaw 4 ν) := by
  classical
  set US : Set (Site 4) := ⋃ s ∈ S, critBox Aloc (2 * r) r s with hUS
  set UT : Set (Site 4) := ⋃ t ∈ T, critBox Aloc (2 * r) r t with hUT
  have hdisj : Disjoint US UT := by
    rw [Set.disjoint_left]
    intro w hw hw'
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp hw'
    exact Set.disjoint_left.mp
      (critBox_disjoint_of_dist Aloc r hr k hk s t (hdist s hs t ht)) hws hwt
  set A : Bool → Set (Site 4) := fun b => if b then US else UT with hA
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
    have hset : (fun s => {ζ : Site 4 → ℝ |
        decide (BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ s) = true}) s
        = {ζ : Site 4 → ℝ | BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ s} := by
      ext ζ; simp
    rw [hset]
    refine comap_restrict_mono (A := A true) ?_ _
      (measurableSet_blockGood_comap Aex Aloc (2 * r) r ℓ s hmeas)
    exact fun w hw => Set.mem_biUnion hs hw
  · refine MeasurableSpace.generateFrom_le ?_
    rintro E ⟨t, ht, rfl⟩
    have hset : (fun t => {ζ : Site 4 → ℝ |
        decide (BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ t) = true}) t
        = {ζ : Site 4 → ℝ | BlockGood r (frBlockField Aex Aloc (2 * r) ζ) ℓ t} := by
      ext ζ; simp
    rw [hset]
    refine comap_restrict_mono (A := A false) ?_ _
      (measurableSet_blockGood_comap Aex Aloc (2 * r) r ℓ t hmeas)
    exact fun w hw => Set.mem_biUnion ht hw

end Sandpile
