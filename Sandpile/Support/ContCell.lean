/-
The cells of the mesh `R^{-1}ℤ^d` and the lattice pairing
`f^{(R)}(φ) = ∫ f(⌊Rz⌋)φ(z)dz` written over them.

The piecewise-constant embedding `f^{(R)}(z) = f(⌊Rz⌋)` of `ssec:notation` is
constant on each cell `{z : ⌊Rz⌋ = x}`, so pairing it with a test function is a
sum over the sites of `f(x)` against the mass the test function puts on the cell
above `x`.  That mass is `cellMass R φ x`; each cell has volume `R^{-d}`, so the
mass is at most `R^{-d}` times the supremum of `|φ|`, and the masses of finitely
many distinct sites sum in absolute value to at most `∫|φ|`.

This is the representation
`\mathcal F_R(\varphi)=\sum_{z\in\Z^d}a_R(z)\zeta(z)` of the proof of
`prop:weighted-membrane-limit` (`sandpile.tex:4717-4723`): applied to a field of
the form `f(x) = ∑_z w(x,z)ζ(z)` it turns the pairing into a finite linear
functional of the scenery with coefficients `a_R(z) = ∑_x w(x,z) cellMass R φ x`,
which is the form the Lindeberg-Feller theorem needs.
-/
import Sandpile.Continuum.Sobolev
import Sandpile.Support.Kernel

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The cell of the mesh `R^{-1}ℤ^d` above the site `x`: the points of `ℝ^d`
whose piecewise-constant embedding is `x`. -/
def cell (d : ℕ) (R : ℝ) (x : Sandpile.Site d) : Set (Space d) :=
  {z : Space d | ∀ i, ⌊R * z i⌋ = x i}

theorem mem_cell_iff {R : ℝ} {x : Sandpile.Site d} {z : Space d} :
    z ∈ cell d R x ↔ ∀ i, ⌊R * z i⌋ = x i := Iff.rfl

/-- Every point lies in the cell above its own embedded site. -/
theorem mem_cell_self (R : ℝ) (z : Space d) : z ∈ cell d R (fun i => ⌊R * z i⌋) :=
  fun _ => rfl

/-- Distinct sites have disjoint cells. -/
theorem cell_disjoint {R : ℝ} {x y : Sandpile.Site d} (hxy : x ≠ y) :
    Disjoint (cell d R x) (cell d R y) := by
  refine Set.disjoint_left.mpr fun z hzx hzy => hxy (funext fun i => ?_)
  rw [← hzx i, hzy i]

theorem measurable_coord (R : ℝ) (i : Fin d) :
    Measurable (fun z : Space d => ⌊R * z i⌋) :=
  Int.measurable_floor.comp
    (((measurable_pi_apply i).comp (PiLp.volume_preserving_ofLp (Fin d)).measurable).const_mul R)

theorem measurableSet_cell (d : ℕ) (R : ℝ) (x : Sandpile.Site d) :
    MeasurableSet (cell d R x) := by
  have : cell d R x = ⋂ i : Fin d, {z : Space d | ⌊R * z i⌋ = x i} := by
    ext z; simp [cell, Set.mem_iInter]
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_coord R i (measurableSet_singleton (x i))

/-- The cell of the mesh, read in the product coordinates, is a product of
half-open intervals. -/
theorem cell_eq_pi (d : ℕ) {R : ℝ} (hR : 0 < R) (x : Sandpile.Site d) :
    {y : Fin d → ℝ | ∀ i, ⌊R * y i⌋ = x i}
      = Set.pi Set.univ (fun i => Set.Ico ((x i : ℝ) / R) (((x i : ℝ) + 1) / R)) := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ico]
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(div_le_iff₀ hR).mpr ?_, (lt_div_iff₀ hR).mpr ?_⟩
    · rw [mul_comm]; exact h1
    · rw [mul_comm]; exact h2
  · rintro ⟨h1, h2⟩
    have h1' := (div_le_iff₀ hR).mp h1
    have h2' := (lt_div_iff₀ hR).mp h2
    rw [mul_comm] at h1' h2'
    exact ⟨h1', h2'⟩

/-- The volume of a cell of the mesh `R^{-1}ℤ^d` is `R^{-d}`. -/
theorem volume_cell (d : ℕ) {R : ℝ} (hR : 0 < R) (x : Sandpile.Site d) :
    volume (cell d R x) = ENNReal.ofReal R⁻¹ ^ d := by
  have hmeas : MeasurableSet {y : Fin d → ℝ | ∀ i, ⌊R * y i⌋ = x i} := by
    have h : {y : Fin d → ℝ | ∀ i, ⌊R * y i⌋ = x i}
        = ⋂ i : Fin d, {y : Fin d → ℝ | ⌊R * y i⌋ = x i} := by
      ext y; simp [Set.mem_iInter]
    rw [h]
    have hm : ∀ i : Fin d, Measurable (fun y : Fin d → ℝ => ⌊R * y i⌋) := fun i =>
      Int.measurable_floor.comp
        ((measurable_pi_apply (X := fun _ : Fin d => ℝ) i).const_mul R)
    exact MeasurableSet.iInter fun i => hm i (measurableSet_singleton (x i))
  have hpre : cell d R x
      = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' {y : Fin d → ℝ | ∀ i, ⌊R * y i⌋ = x i} := rfl
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hmeas.nullMeasurableSet,
    cell_eq_pi d hR x, volume_pi_pi]
  have h : ∀ i : Fin d, (volume : Measure ℝ) (Set.Ico ((x i : ℝ) / R) (((x i : ℝ) + 1) / R))
      = ENNReal.ofReal R⁻¹ := by
    intro i
    rw [Real.volume_Ico]
    congr 1
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A test function is bounded, supported in a ball, and integrable. -/
theorem exists_bound_of_isTestFn {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ (∀ z, |φ z| ≤ C) ∧
      (∀ z, φ z ≠ 0 → ‖z‖ ≤ L) ∧ Integrable φ := by
  obtain ⟨hsmooth, hcs, -⟩ := hφ
  have hcont : Continuous φ := hsmooth.continuous
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
  obtain ⟨L, hL⟩ := (IsCompact.isBounded hcs).subset_closedBall 0
  refine ⟨max C 0, max L 0, le_max_right _ _, le_max_right _ _, ?_, ?_,
    hcont.integrable_of_hasCompactSupport hcs⟩
  · intro z
    have h := hC z
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  · intro z hz
    have hmem : z ∈ tsupport φ := subset_tsupport φ hz
    have h := hL hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact le_trans h (le_max_left _ _)

/-- Every coordinate of a point of `ℝ^d` is bounded by its Euclidean norm. -/
theorem abs_coord_le_norm (z : Space d) (i : Fin d) : |z i| ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : |z i| = Real.sqrt (‖z i‖ ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_abs]
  rw [h]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j : Fin d => ‖z j‖ ^ 2)
    (fun j _ => sq_nonneg (‖z j‖)) (Finset.mem_univ i)

/-- A point of the ball of radius `L` embeds into the box of radius
`⌈RL⌉ + 1`, so a test function supported in that ball meets only the cells above
that box. -/
theorem floor_mem_boxFinset (R : ℝ) {L : ℝ} (z : Space d) (hz : ‖z‖ ≤ L) :
    (fun i => ⌊R * z i⌋) ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * L⌉₊ + 1) := by
  refine Sandpile.mem_boxFinset ?_
  show Finset.univ.sup (fun i => ((0 : Sandpile.Site d) i - ⌊R * z i⌋).natAbs) ≤ _
  refine Finset.sup_le fun i _ => ?_
  have hzi : |z i| ≤ L := le_trans (abs_coord_le_norm z i) hz
  have hb : |R * z i| ≤ |R| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hzi (abs_nonneg R)
  have hceil : |R| * L ≤ (⌈|R| * L⌉₊ : ℝ) := Nat.le_ceil _
  have hup : (⌊R * z i⌋ : ℝ) ≤ (⌈|R| * L⌉₊ : ℝ) + 1 := by
    have h1 := Int.floor_le (R * z i)
    have h2 : R * z i ≤ |R| * L := le_trans (le_abs_self _) hb
    linarith
  have hlo : -((⌈|R| * L⌉₊ : ℝ) + 1) ≤ (⌊R * z i⌋ : ℝ) := by
    have h1 := Int.sub_one_lt_floor (R * z i)
    have h2 : -(|R| * L) ≤ R * z i := neg_le_of_abs_le hb
    linarith
  have hup' : ⌊R * z i⌋ ≤ ((⌈|R| * L⌉₊ : ℤ) + 1) := by exact_mod_cast hup
  have hlo' : -((⌈|R| * L⌉₊ : ℤ) + 1) ≤ ⌊R * z i⌋ := by exact_mod_cast hlo
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg]
  omega

/-- The mass a test function puts on the cell above `x`. -/
noncomputable def cellMass (R : ℝ) (φ : Space d → ℝ) (x : Sandpile.Site d) : ℝ :=
  ∫ z in cell d R x, φ z

/-- The mass a bounded test function puts on a cell of the mesh is at most its
bound times the volume `R^{-d}` of the cell. -/
theorem abs_cellMass_le {R : ℝ} (hR : 0 < R) (φ : Space d → ℝ) (C : ℝ)
    (hC : ∀ z, |φ z| ≤ C) (x : Sandpile.Site d) :
    |cellMass R φ x| ≤ C * R⁻¹ ^ d := by
  have hv : volume (cell d R x) = ENNReal.ofReal R⁻¹ ^ d := volume_cell d hR x
  have hfin : volume (cell d R x) < ⊤ := by
    rw [hv]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := cell d R x) (f := φ) (C := C) hfin
    (fun z _ => by simpa [Real.norm_eq_abs] using hC z)
  have htoReal : (volume : Measure (Space d)).real (cell d R x) = R⁻¹ ^ d := by
    rw [MeasureTheory.measureReal_def, hv, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hR))]
  rw [htoReal] at h
  simpa [Real.norm_eq_abs, cellMass] using h

/-- The embedded field against a test function, split over the cells: away from
the support of the test function both sides vanish, and on the support only the
cell of the point contributes. -/
theorem embed_mul_eq_sum (R : ℝ) (f : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (s : Finset (Sandpile.Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) (z : Space d) :
    Sandpile.Continuum.embed R f z * φ z
      = ∑ x ∈ s, (cell d R x).indicator (fun w => f x * φ w) z := by
  classical
  by_cases hz : φ z = 0
  · rw [hz, mul_zero]
    refine (Finset.sum_eq_zero fun x _ => ?_).symm
    by_cases hx : z ∈ cell d R x
    · rw [Set.indicator_of_mem hx, hz, mul_zero]
    · rw [Set.indicator_of_notMem hx]
  · have h0 : ∀ x ∈ s, x ≠ (fun i => ⌊R * z i⌋) →
        (cell d R x).indicator (fun w => f x * φ w) z = 0 := by
      intro x _ hne
      exact Set.indicator_of_notMem (fun hzc => hne (funext fun i => mem_cell_iff.mp hzc i).symm) _
    have h1 : (fun i => ⌊R * z i⌋) ∉ s →
        (cell d R (fun i => ⌊R * z i⌋)).indicator
          (fun w => f (fun i => ⌊R * z i⌋) * φ w) z = 0 :=
      fun hmem => absurd (hs z hz) hmem
    rw [Finset.sum_eq_single (fun i => ⌊R * z i⌋) h0 h1,
      Set.indicator_of_mem (mem_cell_self R z)]
    rfl

/-- The lattice pairing as a finite sum over the cells of the mesh:
`f^{(R)}(φ) = ∑_x f(x) ∫_{cell(x)} φ`. -/
theorem latticePairing_eq_sum (R : ℝ) (f : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) (s : Finset (Sandpile.Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    Sandpile.Continuum.latticePairing R f φ = ∑ x ∈ s, f x * cellMass R φ x := by
  show ∫ z : Space d, Sandpile.Continuum.embed R f z * φ z = ∑ x ∈ s, f x * cellMass R φ x
  simp_rw [embed_mul_eq_sum R f φ s hs]
  rw [MeasureTheory.integral_finsetSum s
    (fun x _ => (hφ.const_mul (f x)).indicator (measurableSet_cell d R x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MeasureTheory.integral_indicator (measurableSet_cell d R x),
    MeasureTheory.integral_const_mul]
  rfl

end Sandpile.Support
