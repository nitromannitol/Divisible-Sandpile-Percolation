/-
The field the exploration of Step 2 actually computes.

`sandpile.tex:2264-2268`: "For the unit square with center `z ∈ ℤ²`, let `𝒜(z)` be the finite
collection of unit cubes in `ℝ^d` meeting the closed unit neighborhood of that square ...
`Processing` this square means revealing the restrictions of `𝒲` to the cubes in `𝒜(z)` which
have not already been revealed."

Revealing the noise on a cube gives the values `𝒲(g)` for test functions `g` vanishing off that
cube, so the value of the field at `u` that the exploration can compute is the SUM of the
contributions of the cubes meeting the unit ball about `u`, one term per cube.  That sum,
`blockField`, is measurable for the sigma-algebras of those cubes on the nose, whereas
`ballField` itself is only almost surely equal to it, because the white noise is additive only
almost surely.  `CrossFieldVersion.closedCrossEvent_ae_eq_of_field_ae` is what makes the
difference harmless: the crossing reads countably many values.

`nearSites d u` is the paper's `𝒜`, the sites whose unit cells can meet the unit ball about
`u`; `exists_mem_nearSites_cell` is the covering statement that the shift of Step 3 also needs.
-/
import Sandpile.Support.CrossCubeBlocks
import Sandpile.Support.CrossBallMemLp

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- The sites of the unit mesh whose cells can meet the unit ball about `u`. -/
noncomputable def nearSites (d : ℕ) (u : Space 2) : Finset (Sandpile.Site d) :=
  Finset.Icc (fun i => ⌊(planePoint (d := d) u) i⌋ - 1)
    (fun i => ⌊(planePoint (d := d) u) i⌋ + 1)

theorem mem_nearSites_of_norm_lt_one {d : ℕ} (u : Space 2) {y : Space d}
    (h : ‖(planePoint (d := d) u) - y‖ < 1) :
    (fun i => ⌊(1 : ℝ) * y i⌋) ∈ nearSites d u := by
  have key : ∀ i : Fin d, |(planePoint (d := d) u) i - y i| < 1 := by
    intro i
    have hc := PiLp.norm_apply_le (p := 2) ((planePoint (d := d) u) - y) i
    rw [PiLp.sub_apply, Real.norm_eq_abs] at hc
    linarith
  rw [nearSites, Finset.mem_Icc]
  constructor
  · intro i
    have hi := key i
    rw [abs_lt] at hi
    have hfl : ((⌊(planePoint (d := d) u) i⌋ : ℤ) : ℝ) ≤ (planePoint (d := d) u) i :=
      Int.floor_le _
    have : ((⌊(planePoint (d := d) u) i⌋ - 1 : ℤ) : ℝ) ≤ (1 : ℝ) * y i := by
      push_cast
      linarith [hi.1, hi.2]
    exact Int.le_floor.mpr this
  · intro i
    have hi := key i
    rw [abs_lt] at hi
    have hfl : (planePoint (d := d) u) i < ((⌊(planePoint (d := d) u) i⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hgoal : ⌊(1 : ℝ) * y i⌋ < (⌊(planePoint (d := d) u) i⌋ + 1) + 1 := by
      refine Int.floor_lt.mpr ?_
      push_cast
      linarith [hi.1, hi.2]
    exact Int.lt_add_one_iff.mp hgoal

/-- Every point of the unit ball about `u` lies in a cell the exploration can reveal. -/
theorem exists_mem_nearSites_cell {d : ℕ} (u : Space 2) {y : Space d}
    (h : ‖(planePoint (d := d) u) - y‖ < 1) : ∃ x ∈ nearSites d u, y ∈ cell d 1 x :=
  ⟨_, mem_nearSites_of_norm_lt_one u h, mem_cell_self 1 y⟩

/-- The covering clause of the shift: if every site whose cell can meet the unit ball about `u`
is one of the sites the exploration can reveal, the revealed region contains that ball. -/
theorem cover_of_nearSites_range {d : ℕ} {ι : Type} (z : ι → Sandpile.Site d) (u : Space 2)
    (h : ∀ x ∈ nearSites d u, ∃ i, z i = x) :
    ∀ y : Space d, ‖(planePoint (d := d) u) - y‖ < 1 → y ∈ ⋃ i, cell d 1 (z i) := by
  intro y hy
  obtain ⟨x, hx, hyx⟩ := exists_mem_nearSites_cell u hy
  obtain ⟨i, rfl⟩ := h x hx
  exact Set.mem_iUnion.mpr ⟨i, hyx⟩

/-- The contribution of one cell to the unit kernel at `u`. -/
noncomputable def kernelPiece (d : ℕ) (u : Space 2) (x : Sandpile.Site d) : Space d → ℝ :=
  Set.indicator (cell d 1 x) (ballKernel d 1 u)

theorem kernelPiece_eq_zero {d : ℕ} {u : Space 2} {x : Sandpile.Site d} {y : Space d}
    (hy : y ∉ cell d 1 x) : kernelPiece d u x y = 0 :=
  Set.indicator_of_notMem hy _

theorem memLp_kernelPiece {d : ℕ} (hd : d = 2 ∨ d = 3) (u : Space 2) (x : Sandpile.Site d) :
    MemLp (kernelPiece d u x) 2 (volume : Measure (Space d)) :=
  (memLp_ballKernel hd one_pos u).indicator (measurableSet_cell d 1 x)

/-- The unit kernel is the sum of its contributions over the cells that can meet its support. -/
theorem ballKernel_eq_sum_kernelPiece (d : ℕ) (u : Space 2) (y : Space d) :
    ballKernel d 1 u y = ∑ x ∈ nearSites d u, kernelPiece d u x y := by
  classical
  set x₀ : Sandpile.Site d := fun i => ⌊(1 : ℝ) * y i⌋ with hx₀
  have hmem₀ : y ∈ cell d 1 x₀ := mem_cell_self 1 y
  have hother : ∀ x : Sandpile.Site d, x ≠ x₀ → kernelPiece d u x y = 0 := by
    intro x hx
    exact kernelPiece_eq_zero (fun hy => (Set.disjoint_left.mp (cell_disjoint hx) hy) hmem₀)
  by_cases hx₀mem : x₀ ∈ nearSites d u
  · rw [Finset.sum_eq_single x₀ (fun x _ hx => hother x hx) (fun h => absurd hx₀mem h)]
    rw [kernelPiece, Set.indicator_of_mem hmem₀]
  · have hzero : ∀ x ∈ nearSites d u, kernelPiece d u x y = 0 := by
      intro x hx
      exact hother x (fun h => hx₀mem (h ▸ hx))
    rw [Finset.sum_eq_zero hzero]
    by_contra hne
    have hlt : ‖(planePoint (d := d) u) - y‖ < 1 := by
      by_contra hge
      refine hne ?_
      unfold ballKernel
      rw [if_neg hge]
    exact hx₀mem (mem_nearSites_of_norm_lt_one u hlt)

theorem ballKernel_eq_sum_smul (d : ℕ) (u : Space 2) :
    ballKernel d 1 u = ∑ x ∈ nearSites d u, (1 : ℝ) • kernelPiece d u x := by
  funext y
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  exact ballKernel_eq_sum_kernelPiece d u y

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
  {W : (Space d → ℝ) → Ω → ℝ}

/-- The value of the unit field at `u` as the exploration computes it: the sum of the
contributions of the cells that can meet the unit ball about `u`. -/
noncomputable def blockField (d : ℕ) (W : (Space d → ℝ) → Ω → ℝ) (u : Space 2) (ω : Ω) : ℝ :=
  ∑ x ∈ nearSites d u, W (kernelPiece d u x) ω

/-- It is a version of the unit ball field. -/
theorem blockField_ae_eq [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) (u : Space 2) :
    blockField d W u =ᵐ[P] ballField d W 1 u := by
  have h := whiteNoise_finsetSum_ae W P hW (fun _ : Sandpile.Site d => (1 : ℝ))
    (fun x => kernelPiece d u x) (fun x => memLp_kernelPiece hd u x) (nearSites d u)
  rw [← ballKernel_eq_sum_smul d u] at h
  filter_upwards [h] with ω hω
  show ∑ x ∈ nearSites d u, W (kernelPiece d u x) ω = W (ballKernel d 1 u) ω
  rw [hω]
  simp

omit [MeasurableSpace Ω] in
/-- **The exploration's field is measurable for the cells it has revealed.**  If every site
whose cell can meet the unit ball about `u` is one of the revealed sites, the value the
exploration computes at `u` is measurable for the sigma-algebra of the revealed cells. -/
theorem measurable_blockField {ι : Type} (hd : d = 2 ∨ d = 3) (z : ι → Sandpile.Site d)
    (A : Finset ι) (u : Space 2) (hsub : ∀ x ∈ nearSites d u, ∃ i ∈ A, z i = x) :
    Measurable[indepAlg (fun i => noiseBlockAlg W (cell d 1 (z i))) (↑A : Set ι)]
      (blockField d W u) := by
  classical
  letI : MeasurableSpace Ω := indepAlg (fun i => noiseBlockAlg W (cell d 1 (z i))) (↑A : Set ι)
  refine Finset.measurable_sum _ fun x hx => ?_
  obtain ⟨i, hiA, hzi⟩ := hsub x hx
  subst hzi
  have hbase : Measurable[noiseBlockAlg W (cell d 1 (z i))] (W (kernelPiece d u (z i))) :=
    measurable_noiseBlockAlg_eval (memLp_kernelPiece hd u (z i))
      (fun y hy => kernelPiece_eq_zero hy)
  exact fun s hs => le_indepAlg (fun i => noiseBlockAlg W (cell d 1 (z i)))
    (Finset.mem_coe.mpr hiA) _ (hbase hs)

end Sandpile.Support
