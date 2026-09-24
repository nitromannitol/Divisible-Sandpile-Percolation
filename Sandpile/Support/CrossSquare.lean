/-
The unit squares of the plane that the exploration of Step 2 processes
(`sandpile.tex:2255-2268`), and the cells of `ℤ^d` a square carries.

`sqOf u` is the site of the half-open unit square containing `u`, `sqAdj` is the neighbour
relation of squares (a difference of at most one in each coordinate), and `blockSites d z` is
the finite collection of cells of the unit mesh of `ℤ^d` that carry every value of the unit
ball field at every point of a square neighbouring `z`.  The two containments proved here,
`nearSites_subset_blockSites` and `sqAdj_segPt`, are what make the field on a step of the
exploration measurable for the cells the exploration has revealed.
-/
import Sandpile.Support.CrossBlockField
import Sandpile.Support.CrossPath

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

/-- The site of the unit mesh of `ℤ²` whose half-open square contains `u`. -/
noncomputable def sqOf (u : Space 2) : Sandpile.Site 2 := fun i => ⌊u i⌋

theorem sqOf_apply (u : Space 2) (i : Fin 2) : sqOf u i = ⌊u i⌋ := rfl

/-- Two squares are neighbours when their sites differ by at most one in each coordinate. -/
def sqAdj (z z' : Sandpile.Site 2) : Prop := ∀ i, |z i - z' i| ≤ 1

theorem sqAdj_refl (z : Sandpile.Site 2) : sqAdj z z := by
  intro i; simp

theorem sqAdj_symm {z z' : Sandpile.Site 2} (h : sqAdj z z') : sqAdj z' z := by
  intro i
  rw [abs_sub_comm]
  exact h i

/-- Two points at distance less than one in every coordinate lie in neighbouring squares. -/
theorem sqAdj_sqOf {u v : Space 2} (h : ∀ i, |u i - v i| < 1) : sqAdj (sqOf u) (sqOf v) := by
  intro i
  have h1 : ⌊u i⌋ ≤ ⌊v i⌋ + 1 := by
    have : u i ≤ v i + 1 := by have := abs_lt.mp (h i); linarith [this.2]
    have h2 : ⌊u i⌋ ≤ ⌊v i + 1⌋ := Int.floor_le_floor this
    simpa using h2
  have h2 : ⌊v i⌋ ≤ ⌊u i⌋ + 1 := by
    have : v i ≤ u i + 1 := by have := abs_lt.mp (h i); linarith [this.1]
    have h2 : ⌊v i⌋ ≤ ⌊u i + 1⌋ := Int.floor_le_floor this
    simpa using h2
  rw [abs_le, sqOf_apply, sqOf_apply]
  omega

theorem sqOf_mem_le {u : Space 2} (i : Fin 2) : ((sqOf u i : ℤ) : ℝ) ≤ u i := Int.floor_le _

theorem sqOf_lt {u : Space 2} (i : Fin 2) : u i < ((sqOf u i : ℤ) : ℝ) + 1 :=
  Int.lt_floor_add_one _

/-- The lower corner of the cells a square carries. -/
def blockLo (d : ℕ) (z : Sandpile.Site 2) : Sandpile.Site d :=
  fun i => if h : (i : ℕ) < 2 then z ⟨(i : ℕ), h⟩ - 2 else -1

/-- The upper corner of the cells a square carries. -/
def blockHi (d : ℕ) (z : Sandpile.Site 2) : Sandpile.Site d :=
  fun i => if h : (i : ℕ) < 2 then z ⟨(i : ℕ), h⟩ + 2 else 1

/-- The cells of the unit mesh of `ℤ^d` that a square carries: enough to read the unit ball
field at every point of every neighbouring square. -/
noncomputable def blockSites (d : ℕ) (z : Sandpile.Site 2) : Finset (Sandpile.Site d) :=
  Finset.Icc (blockLo d z) (blockHi d z)

theorem mem_blockSites {d : ℕ} {z : Sandpile.Site 2} {x : Sandpile.Site d} :
    x ∈ blockSites d z ↔ ∀ i, blockLo d z i ≤ x i ∧ x i ≤ blockHi d z i := by
  rw [blockSites, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩ i; exact ⟨h1 i, h2 i⟩
  · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem planePoint_apply {d : ℕ} (u : Space 2) (i : Fin d) :
    (planePoint (d := d) u) i = if h : (i : ℕ) < 2 then u ⟨(i : ℕ), h⟩ else 0 := rfl

/-- Every cell that can meet the unit ball about a point of a square neighbouring `z` is one
of the cells that `z` carries. -/
theorem nearSites_subset_blockSites {d : ℕ} {u : Space 2} {z : Sandpile.Site 2}
    (h : sqAdj (sqOf u) z) : nearSites d u ⊆ blockSites d z := by
  intro x hx
  rw [nearSites, Finset.mem_Icc] at hx
  obtain ⟨hlo, hhi⟩ := hx
  rw [mem_blockSites]
  intro i
  have hl : ⌊(planePoint (d := d) u) i⌋ - 1 ≤ x i := hlo i
  have hh : x i ≤ ⌊(planePoint (d := d) u) i⌋ + 1 := hhi i
  by_cases hi : (i : ℕ) < 2
  · have hpp : (planePoint (d := d) u) i = u ⟨(i : ℕ), hi⟩ := by
      rw [planePoint_apply]; exact dif_pos hi
    have hfl : ⌊(planePoint (d := d) u) i⌋ = sqOf u ⟨(i : ℕ), hi⟩ := by
      rw [hpp, sqOf_apply]
    have hadj := h ⟨(i : ℕ), hi⟩
    rw [abs_le] at hadj
    rw [blockLo, blockHi, dif_pos hi, dif_pos hi]
    rw [hfl] at hl hh
    constructor <;> omega
  · have hpp : (planePoint (d := d) u) i = 0 := by
      rw [planePoint_apply]; exact dif_neg hi
    have hfl : ⌊(planePoint (d := d) u) i⌋ = 0 := by rw [hpp]; simp
    rw [blockLo, blockHi, dif_neg hi, dif_neg hi]
    rw [hfl] at hl hh
    constructor <;> omega

/-- Every point of a segment between neighbouring squares lies in a square neighbouring the
first one. -/
theorem sqAdj_segPt {p p' : Space 2} (h : sqAdj (sqOf p) (sqOf p')) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sqAdj (sqOf (segPt p p' t)) (sqOf p) := by
  intro i
  have hval : (segPt p p' t) i = p i + t * (p' i - p i) := by
    simp [segPt]
  have hadj := h i
  rw [abs_le] at hadj
  have hp : ((sqOf p i : ℤ) : ℝ) ≤ p i := sqOf_mem_le i
  have hp' : p i < ((sqOf p i : ℤ) : ℝ) + 1 := sqOf_lt i
  have hq : ((sqOf p' i : ℤ) : ℝ) ≤ p' i := sqOf_mem_le i
  have hq' : p' i < ((sqOf p' i : ℤ) : ℝ) + 1 := sqOf_lt i
  have hcast1 : ((sqOf p' i : ℤ) : ℝ) ≤ ((sqOf p i : ℤ) : ℝ) + 1 := by exact_mod_cast by omega
  have hcast2 : ((sqOf p i : ℤ) : ℝ) ≤ ((sqOf p' i : ℤ) : ℝ) + 1 := by exact_mod_cast by omega
  have hlow : ((sqOf p i : ℤ) : ℝ) - 1 ≤ (segPt p p' t) i := by
    rw [hval]
    nlinarith
  have hhigh : (segPt p p' t) i < ((sqOf p i : ℤ) : ℝ) + 2 := by
    rw [hval]
    nlinarith
  have h1 : sqOf p i - 1 ≤ sqOf (segPt p p' t) i := by
    have hc : ((sqOf p i - 1 : ℤ) : ℝ) ≤ (segPt p p' t) i := by push_cast; linarith
    rw [sqOf_apply]
    exact Int.le_floor.mpr hc
  have h2 : sqOf (segPt p p' t) i ≤ sqOf p i + 1 := by
    have hc : (segPt p p' t) i < ((sqOf p i + 1 + 1 : ℤ) : ℝ) := by push_cast; linarith
    rw [sqOf_apply]
    have := Int.floor_lt.mpr hc
    omega
  rw [abs_le]
  constructor <;> omega


/-- The squares that can meet the rectangle with corners `a` and `b`. -/
noncomputable def rectSq (a b : Fin 2 → ℝ) : Finset (Sandpile.Site 2) :=
  Finset.Icc (fun i => ⌊a i⌋) (fun i => ⌊b i⌋)

theorem sqOf_mem_rectSq {a b : Fin 2 → ℝ} {u : Space 2} (hu : u ∈ rectSet a b) :
    sqOf u ∈ rectSq a b := by
  rw [rectSq, Finset.mem_Icc]
  constructor
  · intro i
    exact Int.floor_le_floor (hu i).1
  · intro i
    exact Int.floor_le_floor (hu i).2

theorem rectSq_nonempty {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) : (rectSq a b).Nonempty := by
  refine ⟨fun i => ⌊a i⌋, ?_⟩
  rw [rectSq, Finset.mem_Icc]
  exact ⟨fun i => le_rfl, fun i => Int.floor_le_floor (hab i).le⟩

/-- Every cell of the unit mesh of `ℤ^d` that the exploration of the rectangle can reveal. -/
noncomputable def allSites (d : ℕ) (a b : Fin 2 → ℝ) : Finset (Sandpile.Site d) :=
  (rectSq a b).biUnion (fun z => blockSites d z)

theorem blockSites_subset_allSites {d : ℕ} {a b : Fin 2 → ℝ} {z : Sandpile.Site 2}
    (hz : z ∈ rectSq a b) : blockSites d z ⊆ allSites d a b :=
  fun _ hx => Finset.mem_biUnion.mpr ⟨z, hz, hx⟩

theorem blockSites_nonempty (d : ℕ) (z : Sandpile.Site 2) : (blockSites d z).Nonempty := by
  refine ⟨blockLo d z, ?_⟩
  rw [mem_blockSites]
  intro i
  refine ⟨le_rfl, ?_⟩
  rw [blockLo, blockHi]
  by_cases hi : (i : ℕ) < 2
  · rw [dif_pos hi, dif_pos hi]; omega
  · rw [dif_neg hi, dif_neg hi]; omega

theorem allSites_nonempty (d : ℕ) {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) :
    (allSites d a b).Nonempty := by
  obtain ⟨z, hz⟩ := rectSq_nonempty hab
  obtain ⟨x, hx⟩ := blockSites_nonempty d z
  exact ⟨x, Finset.mem_biUnion.mpr ⟨z, hz, hx⟩⟩

/-- Every cell that can meet the unit ball about a point of the rectangle is one of the cells
the exploration can reveal. -/
theorem nearSites_subset_allSites {d : ℕ} {a b : Fin 2 → ℝ} {u : Space 2}
    (hu : u ∈ rectSet a b) : nearSites d u ⊆ allSites d a b :=
  fun _ hx =>
    blockSites_subset_allSites (sqOf_mem_rectSq hu)
      (nearSites_subset_blockSites (sqAdj_refl (sqOf u)) hx)

end Sandpile.Support
