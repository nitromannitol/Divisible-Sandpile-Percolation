import Sandpile.External.Stopping.StoppedPathLimit
import Sandpile.Continuum.Stopping

/-!
# Stopped paths at unit-cube exits

The boundary and exit clocks of paths converging to a regular unit-cube exit
produce convergent stopped paths. The geometric conditions are expressed using
the closed cube and the complement of its interior.
-/

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The open unit cube centered at `x`. -/
def openUnitCube {d : ℕ} (x : Continuum.Space d) : Set (Continuum.Space d) :=
  {z | ∀ i, |z i - x i| < 1}

/-- The closed unit cube centered at `x`. -/
def closedUnitCube {d : ℕ} (x : Continuum.Space d) : Set (Continuum.Space d) :=
  {z | ∀ i, |z i - x i| ≤ 1}

/-- The centered open unit cube is open. -/
theorem isOpen_openUnitCube {d : ℕ} (x : Continuum.Space d) : IsOpen (openUnitCube x) := by
  have heq : openUnitCube x = ⋂ i : Fin d, {z : Continuum.Space d | |z i - x i| < 1} := by
    ext z
    simp only [openUnitCube, mem_ofPred_eq, mem_iInter]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).sub continuous_const).abs)
    continuous_const

/-- The centered closed unit cube is closed. -/
theorem isClosed_closedUnitCube {d : ℕ} (x : Continuum.Space d) : IsClosed (closedUnitCube x) := by
  have heq : closedUnitCube x = ⋂ i : Fin d, {z : Continuum.Space d | |z i - x i| ≤ 1} := by
    ext z
    simp only [closedUnitCube, mem_ofPred_eq, mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).sub continuous_const).abs)
    continuous_const

/-- A centered closed unit cube contains its center. -/
theorem closedUnitCube_nonempty {d : ℕ} (x : Continuum.Space d) : (closedUnitCube x).Nonempty := by
  refine ⟨x, ?_⟩
  intro i
  simp only [sub_self, abs_zero, zero_le_one]

/-- In positive dimension the complement of the open unit cube is nonempty. -/
theorem openUnitCube_compl_nonempty {d : ℕ} [NeZero d] (x : Continuum.Space d) :
    (openUnitCube x)ᶜ.Nonempty := by
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  let z : Continuum.Space d := WithLp.toLp 2 (fun j : Fin d => x j + 1)
  refine ⟨z, fun hz => ?_⟩
  have h := hz i
  change |(x i + 1) - x i| < 1 at h
  have : (x i + 1) - x i = 1 := by ring
  rw [this, abs_one] at h
  exact (lt_irrefl 1) h

/-- Approaching the cube boundary and remaining close to the closed cube until
a later clock identifies both stopped-path limits at a regular cube exit. -/
theorem tendsto_stoppedPaths_of_regular_unitCube_exit
    {d : ℕ} [NeZero d] {α : Type*} {l : Filter α}
    {F : α → C(ℝ≥0, Continuum.Space d)} {f : C(ℝ≥0, Continuum.Space d)}
    {a b H : α → ℝ≥0} {δ : α → ℝ} {τ h : ℝ≥0} (x : Continuum.Space d)
    (hF : Tendsto F l (𝓝 f)) (hH : Tendsto H l (𝓝 h))
    (ha : Tendsto (fun i => infDist (F i (a i)) (openUnitCube x)ᶜ) l (𝓝 0))
    (hδ : Tendsto δ l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) (closedUnitCube x) ≤ δ i)
    (horder : ∀ᶠ i in l, a i ≤ b i)
    (hbefore : ∀ s < τ, ∀ i, |f s i - x i| < 1)
    (hafter : ∀ t > τ, ∃ s < t, ∃ i, 1 < |f s i - x i|) :
    Tendsto (fun i => LatticeProb.stoppedPath ((min (a i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) ∧
      Tendsto (fun i => LatticeProb.stoppedPath ((min (b i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) := by
  apply tendsto_stoppedPaths_of_regular_exit (isOpen_openUnitCube x).isClosed_compl
    (openUnitCube_compl_nonempty x) (isClosed_closedUnitCube x) (closedUnitCube_nonempty x)
    hF hH ha hδ hbound horder
  · intro s hs hn
    exact hn (hbefore s hs)
  · intro t ht
    obtain ⟨s, hs, i, hi⟩ := hafter t ht
    exact ⟨s, hs, fun h => (not_lt_of_ge (h i)) hi⟩

end Sandpile.External.Stopping
