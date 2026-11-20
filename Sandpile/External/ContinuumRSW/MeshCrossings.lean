import Sandpile.External.ContinuumRSW.Mesh
import Sandpile.External.ContinuumRSW.ProbabilityLimit

/-!
# Eventual approximation of continuum crossings

For a continuous field, fine-grid threshold crossings bracket the continuum
crossings after an arbitrarily small loss of level.
-/

open Filter MeasureTheory Set Topology

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings

/-- At a sufficiently fine mesh, a continuous field has the same modulus bound
on both the tall and the wide integer-aspect rectangles. -/
theorem eventually_mesh_modulus {f : Space 2 → ℝ} (hf : Continuous f)
    {R : ℝ} (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ rectSet ![0, 0] ![2 * M * R, 2 * M * R],
        ∀ y ∈ rectSet ![0, 0] ![2 * M * R, 2 * M * R],
          dist x y ≤ δ → |f x - f y| ≤ ε) ∧
      ∃ N, ∀ n ≥ N, 14 * crossingMesh R n ≤ δ := by
  obtain ⟨δ, hδ, hmod⟩ := exists_modulus
    (isCompact_rectSet ![0, 0] ![2 * M * R, 2 * M * R]) hf hε
  have hlim : Tendsto (fun n => 14 * crossingMesh R n) atTop (𝓝 0) := by
    simpa using (tendsto_crossingMesh R).const_mul 14
  have hev : ∀ᶠ n in atTop, 14 * crossingMesh R n < δ :=
    hlim.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨δ, hδ, hmod, N, fun n hn => (hN n hn).le⟩

/-- A continuum tall crossing eventually induces sampled tall crossings with a
small level loss. -/
theorem eventually_sampled_tall_of_crosses {Ω : Type} {X : Space 2 → Ω → ℝ} {ω : Ω}
    (hf : Continuous fun x => X x ω) {R ρ ε level : ℝ} {M : ℕ}
    (hR : 0 < R) (hρ : 1 ≤ ρ) (hρM : ρ ≤ M) (hε : 0 < ε)
    (hc : Crosses ![0, 0] ![2 * R, 2 * ρ * R] 0 {u | level ≤ X u ω}) :
    ∃ N, ∀ n ≥ N, ω ∈ sampledCrossingEvent X (crossingMesh R n) (level - ε)
      (2 * (n + 1)) (2 * M * (n + 1)) := by
  obtain ⟨δ, hδ, hmod, N, hN⟩ := eventually_mesh_modulus hf M hε
  refine ⟨N, fun n hn => ?_⟩
  have ht : 0 < crossingMesh R n := by simp only [crossingMesh]; positivity
  have hM : (1 : ℝ) ≤ M := hρ.trans hρM
  have hwide : 2 * ρ * R ≤ 2 * M * R := by nlinarith
  have hshort : 2 * R ≤ 2 * M * R := by nlinarith
  have hsub : rectSet ![0, 0] ![2 * R, 2 * ρ * R] ⊆
      rectSet ![0, 0] ![2 * R, 2 * M * R] := by
    apply rectSet_mono (by intro i; rfl)
    intro i
    fin_cases i <;> simp_all
  have hcross : Crosses ![0, 0] ![2 * R, 2 * M * R] 0 {u | level ≤ X u ω} :=
    crosses_rect_mono hsub rfl rfl hc
  have hrect : rectSet ![0, 0] ![2 * R, 2 * M * R] ⊆
      rectSet ![0, 0] ![2 * M * R, 2 * M * R] := by
    apply rectSet_mono (by intro i; rfl)
    intro i
    fin_cases i <;> simp_all
  apply sampledCrossingEvent_of_crosses ht (crossingMesh_short_side R n)
    (crossingMesh_long_side R M n) ?_ hcross
  intro x hx y hy hxy
  apply hmod x (hrect hx) y (hrect hy)
  have hmesh := hN n hn
  nlinarith

/-- A fine-grid wide crossing induces a continuum wide crossing after a small
additional level loss. -/
theorem eventually_crosses_of_sampled_wide {Ω : Type} {X : Space 2 → Ω → ℝ} {ω : Ω}
    (hf : Continuous fun x => X x ω) {R ρ ε level : ℝ} {M : ℕ}
    (hR : 0 < R) (hρ : 1 ≤ ρ) (hρM : ρ ≤ M) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N,
      ω ∈ sampledCrossingEvent X (crossingMesh R n) (level - ε)
        (2 * M * (n + 1)) (2 * (n + 1)) →
      Crosses ![0, 0] ![2 * ρ * R, 2 * R] 0 {u | level - 2 * ε ≤ X u ω} := by
  obtain ⟨δ, hδ, hmod, N, hN⟩ := eventually_mesh_modulus hf M hε
  refine ⟨N, fun n hn hc => ?_⟩
  have ht : 0 < crossingMesh R n := by simp only [crossingMesh]; positivity
  have hM : (1 : ℝ) ≤ M := hρ.trans hρM
  have hshort : 2 * R ≤ 2 * M * R := by nlinarith
  have hrect : rectSet ![0, 0] ![2 * M * R, 2 * R] ⊆
      rectSet ![0, 0] ![2 * M * R, 2 * M * R] := by
    apply rectSet_mono (by intro i; rfl)
    intro i
    fin_cases i <;> simp_all
  have hc' : ω ∈ sampledCrossingEvent X (crossingMesh R n) (level - ε)
      (crossingMeshWidth ρ n) (2 * (n + 1)) := by
    exact planarCrossingEvent_width_height_mono (crossingMeshWidth_le hρM n) le_rfl _ hc
  have hbounds := crossingMeshWidth_bounds hR (le_trans (by norm_num) hρ) n
  have hbig : crossingMesh R n * (crossingMeshWidth ρ n : ℝ) ≤ 2 * M * R := by
    calc
      _ ≤ crossingMesh R n * ((2 * M * (n + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast crossingMeshWidth_le hρM n) ht.le
      _ = 2 * M * R := crossingMesh_long_side R M n
  have hresult := crosses_of_sampledCrossingEvent_clipped ht (show 0 ≤ 2 * ρ * R by positivity)
    hbounds.1 hbounds.2 hbig (crossingMesh_short_side R n) (hN n hn)
    (fun x hx y hy hxy => hmod x (hrect hx) y (hrect hy) hxy) hc'
  convert hresult using 1; ring_nf

end Sandpile.External.ContinuumRSW
