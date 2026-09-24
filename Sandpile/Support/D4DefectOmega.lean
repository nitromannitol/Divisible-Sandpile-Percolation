/-
The `ω`-shifted test function of `eq:d4-omega-representative`, and the cell
masses it puts on the mesh.

The `ω`-representative pairs against `φ̃ = φ - ω∫_Dφ`, whose integral vanishes
because `ω` integrates to one on `D` and both functions are supported in `D`.
That is what kills the site-free part of the truncation defect in Step 1 of
`prop:d4-superdiffusive-limit`: after it is removed, only the centred kernel
`∑_{j≥t}(p_j(x,y)-p_j(0,y))` is paired, and its `ℓ²` bound is uniform over the
cells that `φ̃` meets.  The total mass `∑_x|m_R(x)|` of those cells stays bounded
as `R → ∞`, since there are `O((RL)^d)` of them and each carries mass
`O(R^{-d})`.
-/
import Sandpile.Support.D4DefectPairing
import Sandpile.Support.ContCell

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The `ω`-shifted test function `φ̃ = φ - ω∫_Dφ` of
`eq:d4-omega-representative`. -/
noncomputable def omegaShift (D : Set (Space d)) (w φ : Space d → ℝ) : Space d → ℝ :=
  fun z => φ z - w z * ∫ y in D, φ y

/-- The `ω`-shift of a test function is a test function on all of `ℝ^d`. -/
theorem isTestFn_univ_omegaShift {D : Set (Space d)} {w φ : Space d → ℝ}
    (hw : IsTestFn D w) (hφ : IsTestFn D φ) :
    IsTestFn (Set.univ : Set (Space d)) (omegaShift D w φ) := by
  obtain ⟨hws, hwc, -⟩ := hw
  obtain ⟨hφs, hφc, -⟩ := hφ
  refine ⟨hφs.sub (hws.mul contDiff_const), ?_, Set.subset_univ _⟩
  exact hφc.sub (hwc.mul_right)

/-- A test function on `D` integrates over `D` to its integral over `ℝ^d`. -/
theorem setIntegral_eq_integral_of_isTestFn {D : Set (Space d)} {φ : Space d → ℝ}
    (hφ : IsTestFn D φ) : ∫ y in D, φ y = ∫ y, φ y :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hz =>
    image_eq_zero_of_notMem_tsupport fun hc => hz (hφ.2.2 hc)

/-- **The `ω`-shift integrates to zero.** -/
theorem integral_omegaShift_eq_zero {D : Set (Space d)} {w φ : Space d → ℝ}
    (hw : IsAveragingDensity D w) (hφ : IsTestFn D φ) :
    ∫ z, omegaShift D w φ z = 0 := by
  obtain ⟨hwt, -, hw1⟩ := hw
  obtain ⟨C, L, -, -, -, -, hφint⟩ := exists_bound_of_isTestFn
    (d := d) ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩
  obtain ⟨C', L', -, -, -, -, hwint⟩ := exists_bound_of_isTestFn
    (d := d) ⟨hwt.1, hwt.2.1, Set.subset_univ _⟩
  have hwtot : ∫ z, w z = 1 := by
    rw [← setIntegral_eq_integral_of_isTestFn hwt]; exact hw1
  have hφtot : ∫ y in D, φ y = ∫ y, φ y := setIntegral_eq_integral_of_isTestFn hφ
  unfold omegaShift
  rw [integral_sub hφint (hwint.mul_const _), integral_mul_const, hwtot, hφtot]
  ring

/-- A site of the box of radius `N` is within `√d·N` of the origin in the
Euclidean metric. -/
theorem latticeDist_le_of_mem_boxFinset {N : ℕ} {x : Site d}
    (hx : x ∈ Sandpile.boxFinset (0 : Site d) N) :
    Sandpile.External.latticeDist x 0 ≤ Real.sqrt d * N := by
  have hb : Sandpile.boxDist (0 : Site d) x ≤ N := Sandpile.mem_boxFinset_iff.mp hx
  have hcoord : ∀ i : Fin d, ((x i - (0 : Site d) i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    intro i
    have h : ((0 : Site d) i - x i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => ((0 : Site d) i - x i).natAbs)
        (Finset.mem_univ i)) hb
    simp only [Pi.zero_apply] at h ⊢
    have hint : -(N : ℤ) ≤ x i ∧ x i ≤ (N : ℤ) := by omega
    have h1 : -(N : ℝ) ≤ ((x i : ℤ) : ℝ) := by exact_mod_cast hint.1
    have h2 : ((x i : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hint.2
    have hz : (((x i - 0 : ℤ)) : ℝ) = ((x i : ℤ) : ℝ) := by push_cast; ring
    rw [hz]
    nlinarith
  have hsum : ∑ i : Fin d, ((x i - (0 : Site d) i : ℤ) : ℝ) ^ 2 ≤ (d : ℝ) * (N : ℝ) ^ 2 := by
    calc ∑ i : Fin d, ((x i - (0 : Site d) i : ℤ) : ℝ) ^ 2
        ≤ ∑ _i : Fin d, (N : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (N : ℝ) ^ 2 := by simp [Finset.sum_const]
  show Real.sqrt (∑ i : Fin d, ((x i - (0 : Site d) i : ℤ) : ℝ) ^ 2) ≤ Real.sqrt d * N
  refine le_trans (Real.sqrt_le_sqrt hsum) (le_of_eq ?_)
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (Nat.cast_nonneg N)]

end Sandpile.Support
