import Sandpile.Support.D4MembraneCoefficients
import Sandpile.Support.D4PotentialL2

/-!
# Square-summable membrane coefficients

The paired potential-kernel coefficient is a finite linear combination of
square-summable potential-kernel slices. The corresponding finite-time
coefficient is finitely supported and hence square-summable.
-/

open scoped ENNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A finite cell pairing of square-summable kernel slices is square-summable. -/
theorem memℓp_cellKernelCoeff (R : ℝ) (ψ : Space 4 → ℝ) (s : Finset (Site 4))
    (K : Site 4 → Site 4 → ℝ) (hK : ∀ x ∈ s, Memℓp (K x) 2) :
    Memℓp (cellKernelCoeff R ψ s K) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have heq : cellKernelCoeff R ψ ∅ K = (0 : Site 4 → ℝ) := by
      funext y
      simp only [cellKernelCoeff, Finset.sum_empty, Pi.zero_apply]
    rw [heq]
    exact zero_memℓp
  | @insert x s hx ih =>
    have hxK := hK x (Finset.mem_insert_self x s)
    have hsK : ∀ y ∈ s, Memℓp (K y) 2 :=
      fun y hy => hK y (Finset.mem_insert_of_mem hy)
    have hterm : Memℓp (fun y => K x y * cellMass R ψ x) 2 := by
      simpa only [mul_comm] using hxK.const_mul (cellMass R ψ x)
    have hsum := hterm.add (ih hsK)
    have heq : cellKernelCoeff R ψ (insert x s) K =
        (fun y => K x y * cellMass R ψ x) + cellKernelCoeff R ψ s K := by
      funext y
      simp only [cellKernelCoeff, Finset.sum_insert hx, Pi.add_apply]
    rw [heq]
    exact hsum

/-- Pairing the potential kernel against finitely many cell masses gives an
`ℓ²` coefficient vector. -/
theorem memℓp_potential_cellKernelCoeff (hHK : Sandpile.External.HeatKernelBounds)
    (R : ℝ) (ψ : Space 4 → ℝ) (s : Finset (Site 4)) :
    Memℓp (cellKernelCoeff R ψ s (potentialKernel 4)) 2 :=
  memℓp_cellKernelCoeff R ψ s (potentialKernel 4)
    (fun x _ => memℓp_potentialKernel_four hHK x)

/-- Pairing a finite-time Green kernel against finitely many cell masses gives
an `ℓ²` coefficient vector. -/
theorem memℓp_greenTime_cellKernelCoeff (R : ℝ) (t : ℕ) (ψ : Space 4 → ℝ)
    (s : Finset (Site 4)) : Memℓp (cellKernelCoeff R ψ s (greenTime 4 t)) 2 := by
  classical
  let s' := s.biUnion (fun x => boxFinset x t)
  have hs' : ∀ x ∈ s, boxFinset x t ⊆ s' := by
    intro x hx y hy
    exact Finset.mem_biUnion.mpr ⟨x, hx, hy⟩
  have hfinite : {y : Site 4 | cellKernelCoeff R ψ s (greenTime 4 t) y ≠ 0}.Finite := by
    refine s'.finite_toSet.subset ?_
    intro y hy
    by_contra hys
    exact hy (cellKernelCoeff_greenTime_eq_zero hs' hys)
  exact (memℓp_zero hfinite).of_exponent_ge (by simp)

end Sandpile.Support
