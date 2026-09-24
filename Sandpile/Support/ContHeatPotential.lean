/-
The rescaled linear field `Z_R` of `ssec:scaling-dlt4` (`sandpile.tex:1833-1839`)
as a finite linear functional of the scenery.

`Z_R(r,w) = R^{d/2-2}\sum_{z}g_{\lfloor R^2r\rfloor}(\lfloor Rw\rfloor,z)\zeta(z)`
is a sum over the whole lattice, but the finite-time Green kernel vanishes
outside the box of radius the time index, so the sum is finite and the field is a
linear functional of finitely many scenery values.  This is the form the
finite-dimensional convergence of `prop:dlt4-heat-potential-invariance` needs,
since the Lindeberg-Feller theorem is applied to it.
-/
import Sandpile.Support.HeatPotentialDefs
import Sandpile.Support.FiniteCoord
import Sandpile.Support.ContCell

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The mesh value of the rescaled linear field is a finite linear functional of
the scenery over any finset containing the box of radius the time index. -/
theorem meshValue_eq_sum (R : ℝ) (ζ : Site d → ℝ) (k : ℕ) (z : Site d)
    {s : Finset (Site d)} (hs : Sandpile.boxFinset z k ⊆ s) :
    Sandpile.Frozen.HeatPotentialInvariance.meshValue d R ζ k z
      = ∑ i : Fin s.card,
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d k z (siteEnum s i)) *
            ζ (siteEnum s i) := by
  show R ^ ((d : ℝ) / 2 - 2) * ∑' y : Site d, Sandpile.greenTime d k z y * ζ y = _
  have h : ∑' y : Site d, Sandpile.greenTime d k z y * ζ y
      = ∑ i : Fin s.card, Sandpile.greenTime d k z (siteEnum s i) * ζ (siteEnum s i) := by
    rw [sum_siteEnum s fun y => Sandpile.greenTime d k z y * ζ y]
    refine tsum_eq_sum fun y hy => ?_
    have hg : Sandpile.greenTime d k z y = 0 := by
      by_contra hne
      exact hy (hs (Sandpile.mem_boxFinset (Sandpile.greenTime_support k z hne)))
    simp [hg]
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The coefficient of `ζ(y)` in the multilinear interpolation `Z_R^{\rm lin}`:
the same multilinear combination of the Green kernels that the interpolation
takes of the mesh values. -/
noncomputable def interpCoeff (d : ℕ) (R r : ℝ) (w : Sandpile.Continuum.Space d)
    (y : Site d) : ℝ :=
  ∑ ε : Fin d → Bool,
    (∏ i : Fin d, if ε i then R * w i - (⌊R * w i⌋ : ℝ)
      else 1 - (R * w i - (⌊R * w i⌋ : ℝ))) *
      ((1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊
            (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y) +
        (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
          (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1)
            (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y))

/-- The interpolated rescaled linear field is a finite linear functional of the
scenery, with the coefficients `interpCoeff`. -/
theorem linInterp_eq_sum (R r : ℝ) (ζ : Site d → ℝ) (w : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
        (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) :
    Sandpile.Frozen.HeatPotentialInvariance.linInterp d R ζ r w
      = ∑ i : Fin s.card, interpCoeff d R r w (siteEnum s i) * ζ (siteEnum s i) := by
  classical
  have hsub : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) ⌊R ^ 2 * r⌋₊ ⊆ s := by
    intro ε
    refine subset_trans (fun y hy => ?_) (hs ε)
    exact Sandpile.mem_boxFinset (le_trans (Sandpile.mem_boxFinset_iff.mp hy) (Nat.le_succ _))
  have hstep : ∀ ε : Fin d → Bool,
      (∏ i : Fin d, if ε i then R * w i - (⌊R * w i⌋ : ℝ)
        else 1 - (R * w i - (⌊R * w i⌋ : ℝ))) *
        ((1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
            Sandpile.Frozen.HeatPotentialInvariance.meshValue d R ζ ⌊R ^ 2 * r⌋₊
              (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) +
          (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
            Sandpile.Frozen.HeatPotentialInvariance.meshValue d R ζ (⌊R ^ 2 * r⌋₊ + 1)
              (fun i => ⌊R * w i⌋ + if ε i then 1 else 0))
      = ∑ i : Fin s.card,
          ((∏ i : Fin d, if ε i then R * w i - (⌊R * w i⌋ : ℝ)
            else 1 - (R * w i - (⌊R * w i⌋ : ℝ))) *
            ((1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))) *
                (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d ⌊R ^ 2 * r⌋₊
                  (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (siteEnum s i)) +
              (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)) *
                (R ^ ((d : ℝ) / 2 - 2) * Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1)
                  (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (siteEnum s i)))) *
            ζ (siteEnum s i) := by
    intro ε
    rw [meshValue_eq_sum R ζ ⌊R ^ 2 * r⌋₊ _ (hsub ε),
      meshValue_eq_sum R ζ (⌊R ^ 2 * r⌋₊ + 1) _ (hs ε), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  show ∑ ε : Fin d → Bool, _ = _
  rw [Finset.sum_congr rfl fun ε (_ : ε ∈ Finset.univ) => hstep ε, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [interpCoeff, Finset.sum_mul]

/-- The corners of the cell of the mesh containing a point of the ball of radius
`L`, thickened by the horizon, lie in one box about the origin.  This supplies
the finset the representation above quantifies over. -/
theorem interp_box_subset (R L r : ℝ) (w : Sandpile.Continuum.Space d) (hw : ‖w‖ ≤ L)
    (ε : Fin d → Bool) :
    Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1)
      ⊆ Sandpile.boxFinset (0 : Site d) (⌈|R| * L⌉₊ + 1 + 1 + (⌊R ^ 2 * r⌋₊ + 1)) := by
  intro y hy
  refine Sandpile.mem_boxFinset ?_
  have h0 : Sandpile.boxDist (0 : Site d) (fun i => ⌊R * w i⌋) ≤ ⌈|R| * L⌉₊ + 1 :=
    Sandpile.mem_boxFinset_iff.mp (floor_mem_boxFinset R w hw)
  have h1 : Sandpile.boxDist (fun i => ⌊R * w i⌋)
      (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) ≤ 1 := by
    refine Finset.sup_le fun i _ => ?_
    by_cases hε : ε i <;> simp [hε]
  have h2 : Sandpile.boxDist (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y
      ≤ ⌊R ^ 2 * r⌋₊ + 1 := Sandpile.mem_boxFinset_iff.mp hy
  have h3 := Sandpile.boxDist_trans (0 : Site d) (fun i => ⌊R * w i⌋)
    (fun i => ⌊R * w i⌋ + if ε i then 1 else 0)
  have h4 := Sandpile.boxDist_trans (0 : Site d)
    (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y
  omega

end Sandpile.Support
