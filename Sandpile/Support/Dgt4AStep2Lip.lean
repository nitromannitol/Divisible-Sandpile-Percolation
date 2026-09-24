/-
The Lipschitz constant of Step 2 of case (a) (`sandpile.tex:5114-5124`):

  "propagating this by `P^{k_n+1}` bounds this Lipschitz constant by
   `P^{k_n+1}\Cov(V_\infty(\cdot),V_\infty(0))(0)/\Sigma^2
    =(\Var\zeta(0)/\Sigma^2)\sum_{\ell\geq k_n+1}(\ell-k_n)p_\ell(0,0)\leq Ck_n^{-(d-4)/2}`."

`P^j` applied to `x\mapsto\Cov(V_\infty(x),V_\infty(0))` at the origin is, after the
one-site variance is divided out, the inner product of the `j`-step average of the Green
coefficient families with the Green coefficients at the origin, and that average is the
tail kernel (`Support/Dgt4AGaussTailLp.lean`).  So the Lipschitz constant is
`\langle\text{tail}_j,G(0,\cdot)\rangle/\sum_zG(0,z)^2`, and Cauchy-Schwarz with
`eq:dgt4-tail-kernel` bounds it by `Cj^{(4-d)/4}`.

The paper's exponent is `(4-d)/2`, obtained from the semigroup identity
`\langle\text{tail}_j,\text{tail}_j\rangle=\langle\text{tail}_{2j},G(0,\cdot)\rangle`
rather than from Cauchy-Schwarz.  The weaker exponent proved here is all that Steps 2 and 4
consume: both uses are of the form `(\E u_n(0))^2k_n^{-\theta}\to0`, and with the paper's
horizon `k_n=\lceil(\log(n+2))^{6/(d-4)}\rceil` the exponent `\theta=(d-4)/4` already gives
`k_n^{\theta}=(\log(n+2))^{3/2}`, against `(\E u_n(0))^2\asymp\log n`.
-/
import Sandpile.Support.Dgt4AGaussTailLp
import Sandpile.Support.LinGaussFactor

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

theorem avgIterate_innerGreenLp_eq (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    {j : ℕ} (hj : 1 ≤ j) :
    (avg^[j] (fun x => (inner ℝ (greenLp d hd x) (greenLp d hd 0) : ℝ))) 0
      = (inner ℝ (tailKernelLp hGH hd hj) (greenLp d hd 0) : ℝ) := by
  rw [avg_iterate_eq_finsetSum, ← sum_smul_greenLp_eq_tailKernelLp hGH hd hj, sum_inner]
  exact Finset.sum_congr rfl fun x _ => by rw [real_inner_smul_left]

theorem exists_abs_avgIterate_innerGreenLp_le (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      |(avg^[j] (fun x => (inner ℝ (greenLp d hd x) (greenLp d hd 0) : ℝ))) 0|
        ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  obtain ⟨Ct, hCt, htail⟩ := (hGH d hd).2.2.1
  refine ⟨Real.sqrt Ct * ‖greenLp d hd (0 : Site d)‖ + 1, by positivity, fun j hj => ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  rw [avgIterate_innerGreenLp_eq hGH hd hj]
  have hcs := abs_real_inner_le_norm (tailKernelLp hGH hd hj) (greenLp d hd 0)
  have h2 : (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2)
      ≤ Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := (htail j hj).2.2
  have hroot : Real.sqrt ((j : ℝ) ^ ((4 - (d : ℝ)) / 2)) = (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hjpos.le]
    congr 1
    ring
  have hnorm : ‖tailKernelLp hGH hd hj‖ ≤ Real.sqrt Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    have hsq : ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ^ 2
        ≤ Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
      rw [norm_tailKernelLp_sq hGH hd hj]
      exact h2
    have hle : ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖
        ≤ Real.sqrt (Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2)) := by
      rw [show ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖
          = Real.sqrt (‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul hCt.le, hroot] at hle
  have hgn : (0 : ℝ) ≤ ‖greenLp d hd (0 : Site d)‖ := norm_nonneg _
  have hjp : (0 : ℝ) ≤ (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg hjpos.le _
  have hmul : ‖tailKernelLp hGH hd hj‖ * ‖greenLp d hd (0 : Site d)‖
      ≤ (Real.sqrt Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 4)) * ‖greenLp d hd (0 : Site d)‖ :=
    mul_le_mul_of_nonneg_right hnorm hgn
  have hCtn : (0 : ℝ) ≤ Real.sqrt Ct := Real.sqrt_nonneg _
  nlinarith [hcs, hmul, hjp, hgn, hCtn]


/-- **The Lipschitz constant of Step 2** (`sandpile.tex:5109-5119`):
`P^j\Cov(V_\infty(\cdot),V_\infty(0))(0)/\Sigma^2\leq Cj^{(4-d)/4}`.  The one-site variance
of the scenery cancels between the covariance and `\Sigma^2`, so the statement is about the
Green function alone. -/
theorem exists_avgIterate_greenCovariance_le (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      |(avg^[j] (fun x => ∑' z : Site d, green d x z * green d 0 z)) 0| / greenSqSum d
        ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  obtain ⟨C, hC, hbnd⟩ := exists_abs_avgIterate_innerGreenLp_le hGH hd
  have hgs1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  have hgs : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one hgs1
  refine ⟨C, hC, fun j hj => ?_⟩
  have hfun : (fun x : Site d => ∑' z : Site d, green d x z * green d 0 z)
      = fun x : Site d => (inner ℝ (greenLp d hd x) (greenLp d hd 0) : ℝ) :=
    funext fun x => (inner_greenLp hd x 0).symm
  rw [hfun, div_le_iff₀ hgs]
  have hpow : (0 : ℝ) ≤ (j : ℝ) ^ ((4 - (d : ℝ)) / 4) :=
    Real.rpow_nonneg (Nat.cast_nonneg j) _
  calc |(avg^[j] (fun x => (inner ℝ (greenLp d hd x) (greenLp d hd 0) : ℝ))) 0|
      ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := hbnd j hj
    _ = C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * 1 := by ring
    _ ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * greenSqSum d :=
        mul_le_mul_of_nonneg_left hgs1 (by positivity)

end Sandpile
