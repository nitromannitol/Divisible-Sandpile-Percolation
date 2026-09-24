/-
The sharp Lipschitz constant of `\Theta_n` for the `\ell^2` distance
(`sandpile.tex:5267-5269`).

"The coordinatewise Lipschitz constants of `\Theta_n` are bounded by
`\sum_{j\geq k_n+1}p_j(0,z)`, so `eq:dgt4-tail-kernel` bounds its Gaussian concentration
proxy by `Ck_n^{-(d-4)/2}`."  The proxy is the `\ell^2` norm of the coordinatewise
constants, and what the concentration inequality needs is the Lipschitz constant for the
`\ell^2` distance itself.  On an infinite product the second does not follow from the first
by itself, since a coordinatewise Lipschitz functional of infinitely many coordinates need
not be continuous; it follows together with the continuity supplied by the crude constant
`\|G(0,\cdot)\|` of `Support/Dgt4AConcField.lean`.  Replacing the coordinates of a finite
set one at a time gives the tail-kernel bound against finitely supported differences, by
Cauchy-Schwarz with the `\ell^2` norm of the tail kernel, and the crude bound carries it to
the limit along the boxes.
-/
import Sandpile.Support.Dgt4AConcField
import Sandpile.Support.Dgt4AGaussTailLp
import Sandpile.Support.Dgt4ATailLipKernel

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The scenery with the coordinates of a finite set replaced. -/
noncomputable def patch (S : Finset (Site d)) (ζ ζ' : Site d → ℝ) : Site d → ℝ :=
  fun z => if z ∈ S then ζ' z else ζ z

theorem patch_empty (ζ ζ' : Site d → ℝ) : patch ∅ ζ ζ' = ζ := by
  funext z
  rw [patch, if_neg (Finset.notMem_empty z)]

theorem patch_insert {S : Finset (Site d)} {a : Site d} (ha : a ∉ S) (ζ ζ' : Site d → ℝ) :
    patch (insert a S) ζ ζ' = Function.update (patch S ζ ζ') a (ζ' a) := by
  funext z
  by_cases hz : z = a
  · subst hz
    rw [Function.update_self, patch, if_pos (Finset.mem_insert_self z S)]
  · rw [Function.update_of_ne hz, patch, patch]
    by_cases hzS : z ∈ S
    · rw [if_pos (Finset.mem_insert_of_mem hzS), if_pos hzS]
    · rw [if_neg (fun hmem => (Finset.mem_insert.mp hmem).elim hz (fun hh => hzS hh)),
        if_neg hzS]

theorem patch_apply_of_notMem {S : Finset (Site d)} {z : Site d} (hz : z ∉ S)
    (ζ ζ' : Site d → ℝ) : patch S ζ ζ' z = ζ z := by
  rw [patch, if_neg hz]

/-- The difference to a patch is supported on the patched set. -/
theorem hasSum_sq_sub_patch (S : Finset (Site d)) (ζ ζ' : Site d → ℝ) :
    HasSum (fun z => (ζ z - patch S ζ ζ' z) ^ 2) (∑ z ∈ S, (ζ z - ζ' z) ^ 2) := by
  have hzero : ∀ z ∉ S, (ζ z - patch S ζ ζ' z) ^ 2 = 0 := by
    intro z hz
    rw [patch_apply_of_notMem hz]
    ring
  have hs : HasSum (fun z => (ζ z - patch S ζ ζ' z) ^ 2)
      (∑ z ∈ S, (ζ z - patch S ζ ζ' z) ^ 2) := hasSum_sum_of_ne_finset_zero hzero
  have heq : ∑ z ∈ S, (ζ z - patch S ζ ζ' z) ^ 2 = ∑ z ∈ S, (ζ z - ζ' z) ^ 2 :=
    Finset.sum_congr rfl fun z hz => by rw [patch, if_pos hz]
  rwa [heq] at hs

/-- The difference from a patch to the target is supported off the patched set. -/
theorem hasSum_sq_patch_sub (S : Finset (Site d)) (ζ ζ' : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ζ z - ζ' z) ^ 2) M) :
    HasSum (fun z => (patch S ζ ζ' z - ζ' z) ^ 2) (M - ∑ z ∈ S, (ζ z - ζ' z) ^ 2) := by
  have h1 : HasSum (fun z => if z ∈ S then (ζ z - ζ' z) ^ 2 else 0)
      (∑ z ∈ S, (ζ z - ζ' z) ^ 2) := by
    have hs : HasSum (fun z : Site d => if z ∈ S then (ζ z - ζ' z) ^ 2 else 0)
        (∑ z ∈ S, if z ∈ S then (ζ z - ζ' z) ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero (fun z hz => if_neg hz)
    have heq : (∑ z ∈ S, if z ∈ S then (ζ z - ζ' z) ^ 2 else 0)
        = ∑ z ∈ S, (ζ z - ζ' z) ^ 2 :=
      Finset.sum_congr rfl fun z hz => if_pos hz
    rwa [heq] at hs
  refine (h.sub h1).congr_fun fun z => ?_
  by_cases hz : z ∈ S
  · rw [if_pos hz, patch, if_pos hz]
    ring
  · rw [if_neg hz, patch, if_neg hz]
    ring

/-- **The tail-kernel bound against a finitely supported difference**
(`sandpile.tex:5058-5060` chained over the patched set). -/
theorem abs_avgIterate_deviation_patch_le (hd : 5 ≤ d) (ζ ζ' : Site d → ℝ)
    (hζ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n j : ℕ) (S : Finset (Site d)) :
    |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (patch S ζ ζ') y
            - odometerOf (patch S ζ ζ') n y)) 0|
      ≤ ∑ z ∈ S, Sandpile.External.tailKernel d j z * |ζ z - ζ' z| := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [patch_empty]
      simp
  | @insert a S ha ih =>
      have hconvS : ∀ y : Site d, ∃ L : ℝ,
          Tendsto (fun m => infiniteGreenFieldPartial m (patch S ζ ζ') y) atTop (𝓝 L) :=
        (exists_tendsto_infiniteGreenField_sub hd ζ (patch S ζ ζ') _
          (hasSum_sq_sub_patch S ζ ζ') hζ).1
      have hstep := abs_avgIterate_deviation_update_le_tailKernel (by omega : 3 ≤ d)
        (patch S ζ ζ') hconvS a (ζ' a) n j
      rw [← patch_insert ha ζ ζ', patch_apply_of_notMem ha] at hstep
      have htri := abs_sub_le
        ((avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0)
        ((avg^[j] (fun y => infiniteGreenField (patch S ζ ζ') y
            - odometerOf (patch S ζ ζ') n y)) 0)
        ((avg^[j] (fun y => infiniteGreenField (patch (insert a S) ζ ζ') y
            - odometerOf (patch (insert a S) ζ ζ') n y)) 0)
      rw [Finset.sum_insert ha]
      linarith [ih]

/-- **The `\ell^2` Lipschitz constant of `\Theta_n` is the `\ell^2` norm of the tail
kernel** (`sandpile.tex:5262-5264`). -/
theorem abs_avgIterate_deviation_sub_le_tailKernelLp
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (ζ ζ' : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ζ z - ζ' z) ^ 2) M)
    (hζ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n j : ℕ) (hj : 1 ≤ j) :
    |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
        - (avg^[j] (fun y => infiniteGreenField ζ' y - odometerOf ζ' n y)) 0|
      ≤ ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M := by
  classical
  have hMnn : 0 ≤ M := h.nonneg fun z => sq_nonneg _
  have hΛnn : 0 ≤ ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ := norm_nonneg _
  have hsummable := summable_tailKernel_sq hGH hd hj
  have hfin : ∀ S : Finset (Site d),
      |(avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0
          - (avg^[j] (fun y => infiniteGreenField (patch S ζ ζ') y
              - odometerOf (patch S ζ ζ') n y)) 0|
        ≤ ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M := by
    intro S
    refine (abs_avgIterate_deviation_patch_le hd ζ ζ' hζ n j S).trans ?_
    refine (Real.sum_mul_le_sqrt_mul_sqrt S (fun z => Sandpile.External.tailKernel d j z)
      (fun z => |ζ z - ζ' z|)).trans ?_
    have h1 : Real.sqrt (∑ z ∈ S, Sandpile.External.tailKernel d j z ^ 2)
        ≤ ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ := by
      have hle : (∑ z ∈ S, Sandpile.External.tailKernel d j z ^ 2)
          ≤ ∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2 :=
        hsummable.sum_le_tsum S (fun z _ => sq_nonneg _)
      have hnorm := norm_tailKernelLp_sq hGH hd hj
      have := Real.sqrt_le_sqrt hle
      rwa [← hnorm, Real.sqrt_sq hΛnn] at this
    have h2 : Real.sqrt (∑ z ∈ S, |ζ z - ζ' z| ^ 2) ≤ Real.sqrt M := by
      refine Real.sqrt_le_sqrt ?_
      refine le_trans (le_of_eq ?_) (sum_le_hasSum S (fun z _ => sq_nonneg _) h)
      exact Finset.sum_congr rfl fun z _ => sq_abs _
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) hΛnn
  set A : ℕ → ℝ := fun m => ∑ z ∈ boxFinset (0 : Site d) m, (ζ z - ζ' z) ^ 2 with hA
  have hAlim : Tendsto A atTop (𝓝 M) := by
    have hb := tendsto_sum_boxFinset h.summable
    rwa [h.tsum_eq] at hb
  have hclose : ∀ m : ℕ,
      |(avg^[j] (fun y => infiniteGreenField (patch (boxFinset (0 : Site d) m) ζ ζ') y
            - odometerOf (patch (boxFinset (0 : Site d) m) ζ ζ') n y)) 0
          - (avg^[j] (fun y => infiniteGreenField ζ' y - odometerOf ζ' n y)) 0|
        ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt (M - A m) := by
    intro m
    have hconvS : ∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun r => infiniteGreenFieldPartial r
          (patch (boxFinset (0 : Site d) m) ζ ζ') y) atTop (𝓝 L) :=
      (exists_tendsto_infiniteGreenField_sub hd ζ (patch (boxFinset (0 : Site d) m) ζ ζ') _
        (hasSum_sq_sub_patch (boxFinset (0 : Site d) m) ζ ζ') hζ).1
    exact abs_avgIterate_deviation_sub_le_of_hasSum_sq hd _ ζ' (M - A m)
      (hasSum_sq_patch_sub (boxFinset (0 : Site d) m) ζ ζ' M h) hconvS n j
  have hg : Tendsto (fun m : ℕ =>
      ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M
        + ‖greenLp d hd (0 : Site d)‖ * Real.sqrt (M - A m)) atTop
      (𝓝 (‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M)) := by
    have hz : Tendsto (fun m : ℕ => M - A m) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := tendsto_const_nhds
      have hc2 := hc.sub hAlim
      simpa using hc2
    have hsq : Tendsto (fun m : ℕ => Real.sqrt (M - A m)) atTop (𝓝 0) := by
      have hcomp := (Real.continuous_sqrt.tendsto 0).comp hz
      simpa [Function.comp_def] using hcomp
    simpa using tendsto_const_nhds.add (hsq.const_mul ‖greenLp d hd (0 : Site d)‖)
  refine ge_of_tendsto hg (Filter.Eventually.of_forall fun m => ?_)
  have htri := abs_sub_le
    ((avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ n y)) 0)
    ((avg^[j] (fun y => infiniteGreenField (patch (boxFinset (0 : Site d) m) ζ ζ') y
        - odometerOf (patch (boxFinset (0 : Site d) m) ζ ζ') n y)) 0)
    ((avg^[j] (fun y => infiniteGreenField ζ' y - odometerOf ζ' n y)) 0)
  linarith [hfin (boxFinset (0 : Site d) m), hclose m]

end Sandpile
