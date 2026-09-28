import Sandpile.Support.Dgt4AGaussTailLp
import Sandpile.Support.LinGaussBridge

/-!
The Gaussian half of the `P^j` term of Step 1 of case (a) (`sandpile.tex:5060-5071`).

`P^jV_\infty(0)` is the linear functional of the scenery with coefficient
`P^jG(\cdot,z)(0)=\sum_{r\geq j}p_r(0,z)` at `z`, so under a centred Gaussian scenery of
variance `v` it is the centred Gaussian of variance `v\sum_z(\sum_{r\geq j}p_r(0,z))^2`, and
`eq:dgt4-tail-kernel` bounds that by `Cj^{(4-d)/2}`.  This replaces the paper's appeal to
Gaussian concentration for the `P^j` term by the exact variance.
-/

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

section Iso

variable {ι : Type*} {κ : Type*}

/-- A finite linear combination of isonormal images is the isonormal image of the same
combination of the coefficient families, indexed by a `Finset`. -/
theorem coeFn_gaussIso_finsetSum_smul (s : Finset κ) (t : κ → ℝ)
    (gs : κ → lp (fun _ : ι => ℝ) 2) :
    ⇑(LatticeProb.gaussIso (∑ i ∈ s, t i • gs i))
      =ᵐ[LatticeProb.gaussLaw ι] fun ω => ∑ i ∈ s, t i * ⇑(LatticeProb.gaussIso (gs i)) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, map_zero]
      filter_upwards [Lp.coeFn_zero ℝ 2 (LatticeProb.gaussLaw ι)] with ω hω
      rw [hω]
      simp
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, map_add, map_smul]
      filter_upwards [Lp.coeFn_add (t j • LatticeProb.gaussIso (gs j))
          (LatticeProb.gaussIso (∑ i ∈ s, t i • gs i)), ih,
        Lp.coeFn_smul (t j) (LatticeProb.gaussIso (gs j))] with ω h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Finset.sum_insert hj, smul_eq_mul]

end Iso

variable {d : ℕ}

/-- **`P^jV_\infty(0)` is the isonormal image of the heat-kernel tail.** -/
theorem ae_avgIterate_infiniteGreenField_eq (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) {j : ℕ} (hj : 1 ≤ j) (c : ℝ) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      (avg^[j] (fun x => infiniteGreenField (fun z => c * ω z) x)) 0
        = c * ⇑(LatticeProb.gaussIso (tailKernelLp hGH hd hj)) ω := by
  have hall : ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)), ∀ x : Site d,
      infiniteGreenField (fun z => c * ω z) x
        = c * ⇑(LatticeProb.gaussIso (greenLp d hd x)) ω :=
    ae_all_iff.2 fun x => ae_infiniteGreenField_eq hd x c
  filter_upwards [hall,
    coeFn_gaussIso_finsetSum_smul (boxFinset (0 : Site d) j) (fun x => heatKernel d j 0 x)
      (fun x => greenLp d hd x)] with ω hω hsum
  rw [avg_iterate_eq_finsetSum, ← sum_smul_greenLp_eq_tailKernelLp hGH hd hj, hsum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hω x]; ring

/-- **The second moment of `P^jV_\infty(0)`** under the i.i.d. centred Gaussian scenery of
variance `v`: it is `v\sum_z(\sum_{r\geq j}p_r(0,z))^2`. -/
theorem integral_avgIterate_infiniteGreenField_sq (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) {j : ℕ} (hj : 1 ≤ j) (v : ℝ≥0) :
    (∫ ζ, ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = (v : ℝ) * ∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2 := by
  classical
  have hS : Measurable fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z := by
    fun_prop
  have he : (fun ζ : Site d → ℝ => ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2)
      = fun ζ => (∑ z ∈ boxFinset (0 : Site d) j,
          heatKernel d j 0 z * infiniteGreenField ζ z) ^ 2 := by
    funext ζ
    rw [avg_iterate_eq_finsetSum]
  have hAE : AEStronglyMeasurable
      (fun ζ : Site d → ℝ => ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
    have hsum : AEMeasurable (fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) j,
        heatKernel d j 0 z * infiniteGreenField ζ z)
        (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
      by
        have h := Finset.aemeasurable_sum (μ := LatticeProb.iidLaw d (gaussianReal 0 v))
          (boxFinset (0 : Site d) j)
          (f := fun (z : Site d) (ζ : Site d → ℝ) => heatKernel d j 0 z * infiniteGreenField ζ z)
          (fun z _ => (aemeasurable_infiniteGreenField_iid hd v z).const_mul _)
        have heq : (∑ i ∈ boxFinset (0 : Site d) j,
              fun ζ : Site d → ℝ => heatKernel d j 0 i * infiniteGreenField ζ i)
            = fun ζ : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) j,
              heatKernel d j 0 z * infiniteGreenField ζ z := by
          funext ζ
          simp [Finset.sum_apply]
        rw [heq] at h
        exact h
    rw [he]
    exact (hsum.pow_const 2).aestronglyMeasurable
  rw [iidLaw_gaussianReal_eq_map d v] at hAE ⊢
  rw [integral_map hS.aemeasurable hAE]
  have hcongr : (∫ ω, ((avg^[j] (fun x =>
        infiniteGreenField (fun z => Real.sqrt (v : ℝ) * ω z) x)) 0) ^ 2
      ∂(LatticeProb.gaussLaw (Site d)))
      = ∫ ω, (Real.sqrt (v : ℝ)) ^ 2 *
          (⇑(LatticeProb.gaussIso (tailKernelLp hGH hd hj)) ω *
            ⇑(LatticeProb.gaussIso (tailKernelLp hGH hd hj)) ω)
        ∂(LatticeProb.gaussLaw (Site d)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_avgIterate_infiniteGreenField_eq hGH hd hj (Real.sqrt (v : ℝ))] with ω hω
    rw [hω]
    ring
  rw [hcongr, integral_const_mul, integral_gaussIso_mul, real_inner_self_eq_norm_sq,
    norm_tailKernelLp_sq, Real.sq_sqrt (NNReal.coe_nonneg v)]

/-- **The `P^j` term of Step 1, Gaussian half** (`sandpile.tex:5055-5066`):
`\E[(P^jV_\infty(0))^2]\leq Cj^{(4-d)/2}`, with a constant free of `j`. -/
theorem exists_integral_avgIterate_infiniteGreenField_sq_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      (∫ ζ, ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
  obtain ⟨Ct, hCt, htail⟩ := (hGH d hd).2.2.1
  refine ⟨((v : ℝ) + 1) * Ct, by positivity, fun j hj => ?_⟩
  rw [integral_avgIterate_infiniteGreenField_sq hGH hd hj v]
  have h2 : (∑' z : Site d, Sandpile.External.tailKernel d j z ^ 2)
      ≤ Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := (htail j hj).2.2
  have hpow : (0 : ℝ) ≤ (j : ℝ) ^ ((4 - (d : ℝ)) / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg j) _
  have hv : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h2 hv, mul_nonneg (mul_nonneg hCt.le hpow) hv]

end Sandpile
