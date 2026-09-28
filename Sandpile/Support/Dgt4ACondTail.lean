import Sandpile.Support.Dgt4ACondMeas
import Sandpile.Support.Dgt4ACondUnion
import Sandpile.Support.Dgt4ACorrGap

/-!
# One-site Gaussian tail of the conditioned field

**The one-site Gaussian tail of the conditioned field**, the estimate Step 3 of case (a)
feeds to its union bound (`sandpile.tex:5176-5183`): under the conditioning
`-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)` the field at a site `z\ne0` is a Gaussian
whose mean is its linear regression on the conditioned value and whose variance is at most
`\Sigma^2`, so the probability that `V_\infty(z)+\E u_n(0)` is nonpositive is at most
`2\exp\{-m^2/(2\Sigma^2)\}` whenever `m` is a lower bound for that conditional mean.

The Gaussian input is Chernoff's bound for an isonormal image
(`measure_abs_ge_gaussIso_le`), applied to the residual coefficient family
`G(z,\cdot)-\langle G(z,\cdot),e\rangle e` with `e=G(0,\cdot)/\|G(0,\cdot)\|`.  Removing
the conditioned direction can only shrink the norm, so the variance is at most
`\|G(0,\cdot)\|^2`, which is `\Sigma^2` in the units of the conditioned scenery.
-/

open LatticeProb.Isonormal

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The residual Green coefficients at a site: `G(x,\cdot)` with its component along the
conditioned direction removed. -/
noncomputable def greenResidLp (d : ℕ) (hd : 5 ≤ d) (x : Site d) : lp (fun _ : Site d => ℝ) 2 :=
  greenLp d hd x - (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w)
    • greenUnit d hd

/-- Removing the conditioned direction does not increase the norm: the conditional variance
is at most `\Sigma^2`. -/
theorem norm_greenResidLp_sq_le (hd : 5 ≤ d) (x : Site d) :
    ‖greenResidLp d hd x‖ ^ 2 ≤ ‖greenLp d hd (0 : Site d)‖ ^ 2 := by
  have hinner : (inner ℝ (greenLp d hd x) (greenUnit d hd) : ℝ)
      = ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w := by
    rw [greenUnit, real_inner_smul_right, inner_greenLp hd x 0]
  have hnorm : ∀ t : ℝ, ‖t • greenUnit d hd‖ ^ 2 = t ^ 2 := by
    intro t
    rw [norm_smul, norm_greenUnit hd, Real.norm_eq_abs, mul_one, sq_abs]
  rw [greenResidLp, norm_sub_sq_real, real_inner_smul_right, hinner, hnorm,
    norm_greenLp_eq hd x]
  nlinarith [sq_nonneg (‖greenLp d hd (0 : Site d)‖⁻¹
    * ∑' w : Site d, green d x w * green d 0 w)]

/-- The isonormal image of the residual coefficients is the residual part of the field. -/
theorem ae_coeFn_gaussIso_greenResidLp (hd : 5 ≤ d) (x : Site d) :
    ⇑(LatticeProb.gaussIso (greenResidLp d hd x)) =ᵐ[LatticeProb.gaussLaw (Site d)]
      fun ω => ⇑(LatticeProb.gaussIso (greenLp d hd x)) ω
        - (‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w)
          * condCoord d hd ω := by
  set k : ℝ := ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w with hk
  have hmap : LatticeProb.gaussIso (greenResidLp d hd x)
      = LatticeProb.gaussIso (greenLp d hd x) - k • LatticeProb.gaussIso (greenUnit d hd) := by
    rw [greenResidLp, map_sub, map_smul]
  rw [hmap]
  filter_upwards [Lp.coeFn_sub (LatticeProb.gaussIso (greenLp d hd x))
      (k • LatticeProb.gaussIso (greenUnit d hd)),
    Lp.coeFn_smul k (LatticeProb.gaussIso (greenUnit d hd))] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  rfl

/-- **The field at the conditioned level is the regression plus an isonormal residual**
(`sandpile.tex:5160-5170`), almost surely in the standard Gaussian. -/
theorem ae_infiniteGreenField_condScenery_eq (hd : 5 ≤ d) (cc s : ℝ) (x : Site d) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      infiniteGreenField (condScenery d hd cc (residField d hd ω) s) x
        = cc * ⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω
          + cc * s * (‖greenLp d hd (0 : Site d)‖⁻¹
            * ∑' w : Site d, green d x w * green d 0 w) := by
  set k : ℝ := ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w with hk
  filter_upwards [ae_tendsto_greenPartialSum hd x, ae_coeFn_gaussIso_greenResidLp hd x]
    with ω h1 h2
  have hr : Tendsto (fun n : ℕ => ∑ z ∈ boxFinset (0 : Site d) n,
      green d x z * residField d hd ω z) atTop
      (𝓝 (⇑(LatticeProb.gaussIso (greenLp d hd x)) ω - condCoord d hd ω * k)) := by
    have hlim := h1.sub ((tendsto_greenPartialSum_greenUnit_site hd x).const_mul
      (condCoord d hd ω))
    refine hlim.congr fun n => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun z _ => by simp only [residField]; ring
  rw [condScenery_eq, infiniteGreenField_shift_eq_site hd cc x hr s, h2, ← hk]
  ring

/-- **The one-site Gaussian tail** (`sandpile.tex:5171-5178`): if `m` is a positive lower
bound for the conditional mean of `V_\infty(x)+a`, the conditional probability that
`V_\infty(x)+a` is nonpositive is at most `2\exp\{-m^2/(2\Sigma^2)\}`. -/
theorem measure_resid_condScenery_nonpos_le (hd : 5 ≤ d) {cc : ℝ} (hcc : 0 < cc) (x : Site d)
    (s a m : ℝ) (hm : 0 < m)
    (hmean : m ≤ a + cc * s * (‖greenLp d hd (0 : Site d)‖⁻¹
      * ∑' w : Site d, green d x w * green d 0 w)) :
    ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r : Site d → ℝ | infiniteGreenField (condScenery d hd cc r s) x + a ≤ 0}
      ≤ ENNReal.ofReal (2 * Real.exp
          (-((m / cc) ^ 2 / (2 * ‖greenLp d hd (0 : Site d)‖ ^ 2)))) := by
  set k : ℝ := ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' w : Site d, green d x w * green d 0 w with hk
  set N : ℝ := ‖greenLp d hd (0 : Site d)‖ with hN
  have hNpos : 0 < N := norm_greenLp_pos hd
  have hNsq : 0 < N ^ 2 := by positivity
  set ρ : Measure (Site d → ℝ) := (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  obtain ⟨g, hgmeas, hgae⟩ := aemeasurable_infiniteGreenField_condScenery hd cc s x
  have hcongr : ρ {r : Site d → ℝ | infiniteGreenField (condScenery d hd cc r s) x + a ≤ 0}
      = ρ {r : Site d → ℝ | g r + a ≤ 0} := by
    refine measure_congr ?_
    filter_upwards [hgae] with r hr
    show (infiniteGreenField (condScenery d hd cc r s) x + a ≤ 0) = (g r + a ≤ 0)
    rw [hr]
  have hmeas : MeasurableSet {r : Site d → ℝ | g r + a ≤ 0} :=
    measurableSet_le (hgmeas.add_const a) measurable_const
  have hmap : ρ {r : Site d → ℝ | g r + a ≤ 0}
      = LatticeProb.gaussLaw (Site d)
        {ω : Site d → ℝ | g (residField d hd ω) + a ≤ 0} := by
    rw [hρ, Measure.map_apply (measurable_residField hd) hmeas]
    rfl
  have hpull : ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)),
      g (residField d hd ω) = infiniteGreenField (condScenery d hd cc (residField d hd ω) s) x :=
    ae_of_ae_map (measurable_residField hd).aemeasurable hgae.symm
  have hsub : {ω : Site d → ℝ | g (residField d hd ω) + a ≤ 0}
      ≤ᵐ[LatticeProb.gaussLaw (Site d)]
      {ω : Site d → ℝ | m / cc ≤ |⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω|} := by
    filter_upwards [hpull, ae_infiniteGreenField_condScenery_eq hd cc s x] with ω h1 h2 hmem
    have hval : cc * ⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω + cc * s * k + a ≤ 0 := by
      have h4 : g (residField d hd ω) + a ≤ 0 := hmem
      rw [h1, h2] at h4
      linarith
    have hle : m ≤ -(cc * ⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω) := by
      nlinarith [hmean]
    show m / cc ≤ |⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω|
    rw [div_le_iff₀ hcc]
    nlinarith [neg_le_abs (⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω)]
  calc ρ {r : Site d → ℝ | infiniteGreenField (condScenery d hd cc r s) x + a ≤ 0}
      = LatticeProb.gaussLaw (Site d) {ω : Site d → ℝ | g (residField d hd ω) + a ≤ 0} := by
        rw [hcongr, hmap]
    _ ≤ LatticeProb.gaussLaw (Site d)
        {ω : Site d → ℝ | m / cc ≤ |⇑(LatticeProb.gaussIso (greenResidLp d hd x)) ω|} :=
        measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (2 * Real.exp (-((m / cc) ^ 2 / (2 * N ^ 2)))) :=
        measure_abs_ge_gaussIso_le (greenResidLp d hd x) (N ^ 2)
          (norm_greenResidLp_sq_le hd x) hNsq (m / cc) (by positivity)

/-- **`eq:dgt4-gaussian-positive-off-origin`** (`sandpile.tex:5171-5189`): the union bound
over the punctured box against the one-site tail.  At the conditioned level
`V_\infty(0)=-(\E u_n(0)+\Sigma^2y/\E u_n(0))` the conditional mean of
`V_\infty(z)+\E u_n(0)` is at least `\E u_n(0)(1-\rho)/2` at every `z\ne0`, so the
probability that some site of the punctured box has `V_\infty(z)+\E u_n(0)\leq0` is at most
the number of sites times the Gaussian tail at that level. -/
theorem measure_resid_exists_nonpos_le (hd : 5 ≤ d) {cc : ℝ} (hcc : 0 < cc)
    {rho a K S y s : ℝ} (k : ℕ)
    (hgap : ∀ x y : Site d, x ≠ y →
      (∑' w : Site d, green d x w * green d y w) ≤ rho * greenSqSum d)
    (ha : 0 < a) (hS : 0 ≤ S) (hy : |y| ≤ K) (hrho : rho < 1)
    (hlarge : 2 * (K * S * rho) ≤ a ^ 2 * (1 - rho))
    (hlevel : cc * s * ‖greenLp d hd (0 : Site d)‖ = -(a + S * y / a)) :
    ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r : Site d → ℝ | ∃ z ∈ (boxFinset (0 : Site d) k).erase 0,
          infiniteGreenField (condScenery d hd cc r s) z + a ≤ 0}
      ≤ ((boxFinset (0 : Site d) k).erase 0).card
        * ENNReal.ofReal (2 * Real.exp
          (-((a * (1 - rho) / 2 / cc) ^ 2 / (2 * ‖greenLp d hd (0 : Site d)‖ ^ 2)))) := by
  have hm : 0 < a * (1 - rho) / 2 := by nlinarith
  refine measure_exists_nonpos_le_card hd _ cc s a k _ ?_
  intro z hz
  have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
  refine measure_resid_condScenery_nonpos_le hd hcc z s a (a * (1 - rho) / 2) hm ?_
  have hreg := condScenery_regression_eq hd cc s z
  have hlow := condMean_greenCorr_lower hd hgap z hz0 ha hS hy
  have hhalf := half_le_gap_bound ha hlarge
  rw [hreg, hlevel]
  linarith

end Sandpile
