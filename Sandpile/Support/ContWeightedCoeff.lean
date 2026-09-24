/-
The pairing of the time-weighted membrane field against a test function as a
finite linear functional of the scenery, and the bound on its coefficients.

This is the first display of the proof of `prop:weighted-membrane-limit`
(`sandpile.tex:4717-4723`):

  "For `φ ∈ C_c^∞(ℝ^d)`, write `𝓕_R(φ) = ∑_{z∈ℤ^d} a_R(z) ζ(z)`,
   `sup_z |a_R(z)| ≤ C(φ) R^{-d/2}`, where the coefficient bound follows from
   the Gaussian upper bound."

The coefficient is `a_R(z) = ∑_x w(x,z) ∫_{cell(x)} φ`, with `w` the weighted
kernel `∑_{j<t} q(j) p_j(x,z)` and the cells those of `Sandpile.Support.cell`.
The bound proved here is the elementary one: the weighted kernel is dominated
by `Q` times the finite-time Green kernel, whose total mass in the first
variable is exactly the horizon `t`, and each cell carries mass at most
`‖φ‖_∞ R^{-d}`; so `|a_R(z)| ≤ Q ‖φ‖_∞ t R^{-d}`, which at `t = ⌊R^2T⌋` and
after the prefactor `R^{(d-4)/2}` is `Q ‖φ‖_∞ T R^{-d/2}`, the paper's bound.

The second half of the file is the Chapman-Kolmogorov identity for the weighted
kernel,
  `∑_z w(x,z) w(y,z) = ∑_{a<t} ∑_{b<t} q(a) q(b) p_{a+b}(x,y)`,
which is the paper's `Cov(P^iζ(x), P^jζ(y)) = Var(ζ(0)) p_{i+j}(x,y)` summed
against the weights, and is what the local central limit theorem is applied to
in the Riemann-sum step.
-/
import Sandpile.Support.ContCell
import Sandpile.Support.TightWeightedMembrane

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The weighted kernel -/

/-- The time-weighted kernel is symmetric. -/
theorem weightedKernel_symm (q : ℕ → ℝ) (t : ℕ) (x y : Site d) :
    weightedKernel d q t x y = weightedKernel d q t y x :=
  Finset.sum_congr rfl fun k _ => by rw [heatKernel_symm k x y]

/-- One step of the semigroup against the time-weighted kernel. -/
theorem tsum_heatKernel_mul_weightedKernel (q : ℕ → ℝ) (m t : ℕ) (x y : Site d) :
    ∑' z : Site d, heatKernel d m x z * weightedKernel d q t z y
      = ∑ j ∈ Finset.range t, q j * heatKernel d (m + j) x y := by
  have hexp : ∀ z : Site d, heatKernel d m x z * weightedKernel d q t z y
      = ∑ j ∈ Finset.range t, q j * (heatKernel d m x z * heatKernel d j z y) := by
    intro z
    show heatKernel d m x z * (∑ j ∈ Finset.range t, q j * heatKernel d j z y) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum fun j (_ : j ∈ Finset.range t) =>
      (summable_heatKernel_mul m x _).mul_left (q j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, tsum_heatKernel_mul_heatKernel m j x y]

/-- The doubled time-weighted kernel is the double time sum of transition
probabilities against the two weights. -/
theorem tsum_weightedKernel_mul_weightedKernel (q : ℕ → ℝ) (t : ℕ) (x y : Site d) :
    ∑' z : Site d, weightedKernel d q t x z * weightedKernel d q t y z
      = ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
          q a * q b * heatKernel d (a + b) x y := by
  have h1 : ∀ z : Site d, weightedKernel d q t x z * weightedKernel d q t y z
      = ∑ a ∈ Finset.range t, q a * (heatKernel d a x z * weightedKernel d q t z y) := by
    intro z
    rw [weightedKernel_symm q t y z]
    show (∑ a ∈ Finset.range t, q a * heatKernel d a x z) * weightedKernel d q t z y = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [tsum_congr h1,
    Summable.tsum_finsetSum fun a (_ : a ∈ Finset.range t) =>
      (summable_heatKernel_mul a x _).mul_left (q a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tsum_mul_left, tsum_heatKernel_mul_weightedKernel q a t x y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The transition kernel has total mass one in its first variable as well. -/
theorem summable_heatKernel_left (k : ℕ) (y : Site d) :
    Summable (fun x : Site d => heatKernel d k x y) := by
  have h : (fun x : Site d => heatKernel d k x y) = fun x => heatKernel d k y x :=
    funext fun x => heatKernel_symm k x y
  rw [h]
  simpa using summable_heatKernel_mul k y (fun _ => (1 : ℝ))

/-- The finite-time Green kernel has total mass the horizon in its first
variable. -/
theorem tsum_greenTime_left (hd : 1 ≤ d) (t : ℕ) (y : Site d) :
    ∑' x : Site d, greenTime d t x y = (t : ℝ) := by
  have h : ∀ x : Site d, greenTime d t x y
      = ∑ j ∈ Finset.range t, heatKernel d j y x := by
    intro x
    rw [greenTime_symm t x y]
    rfl
  rw [tsum_congr h,
    Summable.tsum_finsetSum fun j (_ : j ∈ Finset.range t) => by
      simpa using summable_heatKernel_mul j y (fun _ => (1 : ℝ))]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range t) => tsum_heatKernel hd j y]
  simp

/-- The finite-time Green kernel is summable in its first variable. -/
theorem summable_greenTime_left (t : ℕ) (y : Site d) :
    Summable (fun x : Site d => greenTime d t x y) := by
  have h : (fun x : Site d => greenTime d t x y) = fun x => greenTime d t y x :=
    funext fun x => greenTime_symm t x y
  rw [h]
  simpa using summable_greenTime_mul t y (fun _ => (1 : ℝ))

/-- A finite sum of the finite-time Green kernel in its first variable is at
most the horizon. -/
theorem sum_greenTime_left_le (hd : 1 ≤ d) (t : ℕ) (y : Site d)
    (s : Finset (Site d)) : ∑ x ∈ s, greenTime d t x y ≤ (t : ℝ) := by
  rw [← tsum_greenTime_left hd t y]
  exact (summable_greenTime_left t y).sum_le_tsum s
    (fun x _ => greenTime_nonneg t x y)

/-! ### The coefficients of the pairing -/

/-- The coefficient of `ζ(z)` in the pairing of the time-weighted membrane field
against a test function: `a_R(z) = ∑_x w(x,z) ∫_{cell(x)} φ`. -/
noncomputable def pairCoeff (d : ℕ) (R : ℝ) (q : ℕ → ℝ) (t : ℕ)
    (φ : Space d → ℝ) (s : Finset (Site d)) (z : Site d) : ℝ :=
  ∑ x ∈ s, weightedKernel d q t x z * cellMass R φ x

/-- The pairing of the time-weighted membrane field against a test function is a
finite linear functional of the scenery, with the coefficients `pairCoeff`.
This is `𝓕_R(φ) = ∑_z a_R(z) ζ(z)` of `sandpile.tex:4713`. -/
theorem latticePairing_weightedField_eq (R : ℝ) (q : ℕ → ℝ) (t : ℕ)
    (ζ : Site d → ℝ) (φ : Space d → ℝ) (hφ : Integrable φ)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (s' : Finset (Site d)) (hs' : ∀ x ∈ s, Sandpile.boxFinset x t ⊆ s') :
    Sandpile.Continuum.latticePairing R (weightedField q t ζ) φ
      = ∑ i : Fin s'.card, pairCoeff d R q t φ s (siteEnum s' i) * ζ (siteEnum s' i) := by
  rw [latticePairing_eq_sum R (weightedField q t ζ) φ hφ s hs]
  have h : ∀ x ∈ s, weightedField q t ζ x * cellMass R φ x
      = ∑ i : Fin s'.card,
        weightedKernel d q t x (siteEnum s' i) * cellMass R φ x * ζ (siteEnum s' i) := by
    intro x hx
    rw [weightedField_eq_sum_siteEnum (hs' x hx) ζ, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairCoeff, Finset.sum_mul]

/-- The coefficient bound of `sandpile.tex:4714`: the weighted kernel is
dominated by `Q` times the finite-time Green kernel, whose total mass in the
first variable is the horizon, and each cell carries mass at most `C R^{-d}`. -/
theorem abs_pairCoeff_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (q : ℕ → ℝ) (t : ℕ)
    (Q : ℝ) (hQ : ∀ j ∈ Finset.range t, |q j| ≤ Q) (hQ0 : 0 ≤ Q)
    (φ : Space d → ℝ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (hC0 : 0 ≤ C)
    (s : Finset (Site d)) (z : Site d) :
    |pairCoeff d R q t φ s z| ≤ Q * (C * R⁻¹ ^ d) * (t : ℝ) := by
  have hpow : (0 : ℝ) ≤ R⁻¹ ^ d := pow_nonneg (le_of_lt (inv_pos.mpr hR)) d
  calc |pairCoeff d R q t φ s z|
      ≤ ∑ x ∈ s, |weightedKernel d q t x z * cellMass R φ x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, Q * greenTime d t x z * (C * R⁻¹ ^ d) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_weightedKernel_le q t Q hQ x z)
          (abs_cellMass_le hR φ C hC x) (abs_nonneg _)
          (mul_nonneg hQ0 (greenTime_nonneg t x z))
    _ = Q * (C * R⁻¹ ^ d) * ∑ x ∈ s, greenTime d t x z := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ Q * (C * R⁻¹ ^ d) * (t : ℝ) := by
        refine mul_le_mul_of_nonneg_left (sum_greenTime_left_le hd t z s)
          (mul_nonneg hQ0 (mul_nonneg hC0 hpow))

/-- The coefficient vanishes at sites the walk cannot reach from the support of
the test function. -/
theorem pairCoeff_eq_zero_of_far (R : ℝ) (q : ℕ → ℝ) (t : ℕ) (φ : Space d → ℝ)
    (s : Finset (Site d)) (z : Site d) (hz : ∀ x ∈ s, t < Sandpile.boxDist x z) :
    pairCoeff d R q t φ s z = 0 := by
  refine Finset.sum_eq_zero fun x hx => ?_
  have hk : weightedKernel d q t x z = 0 := by
    by_contra hne
    exact absurd (weightedKernel_support q t x z hne) (not_le.mpr (hz x hx))
  rw [hk, zero_mul]

/-- The doubled weighted kernel is summable. -/
theorem summable_weightedKernel_mul (q : ℕ → ℝ) (t : ℕ) (x y : Site d) :
    Summable (fun z : Site d => weightedKernel d q t x z * weightedKernel d q t y z) := by
  refine summable_of_hasFiniteSupport ?_
  refine Set.Finite.subset (Sandpile.boxFinset x t).finite_toSet ?_
  intro z hz
  have hne : weightedKernel d q t x z ≠ 0 := by
    intro h
    exact hz (by simp [h])
  exact Sandpile.mem_boxFinset (weightedKernel_support q t x z hne)

/-- The total sum of squares of the coefficients is the double cell sum of the
doubled weighted kernel.  With the Chapman-Kolmogorov identity
`tsum_weightedKernel_mul_weightedKernel` this is `Var(𝓕_R(φ))/Var(ζ(0))` written
out as a Riemann sum in the two space and the two time variables, which is what
the local central limit theorem is applied to at `sandpile.tex:4719-4724`. -/
theorem tsum_pairCoeff_sq (R : ℝ) (q : ℕ → ℝ) (t : ℕ) (φ : Space d → ℝ)
    (s : Finset (Site d)) :
    ∑' z : Site d, pairCoeff d R q t φ s z ^ 2
      = ∑ p ∈ s ×ˢ s, cellMass R φ p.1 * cellMass R φ p.2 *
          ∑' z : Site d, weightedKernel d q t p.1 z * weightedKernel d q t p.2 z := by
  have hfin := summable_weightedKernel_mul (d := d) q t
  have hexp : ∀ z : Site d, pairCoeff d R q t φ s z ^ 2
      = ∑ p ∈ s ×ˢ s, cellMass R φ p.1 * cellMass R φ p.2 *
          (weightedKernel d q t p.1 z * weightedKernel d q t p.2 z) := by
    intro z
    rw [sq, pairCoeff, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum fun p (_ : p ∈ s ×ˢ s) => (hfin p.1 p.2).mul_left _]
  exact Finset.sum_congr rfl fun p _ => (hfin p.1 p.2).tsum_mul_left _

/-- The box of radius `r + t` about the origin contains the box of radius `t`
about every site of the box of radius `r`. -/
theorem boxFinset_subset_of_mem (r t : ℕ) {x : Site d}
    (hx : x ∈ Sandpile.boxFinset (0 : Site d) r) :
    Sandpile.boxFinset x t ⊆ Sandpile.boxFinset (0 : Site d) (r + t) := by
  intro y hy
  refine Sandpile.mem_boxFinset ?_
  have h1 : Sandpile.boxDist (0 : Site d) x ≤ r := Sandpile.mem_boxFinset_iff.mp hx
  have h2 : Sandpile.boxDist x y ≤ t := Sandpile.mem_boxFinset_iff.mp hy
  have h3 := Sandpile.boxDist_trans (0 : Site d) x y
  omega

/-- The coefficient bound of `sandpile.tex:4714` in the paper's normalization:
after the prefactor `R^{(d-4)/2}` and at the horizon `⌊R^2T⌋`, the coefficients
are of order `R^{-d/2}`, uniformly in the site. -/
theorem abs_scaled_pairCoeff_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) {T : ℝ} (hT : 0 ≤ T)
    (q : ℕ → ℝ) (Q : ℝ) (hQ : ∀ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, |q j| ≤ Q) (hQ0 : 0 ≤ Q)
    (φ : Space d → ℝ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) (hC0 : 0 ≤ C)
    (s : Finset (Site d)) (z : Site d) :
    |R ^ (((d : ℝ) - 4) / 2) * pairCoeff d R q ⌊R ^ 2 * T⌋₊ φ s z|
      ≤ Q * C * T * R ^ (-(d : ℝ) / 2) := by
  have hpow : (R⁻¹ : ℝ) ^ d = R ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
  have hexp : R ^ (((d : ℝ) - 4) / 2) * (R ^ (-(d : ℝ)) * R ^ (2 : ℕ))
      = R ^ (-(d : ℝ) / 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR, ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hprefix : (0 : ℝ) ≤ R ^ (((d : ℝ) - 4) / 2) := Real.rpow_nonneg hR.le _
  have hcell : (0 : ℝ) ≤ Q * (C * R⁻¹ ^ d) :=
    mul_nonneg hQ0 (mul_nonneg hC0 (pow_nonneg (le_of_lt (inv_pos.mpr hR)) d))
  calc |R ^ (((d : ℝ) - 4) / 2) * pairCoeff d R q ⌊R ^ 2 * T⌋₊ φ s z|
      = R ^ (((d : ℝ) - 4) / 2) * |pairCoeff d R q ⌊R ^ 2 * T⌋₊ φ s z| := by
        rw [abs_mul, abs_of_nonneg hprefix]
    _ ≤ R ^ (((d : ℝ) - 4) / 2) * (Q * (C * R⁻¹ ^ d) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (abs_pairCoeff_le hd hR q _ Q hQ hQ0 φ C hC hC0 s z) hprefix
    _ ≤ R ^ (((d : ℝ) - 4) / 2) * (Q * (C * R⁻¹ ^ d) * (R ^ (2 : ℕ) * T)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hcell) hprefix
    _ = Q * C * T * (R ^ (((d : ℝ) - 4) / 2) * (R ^ (-(d : ℝ)) * R ^ (2 : ℕ))) := by
        rw [hpow]; ring
    _ = Q * C * T * R ^ (-(d : ℝ) / 2) := by rw [hexp]

end Sandpile.Support
