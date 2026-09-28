import Sandpile.Support.FiniteCoord
import LatticeProb.Prob.LaplaceTransform
import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms

/-!
# Exponential Chebyshev bound for the Green average of the scenery

The exponential Chebyshev bound for a Green average of the scenery, which is the last step of
`lem:dgt4-stretched-green-scenery-tail` (`sandpile.tex:4391-4397`). The bound is stated first on a
finite product law (`measure_pi_weighted_neg_le`, via the moment-generating-function form of
Chebyshev's inequality) and then transported to the lattice through the finite-coordinate bridge
(`iidLaw_greenTime_tail_le`), since the Green kernel `g_m(0, ·)` is supported in the box of radius
`m`; `prod_siteEnum` is the reindexing lemma that identifies a product over an enumerated finite
set of sites with the product over the set itself.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- A product over a finite set of sites, read through the enumeration. -/
theorem prod_siteEnum {M : Type*} [CommMonoid M] (s : Finset (Site d)) (f : Site d → M) :
    ∏ i : Fin s.card, f (siteEnum s i) = ∏ z ∈ s, f z := by
  classical
  have h := Equiv.prod_comp s.equivFin.symm (fun z : ↥s => f (z : Site d))
  rw [show (∏ i : Fin s.card, f (siteEnum s i))
      = ∏ i : Fin s.card, f ((s.equivFin.symm i : ↥s) : Site d) from rfl, h,
    Finset.prod_coe_sort]

/-- **Exponential Chebyshev on the finite product.**  The lower tail of a
weighted sum of i.i.d. coordinates is bounded by the product of the Laplace
transforms of the negated coordinates. -/
theorem measure_pi_weighted_neg_le {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ℓ : Fin N → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hint : ∀ i : Fin N, Integrable (fun z => Real.exp (-(lam * ℓ i) * z)) ν)
    (Mb r : ℝ)
    (hM : ∏ i : Fin N, (∫ z, Real.exp (-(lam * ℓ i) * z) ∂ν) ≤ Real.exp Mb) :
    (Measure.pi fun _ : Fin N => ν) {ξ | ∑ i, ℓ i * ξ i ≤ -r} ≤
      ENNReal.ofReal (Real.exp (Mb - lam * r)) := by
  set μ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hμ
  set X : (Fin N → ℝ) → ℝ := fun ξ => ∑ i, -(ℓ i) * ξ i with hX
  have hev : {ξ : Fin N → ℝ | ∑ i, ℓ i * ξ i ≤ -r} = {ξ | r ≤ X ξ} := by
    ext ξ
    have hsum : X ξ = -∑ i, ℓ i * ξ i := by
      rw [hX]
      simp only [neg_mul, Finset.sum_neg_distrib]
    simp only [Set.mem_setOf_eq, hsum]
    constructor <;> intro h <;> linarith
  have hfac : ∀ ξ : Fin N → ℝ,
      Real.exp (lam * X ξ) = ∏ i : Fin N, Real.exp (-(lam * ℓ i) * ξ i) := by
    intro ξ
    rw [← Real.exp_sum, hX]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hintX : Integrable (fun ξ => Real.exp (lam * X ξ)) μ := by
    refine (Integrable.fintype_prod (f := fun i (z : ℝ) => Real.exp (-(lam * ℓ i) * z))
      (μ := fun _ : Fin N => ν) hint).congr ?_
    exact Filter.Eventually.of_forall fun ξ => (hfac ξ).symm
  have hmgf : mgf X μ lam = ∏ i : Fin N, ∫ z, Real.exp (-(lam * ℓ i) * z) ∂ν := by
    rw [mgf]
    rw [integral_congr_ae (Filter.Eventually.of_forall hfac)]
    exact integral_fintype_prod_eq_prod (fun i (z : ℝ) => Real.exp (-(lam * ℓ i) * z))
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t := lam) r hlam hintX
  rw [hev]
  refine measure_le_ofReal μ _ _ ?_
  calc μ.real {ξ | r ≤ X ξ} ≤ Real.exp (-lam * r) * mgf X μ lam := hch
    _ ≤ Real.exp (-lam * r) * Real.exp Mb := by
        rw [hmgf]
        exact mul_le_mul_of_nonneg_left hM (Real.exp_nonneg _)
    _ = Real.exp (Mb - lam * r) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Exponential Chebyshev for the Green average of the scenery.**  The Green
kernel `g_m(0, ·)` is supported in the box of radius `m`, so the average is a
functional of finitely many sites and the bound above transports to the lattice
law. -/
theorem iidLaw_greenTime_tail_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hint : ∀ y : Site d,
      Integrable (fun z => Real.exp (-(lam * greenTime d m 0 y) * z)) ν)
    (Mb r : ℝ)
    (hM : ∏ z ∈ boxFinset (0 : Site d) m,
        (∫ w, Real.exp (-(lam * greenTime d m 0 z) * w) ∂ν) ≤ Real.exp Mb) :
    LatticeProb.iidLaw d ν
        {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -r} ≤
      ENNReal.ofReal (Real.exp (Mb - lam * r)) := by
  classical
  set e : Fin (boxFinset (0 : Site d) m).card → Site d := boxEnum 0 m with he
  set ℓ : Fin (boxFinset (0 : Site d) m).card → ℝ := fun i => greenTime d m 0 (e i) with hℓ
  have hpre : {ζ : Site d → ℝ | ∑' y : Site d, greenTime d m 0 y * ζ y ≤ -r}
      = (fun ζ : Site d → ℝ => fun i => ζ (e i)) ⁻¹' {ξ | ∑ i, ℓ i * ξ i ≤ -r} := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [tsum_greenTime_mul_eq_sum m 0 ζ,
      ← sum_boxEnum (0 : Site d) m fun z => greenTime d m 0 z * ζ z]
  have hmeasset : MeasurableSet {ξ : Fin (boxFinset (0 : Site d) m).card → ℝ |
      ∑ i, ℓ i * ξ i ≤ -r} := by
    refine measurableSet_le ?_ measurable_const
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
  have hmp := LatticeProb.measurePreserving_pick _ ν e (boxEnum_injective 0 m)
  rw [hpre, hmp.measure_preimage hmeasset.nullMeasurableSet]
  refine measure_pi_weighted_neg_le ν ℓ lam hlam (fun i => hint (e i)) Mb r ?_
  rw [show (∏ i : Fin (boxFinset (0 : Site d) m).card,
      ∫ z, Real.exp (-(lam * ℓ i) * z) ∂ν)
      = ∏ z ∈ boxFinset (0 : Site d) m,
          ∫ w, Real.exp (-(lam * greenTime d m 0 z) * w) ∂ν from
    prod_siteEnum _ fun z => ∫ w, Real.exp (-(lam * greenTime d m 0 z) * w) ∂ν]
  exact hM

end Sandpile
