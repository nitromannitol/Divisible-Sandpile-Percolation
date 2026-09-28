import Sandpile.Law
import Sandpile.Walk
import LatticeProb.Prob.FiniteMarginal

/-!
# Step 1 of path survival, the independent case

Step 1 of `lem:dgt4-path-survival` (`sandpile.tex:5495-5526`), the case in which the
threshold field is independent:

  "When the $J(x)$ are independent, the left-hand side of
   \eqref{eq:dgt4-path-threshold-factorization} is zero."

The display in question (`sandpile.tex:5502-5508`) compares the probability that a
finite family of threshold events holds simultaneously with the product of the
individual probabilities,

  "$\left|\P\left(\bigcap_{x\in\Lambda}\{J(x)\leq b_x\}\right)
     -\prod_{x\in\Lambda}\P(J(0)\leq b_x)\right|$".

In case (b) of `IsThresholdField`, `J(x) = -G(0,0)\zeta(x)` is a function of the single
coordinate `σ(x)` of the i.i.d. mass field, so the two sides are equal and the difference
is exactly zero, for every finite `Λ` and every choice of levels.

The first theorem is the finite-dimensional product formula behind it: reading finitely
many coordinates of an i.i.d. field gives the product of the one-site probabilities. It
is the finite-box marginal `LatticeProb.iidLaw_map_restrict` of the library, evaluated on
a box.
-/

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- Finitely many coordinates of an i.i.d. field are independent: the
probability that each of them lies in a prescribed measurable set is the product
of the one-site probabilities. -/
theorem massLaw_iInter_coord (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (Λ : Finset (Site d)) (A : Site d → Set ℝ) (hA : ∀ x, MeasurableSet (A x)) :
    (massLaw d ν) {σ : Site d → ℝ | ∀ x ∈ Λ, σ x ∈ A x} = ∏ x ∈ Λ, ν (A x) := by
  classical
  have hset : {σ : Site d → ℝ | ∀ x ∈ Λ, σ x ∈ A x}
      = Λ.restrict ⁻¹' (Set.univ.pi fun x : Λ => A (x : Site d)) := by
    ext σ
    constructor
    · intro hσ x _
      exact hσ x x.2
    · intro hσ x hx
      exact hσ ⟨x, hx⟩ (Set.mem_univ _)
  have hmeasres : Measurable (Λ.restrict : (Site d → ℝ) → (Λ → ℝ)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x : Site d)
  have hbox : MeasurableSet (Set.univ.pi fun x : Λ => A (x : Site d)) :=
    MeasurableSet.univ_pi fun x => hA _
  rw [massLaw, hset, ← Measure.map_apply hmeasres hbox,
    LatticeProb.iidLaw_map_restrict d ν Λ, Measure.pi_pi]
  exact Finset.prod_coe_sort Λ fun x => ν (A x)

/-- One coordinate of an i.i.d. field has the one-site law. -/
theorem massLaw_coord (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : Site d) (A : Set ℝ) (hA : MeasurableSet A) :
    (massLaw d ν) {σ : Site d → ℝ | σ x ∈ A} = ν A := by
  classical
  have h := massLaw_iInter_coord (d := d) ν {x} (fun _ => A) (fun _ => hA)
  simpa using h

/-- **Step 1 of `lem:dgt4-path-survival` in case (b).**  When
`J(x) = -G(0,0)ζ(x)` reads a single coordinate of the i.i.d. field, the
threshold events at distinct sites are independent and the probability that they
all hold is exactly the product of the individual probabilities: the left-hand
side of `eq:dgt4-path-threshold-factorization` is zero. -/
theorem centeredMassLaw_threshold_factorization (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -(green d 0 0 * scenery d σ x))
    (Λ : Finset (Site d)) (b : Site d → ℝ) :
    (centeredMassLaw d ν) {σ : Site d → ℝ | ∀ x ∈ Λ, J σ x ≤ b x}
      = ∏ x ∈ Λ, (centeredMassLaw d ν) {σ : Site d → ℝ | J σ 0 ≤ b x} := by
  classical
  set μ : Measure ℝ := ν.map fun z => 1 + 2 * (d : ℝ) * z with hμ
  have hμprob : IsProbabilityMeasure μ := by
    rw [hμ]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  set A : Site d → Set ℝ := fun x => {t : ℝ | -(green d 0 0 * ((t - 1) / (2 * d))) ≤ b x} with hA
  have hAmeas : ∀ x, MeasurableSet (A x) := by
    intro x
    exact measurableSet_le (by fun_prop) measurable_const
  have hevent : ∀ (y : Site d) (x : Site d),
      {σ : Site d → ℝ | J σ y ≤ b x} = {σ : Site d → ℝ | σ y ∈ A x} := by
    intro y x
    ext σ
    simp only [Set.mem_setOf_eq, hJ σ y, hA, scenery]
  have hall : {σ : Site d → ℝ | ∀ x ∈ Λ, J σ x ≤ b x}
      = {σ : Site d → ℝ | ∀ x ∈ Λ, σ x ∈ A x} := by
    ext σ
    constructor
    · intro hσ x hx
      have := hσ x hx
      rw [hJ σ x] at this
      simpa [hA, scenery] using this
    · intro hσ x hx
      have := hσ x hx
      rw [hJ σ x]
      simpa [hA, scenery] using this
  haveI := hμprob
  have hcm : centeredMassLaw d ν = massLaw d μ := by rw [centeredMassLaw, hμ]
  rw [hcm, hall, massLaw_iInter_coord (d := d) μ Λ A hAmeas]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [hevent 0 x, massLaw_coord (d := d) μ 0 (A x) (hAmeas x)]

end Sandpile
