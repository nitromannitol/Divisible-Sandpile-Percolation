import Sandpile.Support.LinJacobianCovInput
import Sandpile.Support.LinJacobianStep1Bridge
import Sandpile.Support.LinJacobianCell
import Sandpile.Support.LinJacobianCellGeneral

/-! # Jacobian Step 1 at the Tested Weight

Step 1 of `lem:dgt4-linearization-from-survival`
(`eq:dgt4-derivative-variance-limit`, `sandpile.tex:5710-5783`) at the tested
weight `a_R(x) = R^{(d-4)/2}φ_R(x)` itself.

`Support/LinJacobianEarlyDisplay.lean` proves Step 1 for an abstract nonnegative
weight family with the two intersection moments, the covariance bound and
`eq:dgt4-tested-cell-l2`; here those four inputs are supplied by
`Support/LinJacobianTestedInputs.lean`, `Support/LinJacobianCovInput.lean` and
`Support/LinJacobianCell.lean`, and the conclusion is the hypothesis `hVar` of
Step 2.

The weight is cut off below the scale `R = 1`.  The paper's weight is
nonnegative only for a positive scale, and every statement here is a limit as
`R → ∞`, so nothing is lost: the cut weight agrees with the paper's for `R ≥ 1`.
The test function is nonnegative, which is what makes the odometer functional
convex in the scenery; a signed test function is the difference of two such.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The tested weight below the scale `R = 1`, where the paper's normalization
`R^{(d-4)/2}` is not yet a nonnegative factor. -/
noncomputable def testedWeightCut (d : ℕ) (R L : ℝ) (φ : Space d → ℝ) (x : Site d) : ℝ :=
  if 1 ≤ R then testedWeight d R L φ x else 0

/-- For `R ≥ 1` the cut weight agrees with the uncut tested weight. -/
theorem testedWeightCut_eq {R : ℝ} (hR : 1 ≤ R) (L : ℝ) (φ : Space d → ℝ) (x : Site d) :
    testedWeightCut d R L φ x = testedWeight d R L φ x := by
  rw [testedWeightCut, if_pos hR]

/-- The cut weight is nonnegative when the test function `φ` is, at every scale
`R` (including `R < 1`, where it is zero). -/
theorem testedWeightCut_nonneg (R L : ℝ) {φ : Space d → ℝ} (hφ : ∀ z, 0 ≤ φ z) (x : Site d) :
    0 ≤ testedWeightCut d R L φ x := by
  rw [testedWeightCut]
  split
  · exact testedWeight_nonneg (by linarith) L hφ x
  · exact le_refl 0

/-- The cut weight vanishes outside the support box `Support.supportBox d R L`. -/
theorem testedWeightCut_eq_zero_of_notMem (R L : ℝ) (φ : Space d → ℝ) {x : Site d}
    (hx : x ∉ Sandpile.Support.supportBox d R L) : testedWeightCut d R L φ x = 0 := by
  rw [testedWeightCut]
  split
  · exact testedWeight_eq_zero_of_notMem R L φ hx
  · rfl

/-- The squares of the cut weight form a summable family over the lattice, since the
weight vanishes outside the finite support box. -/
theorem summable_sq_testedWeightCut (R L : ℝ) (φ : Space d → ℝ) :
    Summable fun x : Site d => (testedWeightCut d R L φ x) ^ 2 := by
  classical
  refine summable_of_ne_finset_zero (s := Sandpile.Support.supportBox d R L) fun x hx => ?_
  rw [testedWeightCut_eq_zero_of_notMem R L φ hx]
  norm_num

/-- For a nonnegative test function the cut weight is the scaled cell mass
without the absolute value. -/
theorem testedWeightCut_eq_scaled {R : ℝ} (hR : 1 ≤ R) (L : ℝ) {φ : Space d → ℝ}
    (hφ : ∀ z, 0 ≤ φ z) {x : Site d} (hx : x ∈ Sandpile.Support.supportBox d R L) :
    testedWeightCut d R L φ x
      = R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x| := by
  have hnn : 0 ≤ Sandpile.Support.cellMass R φ x := by
    rw [Sandpile.Support.cellMass]
    exact integral_nonneg fun z => hφ z
  rw [testedWeightCut_eq hR L φ x, testedWeight, if_pos hx, abs_of_nonneg hnn]

/-- **Step 1 of `lem:dgt4-linearization-from-survival` at the tested weight.**
The two tested intersection moments, the covariance bound of the lemma and
`eq:dgt4-tested-cell-l2` give `∑_z Var(∂_{ζ(z)}F_R) → 0`. -/
theorem tendsto_tsum_variance_testedWeight {l : Filter ℝ} [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (φ : Space d → ℝ) (hφsq : Integrable (fun z => φ z ^ 2))
    (hφ : ∀ z, 0 ≤ φ z) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ)
    (n : ℝ → ℕ) (δ₀ C : ℝ) (hδ₀ : 0 < δ₀)
    (hC : ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ (n R) i X *
                  Sandpile.survivalInd σ (n R) j Y ∂μ) -
                (∫ σ, Sandpile.survivalInd σ (n R) i X ∂μ) *
                (∫ σ, Sandpile.survivalInd σ (n R) j Y ∂μ)| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => ∑' z : Site d,
        variance (fun σ => ∑ x ∈ Sandpile.Support.supportBox d R L,
          testedWeightCut d R L φ x * odometerJacobian (scenery d σ) (n R) x z) μ)
      l (𝓝 0) := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    exists_sum_tested_integral_interCountReal_le hd hGreen φ Cφ L hCφ hL hb hint
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    exists_sum_tested_integral_interCountReal_sq_le hd hInter φ Cφ L hCφ hL hb hint
  set a : ℝ → Site d → ℝ := fun R => testedWeightCut d R L φ with hadef
  have hmatch : ∀ R : ℝ, 1 ≤ R → ∀ x ∈ Sandpile.Support.supportBox d R L,
      a R x = R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x| :=
    fun R hR x hx => testedWeightCut_eq_scaled hR L hφ hx
  have hzero : ∀ R : ℝ, ¬ (1 ≤ R) → ∀ x : Site d, a R x = 0 := by
    intro R hR x
    simp only [hadef, testedWeightCut, if_neg hR]
  refine tendsto_tsum_variance_of_moments (hl := hl) μ (by omega) n
    (fun R => Sandpile.Support.supportBox d R L) a
    (fun R x => testedWeightCut_nonneg R L hφ x)
    (fun R x hx => testedWeightCut_eq_zero_of_notMem R L φ hx)
    (fun R => summable_sq_testedWeightCut R L φ)
    interCountReal interCountReal_nonneg
    (fun t x y => ae_sum_indicator_le_interCountReal_of_green hd hGreen t x y)
    (max C 0) C₁ C₂ (∫ z, φ z ^ 2 ∂(volume : Measure (Space d)))
    (le_max_right _ _) hC₁0 hC₂0 (integral_nonneg fun z => sq_nonneg _)
    ?_ ?_
    (fun x y => integrable_interCountReal_of_green hd hGreen x y)
    (fun x y => integrable_interCountReal_sq_of_inter hd hInter x y)
    (fun N t x y => integrable_sum_indicator_mul_covSurvival μ N t x y)
    δ₀ hδ₀ (hcov_jacobian_of_frozen hd hGreen μ n δ₀ C hC) ?_
  · intro R
    by_cases hR : 1 ≤ R
    · refine le_trans (le_of_eq ?_) (hC₁ R hR)
      exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
        rw [hmatch R hR x hx, hmatch R hR y hy]
    · have : ∀ x ∈ Sandpile.Support.supportBox d R L,
          ∑ y ∈ Sandpile.Support.supportBox d R L,
            a R x * a R y * ∫ p, interCountReal p.1 p.2 ∂(walkPairLaw d x y) = 0 := by
        intro x _
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [hzero R hR x]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
      exact hC₁0
  · intro R
    by_cases hR : 1 ≤ R
    · refine le_trans (le_of_eq ?_) (hC₂ R hR)
      exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
        rw [hmatch R hR x hx, hmatch R hR y hy]
    · have : ∀ x ∈ Sandpile.Support.supportBox d R L,
          ∑ y ∈ Sandpile.Support.supportBox d R L,
            a R x * a R y * ∫ p, (interCountReal p.1 p.2) ^ 2 ∂(walkPairLaw d x y) = 0 := by
        intro x _
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [hzero R hR x]
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
      exact hC₂0
  · filter_upwards [(eventually_ge_atTop (1 : ℝ)).filter_mono hl] with R hR
    have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
    have hcongr : ∀ z : Site d, (a R z) ^ 2 = (testedWeight d R L φ z) ^ 2 := by
      intro z
      simp only [hadef]
      rw [testedWeightCut_eq hR L φ z]
    rw [tsum_congr hcongr]
    exact tsum_sq_testedWeight_le' hR0 L hint hφsq

/-- **The hypothesis `hVar` of Step 2 at the tested weight.**  The finite sum
over the sites the tested field reads, under the i.i.d. law of the field, is
below the full site sum of Step 1 under the law of the mass configuration. -/
theorem tendsto_finset_variance_testedWeight {l : Filter ℝ} [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (φ : Space d → ℝ) (hφsq : Integrable (fun z => φ z ^ 2))
    (hφ : ∀ z, 0 ≤ φ z) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L)
    (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ)
    (n : ℝ → ℕ) (δ₀ C : ℝ) (hδ₀ : 0 < δ₀)
    (hC : ∀ δ : ℝ, δ ∈ Set.Ioo 0 δ₀ →
      ∃ εfun : ℝ → ℝ, (∀ R : ℝ, 0 ≤ εfun R) ∧ Tendsto εfun l (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 → (j : ℝ) ≤ ((n R : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            Frozen.DGT4PathSurvival.IsNNPath i X →
            Frozen.DGT4PathSurvival.IsNNPath j Y →
            |(∫ σ, Sandpile.survivalInd σ (n R) i X *
                  Sandpile.survivalInd σ (n R) j Y
                  ∂(Sandpile.centeredMassLaw d ν)) -
                (∫ σ, Sandpile.survivalInd σ (n R) i X
                  ∂(Sandpile.centeredMassLaw d ν)) *
                (∫ σ, Sandpile.survivalInd σ (n R) j Y
                  ∂(Sandpile.centeredMassLaw d ν))| ≤
              C / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)) +
                εfun R)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => ∑ v ∈ testedSites (Sandpile.Support.supportBox d R L) (n R),
        variance (fun ζ => ∑ x ∈ Sandpile.Support.supportBox d R L,
          testedWeightCut d R L φ x * odometerJacobian ζ (n R) x v)
          (LatticeProb.iidLaw d ν)) l (𝓝 0) :=
  tendsto_finset_sum_variance_odometerJacobian ν (by omega) n
    (fun R => Sandpile.Support.supportBox d R L) (fun R => testedWeightCut d R L φ)
    (fun R x => testedWeightCut_nonneg R L hφ x)
    (fun R x hx => testedWeightCut_eq_zero_of_notMem R L φ hx)
    (fun R => summable_sq_testedWeightCut R L φ)
    (fun R => testedSites (Sandpile.Support.supportBox d R L) (n R))
    (tendsto_tsum_variance_testedWeight (hl := hl) hd hGreen hInter (Sandpile.centeredMassLaw d ν)
      φ hφsq hφ Cφ L hCφ hL hb hint n δ₀ C hδ₀ hC)

end Sandpile
