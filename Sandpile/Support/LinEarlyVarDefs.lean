/-
The objects of the expansion identity of `eq:dgt4-early-derivative-variance`
(`sandpile.tex:5731-5753`), the first open piece of `eq:dgt4-derivative-variance-limit`.

The paper splits the coordinate derivative of the tested odometer at the time
`n_R - \delta R^2`,

  `D^{≤}_{R,z} := ∑_{x∈\Z^d} a_R(x) E_x ∑_{0≤i<n_R, i≤n_R-\delta R^2} 1_{X_i=z} S_{n_R,i}(X)`,

and expands `∑_z Var(D^{≤}_{R,z})` over two independent walks:

  `∑_z Var(D^{≤}_{R,z})
     = ∑_{x,y} a_R(x)a_R(y) E_x E_y ∑_{i,j≤n_R-\delta R^2} 1_{X_i=Y_j}
        Cov(S_{n_R,i}(X), S_{n_R,j}(Y) | X,Y)`.

The two ingredients of that display are the centered survival indicator
`S_{n,i}(X) - E S_{n,i}(X)` and the conditional covariance
`Cov(S_{n,i}(X),S_{n,j}(Y) | X,Y) = E[S_{n,i}(X)S_{n,j}(Y)] - E S_{n,i}(X) E S_{n,j}(Y)`,
both taken over the scenery law `μ`.  They are defined here, together with the
early part `D^{≤}_{R,z}` itself, so that the expansion can be stated and proved
in the walk-pair vocabulary of `Sandpile.walkPairLaw`.
-/
import Sandpile.Support.LinEarlyVar
import Sandpile.Support.LinSurvivalGradient

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The centered survival indicator `S_{n,i}(X) - E S_{n,i}(X)`, the scenery
expectation being taken against `μ`. -/
noncomputable def centeredSurvival (μ : Measure (Site d → ℝ)) (n i : ℕ) (X : ℕ → Site d)
    (σ : Site d → ℝ) : ℝ :=
  survivalInd σ n i X - ∫ σ', survivalInd σ' n i X ∂μ

/-- The conditional covariance `Cov(S_{n,i}(X),S_{n,j}(Y) | X,Y)` of the two
survival indicators, the paths held fixed. -/
noncomputable def covSurvival (μ : Measure (Site d → ℝ)) (n i j : ℕ)
    (X Y : ℕ → Site d) : ℝ :=
  covariance (fun σ => survivalInd σ n i X) (fun σ => survivalInd σ n j Y) μ

/-- The visit indicator `1_{X_i=z}` of the walk `X` at time `i`. -/
noncomputable def visitWeight {d : ℕ} (z : Site d) (i : ℕ) (X : ℕ → Site d) : ℝ :=
  if X i = z then (1 : ℝ) else 0

/-- The early part `D^{≤}_{R,z}` of the coordinate derivative of the tested
odometer: the sites `x` of the test box, the times `i` of the finite set `t`, and
the visit indicator `1_{X_i=z}` weighted by the survival indicator. -/
noncomputable def earlyDeriv (_μ : Measure (Site d → ℝ)) (n : ℕ) (s : Finset (Site d))
    (a : Site d → ℝ) (t : Finset ℕ) (z : Site d) (σ : Site d → ℝ) : ℝ :=
  ∑ x ∈ s, a x * ∫ X, ∑ i ∈ t,
    (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X ∂(walkLaw d x)

/-- The centered early part, whose scenery mean is zero. -/
noncomputable def earlyDerivCentered (μ : Measure (Site d → ℝ)) (n : ℕ) (s : Finset (Site d))
    (a : Site d → ℝ) (t : Finset ℕ) (z : Site d) (σ : Site d → ℝ) : ℝ :=
  ∑ x ∈ s, a x * ∫ X, ∑ i ∈ t,
    (if X i = z then (1 : ℝ) else 0) * centeredSurvival μ n i X σ ∂(walkLaw d x)

/-- The survival indicator is integrable against a probability measure on the
scenery. -/
theorem integrable_survivalInd_scenery_of_prob (μ : Measure (Site d → ℝ))
    [IsProbabilityMeasure μ] (n i : ℕ) (X : ℕ → Site d) :
    Integrable (fun σ : Site d → ℝ => survivalInd σ n i X) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_survivalInd_scenery n i X).aestronglyMeasurable
    (Filter.Eventually.of_forall fun σ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_survivalInd_le_one σ n i X

/-- The survival indicator is square-integrable against a probability measure on
the scenery. -/
theorem memLp_survivalInd (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n i : ℕ) (X : ℕ → Site d) :
    MemLp (fun σ : Site d → ℝ => survivalInd σ n i X) 2 μ :=
  MemLp.of_bound (measurable_survivalInd_scenery n i X).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun σ => by
      rw [Real.norm_eq_abs]; exact abs_survivalInd_le_one σ n i X)

/-- The centered survival indicator is integrable against a probability measure
on the scenery. -/
theorem integrable_centeredSurvival (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n i : ℕ) (X : ℕ → Site d) :
    Integrable (fun σ : Site d → ℝ => centeredSurvival μ n i X σ) μ :=
  (integrable_survivalInd_scenery_of_prob μ n i X).sub (integrable_const _)

/-- The centered survival indicator has mean zero. -/
theorem integral_centeredSurvival_eq_zero (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n i : ℕ) (X : ℕ → Site d) :
    ∫ σ, centeredSurvival μ n i X σ ∂μ = 0 := by
  unfold centeredSurvival
  rw [integral_sub (integrable_survivalInd_scenery_of_prob μ n i X)
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-- `∑'_z 1_{X_i=z} 1_{Y_j=z} = 1_{X_i=Y_j}`. -/
theorem tsum_indicator_mul_indicator (X Y : ℕ → Site d) (i j : ℕ) :
    ∑' z : Site d, (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0)
      = if X i = Y j then (1 : ℝ) else 0 := by
  classical
  rw [tsum_eq_single (X i)]
  · by_cases h : X i = Y j
    · rw [if_pos h, if_pos rfl, if_pos h.symm, one_mul]
    · rw [if_neg h, if_pos rfl, if_neg (fun hh => h hh.symm), mul_zero]
  · intro z hz
    rw [if_neg (fun h => hz h.symm), zero_mul]

/-- `covSurvival` is the scenery covariance of the two survival indicators. -/
theorem covSurvival_eq_covariance (μ : Measure (Site d → ℝ)) (n i j : ℕ)
    (X Y : ℕ → Site d) :
    covSurvival μ n i j X Y
      = covariance (fun σ => survivalInd σ n i X) (fun σ => survivalInd σ n j Y) μ := by
  rw [covSurvival]

/-- The covariance of the two visit-weighted survival time sums is the double
time sum of the conditional covariances. -/
theorem covariance_timesum_eq (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n : ℕ) (t : Finset ℕ) (z : Site d) (X Y : ℕ → Site d) :
    covariance
        (fun σ => ∑ i ∈ t, (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X)
        (fun σ => ∑ j ∈ t, (if Y j = z then (1 : ℝ) else 0) * survivalInd σ n j Y) μ
      = ∑ i ∈ t, ∑ j ∈ t,
          (if X i = z then (1 : ℝ) else 0) * (if Y j = z then (1 : ℝ) else 0)
            * covSurvival μ n i j X Y := by
  classical
  have hf : ∀ i ∈ t, MemLp (fun σ => (if X i = z then (1 : ℝ) else 0) * survivalInd σ n i X) 2 μ := by
    intro i hi
    exact (memLp_survivalInd μ n i X).const_mul _
  have hg : ∀ j ∈ t, MemLp (fun σ => (if Y j = z then (1 : ℝ) else 0) * survivalInd σ n j Y) 2 μ := by
    intro j hj
    exact (memLp_survivalInd μ n j Y).const_mul _
  rw [covariance_fun_sum_left' hf (memLp_finsetSum t hg)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [covariance_fun_sum_right' hg (hf i hi)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, covSurvival_eq_covariance]
  ring

end Sandpile
