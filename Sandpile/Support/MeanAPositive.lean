/-
The positivity clauses of `ssec:scaling-dlt4`.

`cor:dlt4-mean-asymptotic` asserts `Var 𝒰(1,0) > 0` and then divides by
`E 𝒰(1,0)`, so both positivity statements are needed.  They separate cleanly.
The variance is positive as soon as the value dominates an unbounded variable,
which is what the paper's two stopping rules `τ = 0` and `τ = 1` give
(`sandpile.tex:2024-2026`).  The mean is then positive for free, with no
Gaussian input at all: the value is a limit in distribution of the nonnegative
rescaled odometers, hence nonnegative, and a nonnegative variable of positive
variance has positive mean.
-/
import Sandpile.Support.MeanAMoment
import Sandpile.Support.ExplMeanGrowth
import Sandpile.Support.MainExplBrownianCont

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

namespace Sandpile.Support

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}

/-- The bounded continuous test function which vanishes exactly on the nonnegative
half-line. -/
noncomputable def negPartTest : BoundedContinuousFunction ℝ ℝ where
  toFun := fun y => max 0 (min 1 (-y))
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨1, fun x y => ?_⟩
    have hx : (0 : ℝ) ≤ max 0 (min 1 (-x)) := le_max_left _ _
    have hx' : max 0 (min 1 (-x)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have hy : (0 : ℝ) ≤ max 0 (min 1 (-y)) := le_max_left _ _
    have hy' : max 0 (min 1 (-y)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith

/-- **A limit in distribution of nonnegative variables is nonnegative.**  Weak
convergence tested against the bounded continuous function that vanishes exactly on
the nonnegative half-line. -/
theorem ae_nonneg_of_tendstoInDistribution [l.NeBot]
    (h : TendstoInDistribution X l Z μ μ')
    (hnn : ∀ i, ∀ᵐ ω ∂(μ i), 0 ≤ X i ω) :
    ∀ᵐ ω ∂μ', 0 ≤ Z ω := by
  have hzero : ∀ i, (∫ ω, negPartTest (X i ω) ∂(μ i)) = 0 := by
    intro i
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hnn i] with ω hω
    show max 0 (min 1 (-(X i ω))) = 0
    have hm : min 1 (-(X i ω)) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
    exact max_eq_left hm
  have hconv := tendsto_integral_bdd_of_tendstoInDistribution h negPartTest
  simp only [hzero] at hconv
  have hlim : (∫ ω, negPartTest (Z ω) ∂μ') = 0 :=
    (tendsto_nhds_unique tendsto_const_nhds hconv).symm
  have hfnn : ∀ᵐ ω ∂μ', 0 ≤ negPartTest (Z ω) :=
    Filter.Eventually.of_forall fun ω => le_max_left _ _
  have hmeas : AEStronglyMeasurable (fun ω => negPartTest (Z ω)) μ' :=
    negPartTest.continuous.comp_aestronglyMeasurable h.aemeasurable_limit.aestronglyMeasurable
  have hint : Integrable (fun ω => negPartTest (Z ω)) μ' := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_left _ _)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hfnn hint).1 hlim
  filter_upwards [hae] with ω hω
  by_contra hneg
  have hneg' : Z ω < 0 := not_le.mp hneg
  have h1 : (0 : ℝ) < min 1 (-(Z ω)) := lt_min zero_lt_one (by linarith)
  have h2 : (0 : ℝ) < max 0 (min 1 (-(Z ω))) := lt_max_of_lt_right h1
  have h3 : max 0 (min 1 (-(Z ω))) = 0 := hω
  linarith


/-- **A variable dominating an unbounded variable has positive variance.**  This is
`sandpile.tex:2024-2026`: the two stopping rules give `𝒰(1,0) ≥ max{Z(1,0),0}`, and a
nondegenerate centred Gaussian is unbounded above, so the value is nonconstant. -/
theorem variance_pos_of_ae_le_unbounded {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsProbabilityMeasure P] (X Y : Ω₀ → ℝ) (hX : MemLp X 2 P) (hle : ∀ᵐ ω ∂P, Y ω ≤ X ω)
    (hunb : ∀ M : ℝ, P {ω | M < Y ω} ≠ 0) :
    0 < variance X P := by
  rcases (variance_nonneg X P).lt_or_eq with h | h
  · exact h
  · exfalso
    have hconst : X =ᵐ[P] fun _ => ∫ ω, X ω ∂P :=
      ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hX h.symm
    have hkey : ∀ᵐ ω ∂P, ¬ ((∫ ω, X ω ∂P) < Y ω) := by
      filter_upwards [hle, hconst] with ω h1 h2
      simp only [not_lt]
      rw [← h2]
      exact h1
    rw [MeasureTheory.ae_iff] at hkey
    exact hunb (∫ ω, X ω ∂P) (by simpa using hkey)

/-- **A nonnegative variable of positive variance has positive mean.**  This is the
positivity the ninth and tenth clauses of `cor:dlt4-mean-asymptotic` divide by, and it
needs no Gaussian input. -/
theorem integral_pos_of_ae_nonneg_of_variance_pos {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsProbabilityMeasure P] (X : Ω₀ → ℝ) (hX : MemLp X 2 P) (hnn : ∀ᵐ ω ∂P, 0 ≤ X ω)
    (hvar : 0 < variance X P) :
    0 < ∫ ω, X ω ∂P := by
  have hint : Integrable X P := hX.integrable one_le_two
  rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzero : ∫ ω, X ω ∂P = 0 := h.symm
    have hae : X =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
    have : variance X P = 0 := by
      rw [variance_congr hae]
      exact variance_zero P
    exact absurd this (ne_of_gt hvar)

/-- **Theorem 1.3(i)(a) from the ninth and eighth clauses of
`cor:dlt4-mean-asymptotic`.**  The positivity of the limiting mean is not assumed: it
comes from the positivity of the limiting variance together with the nonnegativity of
the limiting value, and both are clauses the corollary already asserts.  The two
realization spaces are built here, by `Sandpile.Continuum.exists_isWhiteNoise` and by
`Sandpile.Continuum.exists_isBrownian_cont`, which supplies the motion together with
the continuity of every path and the measurability of its value at each time. -/
theorem mean_growth_le_three_of_variance_pos
    (d : ℕ) (ν : Measure ℝ)
    (h : ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∃ Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
        MemLp (fun ω => Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) 2 PW ∧
        (∀ᵐ ω ∂PW, 0 ≤ Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) ∧
        0 < variance (fun ω => Sandpile.Continuum.continuumValue d Z B PB 1 0 ω) PW ∧
        Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
            ((∫ ω, Sandpile.Continuum.continuumValue d Z B PB 1 0 ω ∂PW) *
              (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
          atTop (𝓝 1)) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L) := by
  obtain ⟨ΩW, mW, PW, hPW, W, hW⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  obtain ⟨ΩB, mB, PB, hPB, B, hB, hBc, hBm⟩ := Sandpile.Continuum.exists_isBrownian_cont d
  letI := mW
  letI := hPW
  letI := mB
  letI := hPB
  obtain ⟨Z, hL2, hnn, hvar, hratio⟩ := h ΩW PW W hW ΩB PB B hB hBc hBm
  exact exists_growth_limit_of_ratio ((4 - (d : ℝ)) / 4) _
    (integral_pos_of_ae_nonneg_of_variance_pos PW _ hL2 hnn hvar) _ hratio

end Sandpile.Support
