/-
The convergence half of `prop:weighted-membrane-limit` (`sandpile.tex:4692-4703`)
reduced to one limit: the limit of the sum of squares of the rescaled
coefficients.

The proof of the proposition (`sandpile.tex:4717-4731`) has three steps.  The
first writes the pairing as `∑_z a_R(z) ζ(z)` and bounds the coefficients by
`C(φ) R^{-d/2}`; that is `Sandpile.Support.latticePairing_weightedField_eq` and
`Sandpile.Support.abs_scaled_pairCoeff_le`.  The third is the Lindeberg-Feller
theorem, which is `Sandpile.Support.tendstoInDistribution_linear_pick_mass`.
The second, the only analytic step, is the local central limit theorem followed
by a Riemann-sum argument, which identifies

  `lim_R ∑_z a_R(z)^2  =  Var(𝒢(φ)) / Var(ζ(0))`.

The theorem below is the proposition's first clause granted exactly that limit,
whatever its value: it takes the limit `V` of the sums of squares as a
hypothesis and produces the convergence in distribution of the pairing to the
centred Gaussian of variance `(∫ z^2 dν) V`.  Nothing else about the weight, the
test function or the dimension is used, and the proof is the paper's, with the
local central limit theorem removed.
-/
import Sandpile.Support.ContWeightedCoeff
import Sandpile.Support.ContSeqCLT

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The sites whose cells meet the support of a test function supported in the
ball of radius `L`. -/
noncomputable def supportBox (d : ℕ) (R L : ℝ) : Finset (Site d) :=
  Sandpile.boxFinset (0 : Site d) (⌈|R| * L⌉₊ + 1)

/-- The sites the coefficients of the pairing are supported in: the walk moves
at most the horizon away from the cells of `supportBox`. -/
noncomputable def coeffBox (d : ℕ) (R L T : ℝ) : Finset (Site d) :=
  Sandpile.boxFinset (0 : Site d) (⌈|R| * L⌉₊ + 1 + ⌊R ^ 2 * T⌋₊)

/-- The coefficient `a_R(z)` of `sandpile.tex:4713`, with the diffusive
prefactor `R^{(d-4)/2}` and the horizon `⌊R^2T⌋`. -/
noncomputable def scaledCoeff (d : ℕ) (R L T : ℝ) (q : ℝ → ℝ) (φ : Space d → ℝ)
    (z : Site d) : ℝ :=
  R ^ (((d : ℝ) - 4) / 2) *
    pairCoeff d R (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊ φ (supportBox d R L) z

/-- The coefficients live on `coeffBox`: the weighted kernel reaches at most the
horizon from the cells the test function meets. -/
theorem scaledCoeff_eq_zero_of_notMem (R L T : ℝ) (q : ℝ → ℝ) (φ : Space d → ℝ)
    {z : Site d} (hz : z ∉ coeffBox d R L T) : scaledCoeff d R L T q φ z = 0 := by
  have hfar : ∀ x ∈ supportBox d R L, ⌊R ^ 2 * T⌋₊ < Sandpile.boxDist x z := by
    intro x hx
    by_contra hle
    exact hz (boxFinset_subset_of_mem _ _ hx (Sandpile.mem_boxFinset (not_lt.mp hle)))
  rw [scaledCoeff, pairCoeff_eq_zero_of_far R _ _ φ _ z hfar, mul_zero]

/-- So the sum over `coeffBox` in the hypothesis below is the TOTAL sum of
squares of the coefficients, which by `variance_scaled_pairing` is the variance
of the rescaled pairing divided by the scenery variance. -/
theorem tsum_scaledCoeff_sq (R L T : ℝ) (q : ℝ → ℝ) (φ : Space d → ℝ) :
    ∑' z : Site d, scaledCoeff d R L T q φ z ^ 2
      = ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2 := by
  refine tsum_eq_sum fun z hz => ?_
  rw [scaledCoeff_eq_zero_of_notMem R L T q φ hz]
  ring

/-- The rescaled pairing of the time-weighted membrane field with a test
function, written out. -/
theorem scaled_pairing_eq (R L T : ℝ) (q : ℝ → ℝ) (φ : Space d → ℝ)
    (hint : Integrable φ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) (ζ : Site d → ℝ) :
    R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] ζ) x) φ
      = ∑ i : Fin (coeffBox d R L T).card,
          (R ^ (((d : ℝ) - 4) / 2) *
            pairCoeff d R (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊ φ
              (supportBox d R L) (siteEnum (coeffBox d R L T) i)) *
            ζ (siteEnum (coeffBox d R L T) i) := by
  have hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ supportBox d R L :=
    fun z hz => floor_mem_boxFinset R z (hsupp z hz)
  have hs' : ∀ x ∈ supportBox d R L,
      Sandpile.boxFinset x ⌊R ^ 2 * T⌋₊ ⊆ coeffBox d R L T :=
    fun x hx => boxFinset_subset_of_mem _ _ hx
  rw [show (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] ζ) x)
      = weightedField (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊ ζ from rfl,
    latticePairing_weightedField_eq R _ _ ζ φ hint _ hs _ hs', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The convergence half of `prop:weighted-membrane-limit`, granted the limit
of the sums of squares of the coefficients.**  The hypothesis `hcov` is the
paper's `Var(𝓕_R(φ)) → Var(𝓖(φ))` divided by the scenery variance, which is what
the local central limit theorem and the Riemann-sum argument of
`sandpile.tex:4719-4724` supply; everything else in the proof of the
proposition is discharged here. -/
theorem weighted_pairing_tendsto_of_covariance (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    (q : ℝ → ℝ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQbd : ∀ r : ℝ, |q r| ≤ Q)
    (φ : Space d → ℝ) (C L : ℝ) (hC0 : 0 ≤ C)
    (hCbd : ∀ z, |φ z| ≤ C) (hsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ L) (hint : Integrable φ)
    (V : ℝ)
    (hcov : Tendsto (fun R : ℝ => ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2)
      atTop (𝓝 V)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * V))) := by
  classical
  have he : ∀ R : ℝ, Function.Injective (siteEnum (coeffBox d R L T)) :=
    fun R => siteEnum_injective _
  have hbd : ∀ R : ℝ, 0 < R → ∀ z : Site d,
      |scaledCoeff d R L T q φ z| ≤ Q * C * T * R ^ (-(d : ℝ) / 2) := by
    intro R hR z
    exact abs_scaled_pairCoeff_le hd hR hT _ Q (fun j _ => hQbd _) hQ0 φ C hCbd hC0 _ z
  have hdpos : (0 : ℝ) < (d : ℝ) / 2 := by
    have h : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hzero : Tendsto (fun R : ℝ => Q * C * T * R ^ (-(d : ℝ) / 2)) atTop (𝓝 0) := by
    simp only [neg_div]
    simpa using (tendsto_rpow_neg_atTop hdpos).const_mul (Q * C * T)
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop,
      ∀ i : Fin (coeffBox d R L T).card,
        |scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i)| ≤ δ := by
    intro δ hδ
    have h1 : ∀ᶠ R : ℝ in atTop, Q * C * T * R ^ (-(d : ℝ) / 2) < δ :=
      hzero.eventually (eventually_lt_nhds hδ)
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with R hR1 hR0 i
    exact le_trans (hbd R hR0 _) hR1.le
  have hQlim : Tendsto (fun R : ℝ => ∑ i : Fin (coeffBox d R L T).card,
      scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i) ^ 2) atTop (𝓝 V) := by
    have hsum : ∀ R : ℝ, ∑ i : Fin (coeffBox d R L T).card,
        scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i) ^ 2
        = ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2 :=
      fun R => sum_siteEnum (coeffBox d R L T) fun z => scaledCoeff d R L T q φ z ^ 2
    simpa only [hsum] using hcov
  have hrep : (fun (R : ℝ) (σ : Site d → ℝ) =>
      R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      = fun (R : ℝ) (σ : Site d → ℝ) => ∑ i : Fin (coeffBox d R L T).card,
          scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i) *
            Sandpile.scenery d σ (siteEnum (coeffBox d R L T) i) := by
    funext R σ
    exact scaled_pairing_eq R L T q φ hint hsupp (Sandpile.scenery d σ)
  rw [hrep]
  exact tendstoInDistribution_linear_pick_mass hd ν hsq hmean
    (fun R => (coeffBox d R L T).card)
    (fun R i => scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i))
    (fun R => siteEnum (coeffBox d R L T)) he hsmall V hQlim

/-- For a centred law the variance is the second moment, which is how the
scenery variance of the paper's covariance enters the Gaussian limit. -/
theorem variance_eq_second_moment (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0) :
    variance (id : ℝ → ℝ) ν = ∫ z, z ^ 2 ∂ν := by
  rw [ProbabilityTheory.variance_eq_integral hsq.aemeasurable]
  simp [hmean]

/-- The reduction with the limit variance written in the paper's normalization,
the scenery variance times the limit of the sums of squares. -/
theorem weighted_pairing_tendsto_of_covariance' (hd : 1 ≤ d) {T : ℝ} (hT : 0 ≤ T)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    (q : ℝ → ℝ) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQbd : ∀ r : ℝ, |q r| ≤ Q)
    (φ : Space d → ℝ) (C L : ℝ) (hC0 : 0 ≤ C)
    (hCbd : ∀ z, |φ z| ≤ C) (hsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ L) (hint : Integrable φ)
    (V : ℝ)
    (hcov : Tendsto (fun R : ℝ => ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2)
      atTop (𝓝 V)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal (variance (id : ℝ → ℝ) ν * V))) := by
  rw [variance_eq_second_moment ν hsq hmean]
  exact weighted_pairing_tendsto_of_covariance hd hT ν hsq hmean q Q hQ0 hQbd φ C L hC0
    hCbd hsupp hint V hcov

/-- The variance of the rescaled pairing is the scenery variance times the sum of
squares of the coefficients.  So the hypothesis `hcov` of the two theorems above
is exactly the paper's `Var(𝓕_R(φ)) → Var(𝓖(φ))` divided by `Var(ζ(0))`. -/
theorem variance_scaled_pairing (hd : 1 ≤ d) (R L T : ℝ) (q : ℝ → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (φ : Space d → ℝ) (hint : Integrable φ) (hsupp : ∀ z, φ z ≠ 0 → ‖z‖ ≤ L) :
    variance (fun σ : Site d → ℝ =>
        R ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing R
            (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
        (Sandpile.centeredMassLaw d ν)
      = variance (id : ℝ → ℝ) ν *
          ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2 := by
  have hrep : (fun σ : Site d → ℝ =>
      R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((j : ℝ) / R ^ 2) * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)
      = fun σ : Site d → ℝ => ∑ i : Fin (coeffBox d R L T).card,
          scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i) *
            Sandpile.scenery d σ (siteEnum (coeffBox d R L T) i) := by
    funext σ
    exact scaled_pairing_eq R L T q φ hint hsupp (Sandpile.scenery d σ)
  have hmp : MeasurePreserving (Sandpile.scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨Sandpile.measurable_scenery d, Sandpile.map_scenery_centeredMassLaw d ν hd⟩
  have hm : Measurable (fun ζ : Site d → ℝ => ∑ i : Fin (coeffBox d R L T).card,
      scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i) *
        ζ (siteEnum (coeffBox d R L T) i)) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply _)
  rw [hrep, hmp.variance_fun_comp hm.aemeasurable, ← covariance_self hm.aemeasurable,
    covariance_linear_pick ν hsq (siteEnum (coeffBox d R L T)) (siteEnum_injective _)
      (fun i => scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i))
      (fun i => scaledCoeff d R L T q φ (siteEnum (coeffBox d R L T) i)), mul_comm]
  congr 1
  rw [← sum_siteEnum (coeffBox d R L T) fun z => scaledCoeff d R L T q φ z ^ 2]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

end Sandpile.Support
