/-
Theorem 1.3(iii)(d) of `sandpile.tex` (`thm:main-explosion`, part (iii)(d),
`sandpile.tex:290-296`) from the sharper `thm:dgt4-many-limits`
(`sandpile.tex:5900-5928`), which is the paper's own derivation: the scenery,
the sequence of scales and the family of subsequential limits are exactly the
ones the sharper theorem produces, the index set is `[3/2,2]`, the assignment of
a covariance to an index is injective because the covariances already differ on
the diagonal, and convergence of the whole family is impossible because two of
its subsequences converge to centred Gaussians with different variances.

Two points need more than bookkeeping.

The tightness clause of Theorem 1.3(iii)(d) is asked of the WHOLE family, over
every scale `R ≥ 1`, whereas `thm:dgt4-many-limits` supplies it only along its
subsequence.  It is therefore taken from the odometer's own tightness,
`dgt4_odometer_tight'`, which needs two moments of the one-site law; both come
from the exponential moment the scenery carries.

Distinctness of the limit LAWS, which is what rules out convergence, is
distinctness of the variances `Real.toNNReal (K κ φ φ)`, and `Real.toNNReal`
identifies all nonpositive reals.  The diagonal of the covariance is
nonnegative, being the limit of the sums of squares of the coefficients of the
weighted field (`tendsto_sum_scaledCoeff_sq`), so distinct diagonal values stay
distinct after `Real.toNNReal`.
-/
import Sandpile.Support.ContNonconvergence
import Sandpile.Support.ContDGT4Membrane
import Sandpile.Support.ExponentialMoments
import Sandpile.Support.ExplFluctuation

open LatticeProb

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- Two nonnegative reals that differ still differ after `Real.toNNReal`. -/
theorem toNNReal_ne_of_ne {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    Real.toNNReal a ≠ Real.toNNReal b := by
  intro h
  exact hab (by rw [← Real.coe_toNNReal a ha, ← Real.coe_toNNReal b hb, h])

/-- Two centred real Gaussians with different variance parameters are different
measures.  The variance parameter is read back off the measure, so distinctness
of the parameters is distinctness of the laws, which is what "distinct
subsequential limits" asks for. -/
theorem gaussianReal_zero_ne_of_ne {v w : ℝ≥0} (h : v ≠ w) :
    gaussianReal 0 v ≠ gaussianReal 0 w := by
  intro hvw
  refine h (NNReal.coe_injective ?_)
  have hv : variance (id : ℝ → ℝ) (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have hw : variance (id : ℝ → ℝ) (gaussianReal 0 w) = (w : ℝ) := variance_id_gaussianReal
  rw [← hv, ← hw, hvw]

/-- The diagonal of the weighted membrane covariance is nonnegative: it is the
limit of the sums of squares of the coefficients of the weighted field. -/
theorem weightedMembraneCov_nonneg (hLCLT : Sandpile.External.LocalCLT)
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d)
    {κ T ν2 : ℝ} (hκ : 0 ≤ κ) (hT : 0 < T) (hν2 : 0 ≤ ν2)
    (φ : Space d → ℝ) (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    0 ≤ Sandpile.Continuum.weightedMembraneCov d ν2 κ T φ φ := by
  obtain ⟨C, L, hC0, hL0, hC, hsupp, hint⟩ := exists_bound_of_isTestFn hφ
  have hq : ContinuousOn (fun r : ℝ => (1 - r / T) ^ κ) (Set.Icc 0 T) :=
    ((Real.continuous_rpow_const hκ).comp
      (continuous_const.sub (continuous_id.div_const T))).continuousOn
  rw [Sandpile.Continuum.weightedMembraneCov]
  refine mul_nonneg hν2 ?_
  exact ge_of_tendsto' (tendsto_sum_scaledCoeff_sq hLCLT hHK hd hT _ hq φ hint hC hsupp)
    (fun R => Finset.sum_nonneg fun z _ => sq_nonneg _)

/-- The reindexed family of `thm:dgt4-many-limits` read at a natural number is
the diffusive fluctuation along the subsequence. -/
theorem diffusiveFluctuation_reindex (P : MeasureTheory.Measure (Sandpile.Site d → ℝ))
    (T : ℝ) (Rseq : ℕ → ℝ) (kl : ℕ → ℕ) (φ : Space d → ℝ) (k : ℕ)
    (σ : Sandpile.Site d → ℝ) :
    Rseq (kl ⌊(k : ℝ)⌋₊) ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing (Rseq (kl ⌊(k : ℝ)⌋₊))
          (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊(k : ℝ)⌋₊) ^ 2⌋₊ x -
            Sandpile.meanOdometer P ⌊T * Rseq (kl ⌊(k : ℝ)⌋₊) ^ 2⌋₊) φ
      = Sandpile.Continuum.diffusiveFluctuation P T (Rseq (kl k)) σ φ := by
  rw [Nat.floor_natCast]
  rfl

/-- **Theorem 1.3(iii)(d) from `thm:dgt4-many-limits`.**  The scenery, the scales
and the subsequential limits are the sharper theorem's; the index set is
`[3/2,2]`, the assignment of a covariance to an index is injective because the
covariances differ on the diagonal, and the family cannot converge because two of
its subsequences converge to centred Gaussians of different variances.  The
tightness clause is the odometer's own, since it is asked of the whole family. -/
theorem high_nonconvergence_of
    (hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hd : 5 ≤ d) (ν : MeasureTheory.Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (Rseq : ℕ → ℝ) (hRtop : Tendsto Rseq atTop atTop)
    (hsub : ∀ κ : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
      ∃ kl : ℕ → ℕ, StrictMono kl ∧
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Space d → ℝ) =>
              Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
                  (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                      ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T))
    (hdist : ∀ T : ℝ, 0 < T → ∀ κ κ' : ℝ, κ ∈ Set.Icc ((3 : ℝ) / 2) 2 →
      κ' ∈ Set.Icc ((3 : ℝ) / 2) 2 → κ ≠ κ' →
      ∃ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
        Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ ≠
          Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ' T φ φ)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : ((d : ℝ) - 4) / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s (Sandpile.centeredMassLaw d ν)
        (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) ∧
      (∃ (I : Set ℝ) (K : ℝ → (Space d → ℝ) → (Space d → ℝ) → ℝ),
        ¬ I.Countable ∧
          (∀ κ ∈ I, ∀ κ' ∈ I, κ ≠ κ' →
            ∃ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ ∧
              gaussianReal 0 (Real.toNNReal (K κ φ φ)) ≠
                gaussianReal 0 (Real.toNNReal (K κ' φ φ))) ∧
          ∀ κ ∈ I, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
            ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
              TendstoInDistribution
                (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
                  Sandpile.Continuum.diffusiveFluctuation
                    (Sandpile.centeredMassLaw d ν) T (Rs k) σ φ)
                atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
                (gaussianReal 0 (Real.toNNReal (K κ φ φ)))) ∧
      ¬ ∃ K : (Space d → ℝ) → (Space d → ℝ) → ℝ,
        Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
          (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) K := by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_exp hθ hexp
  have hmem2 : MemLp (id : ℝ → ℝ) 2 ν :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq
  have hposint : Integrable (fun z : ℝ => max z 0) ν := integrable_max_zero ν hmem2
  have hν2 : 0 ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  have hlim : ∀ κ ∈ Set.Icc ((3 : ℝ) / 2) 2, ∃ Rs : ℕ → ℝ, Tendsto Rs atTop atTop ∧
      ∀ φ : Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
        TendstoInDistribution
          (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
            Sandpile.Continuum.diffusiveFluctuation
              (Sandpile.centeredMassLaw d ν) T (Rs k) σ φ)
          atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
          (gaussianReal 0 (Real.toNNReal
            (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T φ φ))) := by
    intro κ hκ
    obtain ⟨kl, hkl, hconv⟩ := hsub κ hκ
    refine ⟨fun k => Rseq (kl k), hRtop.comp hkl.tendsto_atTop, ?_⟩
    intro φ hφ
    have h1 := (hconv T hT s hs).1 φ hφ
    have h2 := tendstoInDistribution_comp_atTop (Sandpile.centeredMassLaw d ν)
      (fun (L : ℝ) (σ : Sandpile.Site d → ℝ) =>
        Rseq (kl ⌊L⌋₊) ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (Rseq (kl ⌊L⌋₊))
            (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                ⌊T * Rseq (kl ⌊L⌋₊) ^ 2⌋₊) φ)
      _ (fun k : ℕ => (k : ℝ)) tendsto_natCast_atTop_atTop h1
    have heq : (fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
        Rseq (kl ⌊((k : ℕ) : ℝ)⌋₊) ^ (((d : ℝ) - 4) / 2) *
          Sandpile.Continuum.latticePairing (Rseq (kl ⌊((k : ℕ) : ℝ)⌋₊))
            (fun x => Sandpile.odometer σ ⌊T * Rseq (kl ⌊((k : ℕ) : ℝ)⌋₊) ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν)
                ⌊T * Rseq (kl ⌊((k : ℕ) : ℝ)⌋₊) ^ 2⌋₊) φ)
        = fun (k : ℕ) (σ : Sandpile.Site d → ℝ) =>
          Sandpile.Continuum.diffusiveFluctuation
            (Sandpile.centeredMassLaw d ν) T (Rseq (kl k)) σ φ := by
      funext k σ
      exact diffusiveFluctuation_reindex (Sandpile.centeredMassLaw d ν) T Rseq kl φ k σ
    exact heq ▸ h2
  refine ⟨dgt4_odometer_tight' hGreenHigh hBesov hd ν hsq hposint T hT s hs,
    ⟨Set.Icc ((3 : ℝ) / 2) 2,
      fun κ => Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T,
      not_countable_Icc_three_halves_two, ?_, hlim⟩, ?_⟩
  · intro κ hκ κ' hκ' hne
    obtain ⟨φ, hφ, hφne⟩ := hdist T hT κ κ' hκ hκ' hne
    exact ⟨φ, hφ, gaussianReal_zero_ne_of_ne (toNNReal_ne_of_ne
      (weightedMembraneCov_nonneg hLocalCLT hHeatKernel hd1
        (le_trans (by norm_num) hκ.1) hT hν2 φ hφ)
      (weightedMembraneCov_nonneg hLocalCLT hHeatKernel hd1
        (le_trans (by norm_num) hκ'.1) hT hν2 φ hφ) hφne)⟩
  · obtain ⟨φ, hφ, hne⟩ := hdist T hT ((3 : ℝ) / 2) 2
      (Set.left_mem_Icc.mpr (by norm_num)) (Set.right_mem_Icc.mpr (by norm_num))
      (by norm_num)
    obtain ⟨Rs, hRs, hRsconv⟩ := hlim ((3 : ℝ) / 2) (Set.left_mem_Icc.mpr (by norm_num))
    obtain ⟨Rs', hRs', hRs'conv⟩ := hlim 2 (Set.right_mem_Icc.mpr (by norm_num))
    exact not_exists_tendstoInNegSobolev_of_two_limits d s (Sandpile.centeredMassLaw d ν)
      (Sandpile.Continuum.diffusiveFluctuation (Sandpile.centeredMassLaw d ν) T) φ hφ _ _
      (toNNReal_ne_of_ne
        (weightedMembraneCov_nonneg hLocalCLT hHeatKernel hd1 (by norm_num) hT hν2 φ hφ)
        (weightedMembraneCov_nonneg hLocalCLT hHeatKernel hd1 (by norm_num) hT hν2 φ hφ) hne)
      Rs Rs' hRs hRs' (hRsconv φ hφ) (hRs'conv φ hφ)


end Sandpile.Support
