import Sandpile.Support.EventBridge
import Sandpile.Support.GaussPersist
import Sandpile.Support.Spectral
import Sandpile.Support.ScaleRates
import Sandpile.Support.ThirdMoment

/-!
# The two-term bound at a fixed set of geometric scales

This is the probabilistic core of `thm:critical-toppling`. Testing the odometer against the
membrane field at the times `n_j = N q^j` puts the lower event inside an orthant of the
standardized fields; the multivariate Berry-Esseen comparison replaces that orthant probability
by the Gaussian one at the cost of the third absolute moment of the coefficients; the covariance
matrix is nearly isotropic once `q` is large, so the Gaussian orthant is at most `κ^m` with
`κ < 1` (`gaussian_orthant_le_kappa`); and the third moment is the sum over the scales of the
Green supremum against its own standard deviation. `exists_critical_scale_bound` assembles these
into the two-term bound. What is left after this is real arithmetic in `t` and `L`: the choice
of `N`, the count `m` of scales, the verification that the thresholds are below one, and the
passage from `κ^m` to `L^{-c}`.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.External.BerryEsseen
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The Gaussian side of `thm:critical-toppling`**: at the geometric scales
and with the thresholds below one, the centred Gaussian with the covariance of
the standardized membrane fields gives the orthant at most `κ^m`. -/
theorem gaussian_orthant_le_kappa (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hcorr : ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      (∑' x : Site d, greenTime d m 0 x * greenTime d n 0 x) ≤
        C * Sandpile.External.Variance.corrRate d m n *
          Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
          Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2))
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hr : geomRatio q ≤ 1 / 2) (hρ : 12 * C * geomRatio q ≤ persistDelta)
    {m : ℕ} {s : Finset (Site d)}
    (hsub : ∀ j : Fin m, boxFinset (0 : Site d) (N * q ^ (j : ℕ)) ⊆ s)
    (c : Fin m → ℝ) (hc : ∀ j, c j ≤ 1) :
    multivariateGaussian 0
        (Sandpile.External.BerryEsseen.gram ν
          (stdCoeff d ν s (fun j : Fin m => N * q ^ (j : ℕ))))
        {y : EuclideanSpace ℝ (Fin m) | ∀ j, y j ≤ c j}
      ≤ ENNReal.ofReal (persistKappa ^ m) := by
  have hbounds := fun v => gram_quadForm_bounds ν hvar hC hcorr hd hd3 hq hN hr hρ hsub v
  refine le_trans (measure_mono ?_)
    (multivariateGaussian_orthant_persist _
      (Sandpile.External.BerryEsseen.gram_posSemidef ν _)
      (fun v => (hbounds v).1) (fun v => (hbounds v).2))
  intro y hy j
  exact le_trans (hy j) (hc j)

end Sandpile

namespace Sandpile

variable {d : ℕ}

/-- **The two-term bound of `thm:critical-toppling` at a fixed set of geometric
scales**: the odometer's lower event is at most the Gaussian persistence
probability plus the Berry-Esseen remainder, and the remainder is the
third-moment rate of the standardized coefficients. -/
theorem exists_critical_scale_bound (hBE : Sandpile.External.MultivariateBerryEsseen)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {Mmom : ℝ} (hMmom : 0 < Mmom) :
    ∃ CBE : ℝ, 0 < CBE ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        0 < variance (id : ℝ → ℝ) ν → Integrable (fun z => |z| ^ 3) ν →
        ∫ z, |z| ^ 3 ∂ν ≤ Mmom * variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) →
        ∀ Ccor : ℝ, 0 ≤ Ccor →
          (∀ m n : ℕ, 1 ≤ m → m ≤ n →
            (∑' x : Site d, greenTime d m 0 x * greenTime d n 0 x) ≤
              Ccor * Sandpile.External.Variance.corrRate d m n *
                Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
                Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2)) →
        ∀ q N : ℕ, 1 ≤ q → 1 ≤ N → geomRatio q ≤ 1 / 2 →
          12 * Ccor * geomRatio q ≤ persistDelta →
        ∀ m t : ℕ, 1 ≤ m → (∀ j : Fin m, N * q ^ (j : ℕ) ≤ t) →
        ∀ s : Finset (Site d), (∀ j : Fin m, boxFinset (0 : Site d) (N * q ^ (j : ℕ)) ⊆ s) →
        ∀ Msup : Fin m → ℝ,
          (∀ (j : Fin m) (x : Site d), greenTime d (N * q ^ (j : ℕ)) 0 x ≤ Msup j) →
        ∀ h : ℝ, (∀ j : Fin m, h / membraneSd d ν (N * q ^ (j : ℕ)) ≤ 1) →
          (Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ h}).toReal
            ≤ persistKappa ^ m + CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
                (Real.sqrt (m : ℝ) *
                  ∑ j, Msup j / Real.sqrt (greenSq d (N * q ^ (j : ℕ)))) := by
  obtain ⟨CBE, hCBE, hBE'⟩ :=
    hBE Mmom persistDelta hMmom persistDelta_pos persistDelta_lt_one
  refine ⟨CBE, hCBE, ?_⟩
  intro ν hprob hmean hvar hint hmom Ccor hC hcorr q N hq hN hr hρ m t hm hnt s hsub
    Msup hMsup h hthr
  classical
  set ns : Fin m → ℕ := fun j => N * q ^ (j : ℕ) with hnsdef
  have hns : ∀ j : Fin m, 1 ≤ ns j := by
    intro j
    have h1 : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 := by ring
      _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul hN h1
  set a := stdCoeff d ν s ns with hadef
  set c : Fin m → ℝ := fun j => h / membraneSd d ν (ns j) with hcdef
  have hbounds := fun v => gram_quadForm_bounds ν hvar hC hcorr hd hd3 hq hN hr hρ hsub v
  -- the Berry-Esseen comparison
  have hcomp := hBE' s.card m hm ν hprob hmean hvar hint hmom a hbounds c
  -- the Gaussian side
  have hgauss : (multivariateGaussian 0 (Sandpile.External.BerryEsseen.gram ν a)
      {y : EuclideanSpace ℝ (Fin m) | ∀ j, y j ≤ c j}).toReal ≤ persistKappa ^ m := by
    have hle := gaussian_orthant_le_kappa ν hvar hC hcorr hd hd3 hq hN hr hρ hsub c hthr
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal (pow_nonneg persistKappa_pos.le m)] at this
  -- the third moment
  have hthird := third_moment_bound ν hvar hns hsub Msup hMsup
  -- the event bridge
  have hbridge : (Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ h}).toReal
      ≤ ((Measure.pi fun _ : Fin s.card => ν)
          {ξ | ∀ j, ∑ i, a i j * ξ i ≤ c j}).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_odometer_le_pi ν hd hvar hns hnt hsub h)
    exact measure_ne_top _ _
  have hmpow : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have habs := abs_le.mp hcomp
  have hstep : ((Measure.pi fun _ : Fin s.card => ν)
        {ξ | ∀ j, ∑ i, a i j * ξ i ≤ c j}).toReal
      ≤ persistKappa ^ m + CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
          (variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) *
            ∑ i : Fin s.card, coeffNorm a i ^ 3) := by
    have h1 := habs.2
    nlinarith [h1, hgauss]
  refine le_trans hbridge (le_trans hstep ?_)
  have hmul : CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
        (variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) * ∑ i : Fin s.card, coeffNorm a i ^ 3)
      ≤ CBE * (m : ℝ) ^ ((1 : ℝ) / 4) *
        (Real.sqrt (m : ℝ) * ∑ j, Msup j / Real.sqrt (greenSq d (ns j))) := by
    exact mul_le_mul_of_nonneg_left hthird (mul_nonneg hCBE.le hmpow)
  linarith

end Sandpile
