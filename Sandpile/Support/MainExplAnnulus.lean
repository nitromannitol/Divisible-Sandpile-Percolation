import Sandpile.Support.MainExplLattice
import Sandpile.Support.ExplWalkCutoff
import Sandpile.Support.ExplValueGap

/-!
# The field half of the cutoff error: the bound on the dyadic annuli

This is the field half of the cutoff error of `sandpile.tex:1908-1921`: the bound on the
dyadic annuli.

`Sandpile.Support.exists_walk_cutoff_stoppingSup_gap` turns a bound of the reward
by a fixed power of the radius on each dyadic annulus into the vanishing of the
cutoff error, uniformly over the scale, the starting point and the stopping time.
Its hypothesis `hV` is the only thing the unkilled route of `thm:main-explosion`
(i)(b) still has to supply, and here it is supplied with the power one, from the
linear envelope of the interpolated field: on the annulus of index `j` the radius
is at most `2^{j+1}A` and at least `A ≥ 1`, so the envelope `K(1+|y|)` is at most
`2K` times the radius. The failure probability is the one of the envelope, so it
is the accuracy asked for, uniformly in the scale.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile.Frozen.HeatPotentialInvariance

variable {d : ℕ}

/-- Every polynomial moment of the one-site law follows from the exponential moment the
paper assumes, because `x^n/n!` is one term of the exponential series. -/
theorem integrable_abs_rpow_of_exp (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (p : ℝ) (hp : 0 ≤ p) : Integrable (fun z : ℝ => |z| ^ p) ν := by
  classical
  set n : ℕ := ⌈p⌉₊ with hndef
  set C : ℝ := (Nat.factorial n : ℝ) / θ₀ ^ n with hCdef
  have hθn : (0:ℝ) < θ₀ ^ n := pow_pos hθ₀ n
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hdom : ∀ z : ℝ, |z| ^ p ≤ 1 + C * Real.exp (θ₀ * |z|) := by
    intro z
    have hexp0 : (0:ℝ) < Real.exp (θ₀ * |z|) := Real.exp_pos _
    rcases le_or_gt |z| 1 with h | h
    · have h1 : |z| ^ p ≤ 1 := Real.rpow_le_one (abs_nonneg z) h hp
      nlinarith
    · have h1 : (1:ℝ) ≤ |z| := h.le
      have h2 : |z| ^ p ≤ |z| ^ ((n : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
      have h3 : |z| ^ ((n : ℕ) : ℝ) = |z| ^ n := Real.rpow_natCast _ _
      have h4 : (θ₀ * |z|) ^ n / (Nat.factorial n : ℝ) ≤ Real.exp (θ₀ * |z|) :=
        Real.pow_div_factorial_le_exp (θ₀ * |z|) (by positivity) n
      have h5 : (θ₀ * |z|) ^ n = θ₀ ^ n * |z| ^ n := mul_pow _ _ _
      have hfac : (0:ℝ) < (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have h6 : |z| ^ n ≤ C * Real.exp (θ₀ * |z|) := by
        rw [hCdef]
        rw [h5, div_le_iff₀ hfac] at h4
        rw [div_mul_eq_mul_div, le_div_iff₀ hθn]
        nlinarith
      rw [h3] at h2
      nlinarith
  refine Integrable.mono' ((integrable_const (1:ℝ)).add (hexp.const_mul C)) ?_ ?_
  · exact (Continuous.rpow_const continuous_abs (fun _ => Or.inr hp)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) p)]
    exact hdom z


/-- **The dyadic-annulus bound for the interpolated rescaled field, with power one and one
amplitude at every scale.**  Outside an event of the prescribed probability, and for every
cutoff radius at least one, the field on the `j`-th dyadic annulus is at most `K` times the
outer radius of that annulus.  This is the hypothesis `hV` of
`exists_walk_cutoff_stoppingSup_gap` and of `exists_walk_cutoff_error_of_annulus_bound`. -/
theorem exists_field_annulus_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∃ G : Set (Site d → ℝ),
      Sandpile.centeredMassLaw d ν Gᶜ ≤ ENNReal.ofReal δ ∧
      ∀ σ ∈ G, ∀ A : ℝ, 1 ≤ A → ∀ r : ℝ, 0 ≤ r → r ≤ T →
        ∀ (y : Sandpile.Continuum.Space d) (j : ℕ), y ∈ Sandpile.Continuum.dyadicAnnulus A j →
          |linInterp d R (Sandpile.scenery d σ) r y| ≤ K * (2 ^ (j + 1) * A) ^ (1 : ℕ) := by
  classical
  set β : ℝ := min (1 - (d : ℝ) / 4) ((1 - θ) / 4) with hβdef
  have hdr : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hβ0 : (0:ℝ) < β := lt_min (by linarith) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (((d : ℝ) + 1) / β) ((d : ℝ) + 1))
  set p : ℝ := (N : ℝ) + 2 with hpdef
  have hp : (2:ℝ) ≤ p := by
    have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [hpdef]; linarith
  have hNle : max (((d : ℝ) + 1) / β) ((d : ℝ) + 1) < (N : ℝ) := hN
  have hpd : (d : ℝ) + 1 < p := by
    have h := le_trans (le_max_right (((d : ℝ) + 1) / β) ((d : ℝ) + 1)) hNle.le
    rw [hpdef]; linarith
  have hq : ((d : ℝ) + 1) < p * β := by
    have h : ((d : ℝ) + 1) / β < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hNle
    have h2 : ((d : ℝ) + 1) < (N : ℝ) * β := by
      rw [div_lt_iff₀ hβ0] at h
      exact h
    have h3 : (N : ℝ) * β ≤ p * β := by
      have : (N : ℝ) ≤ p := by rw [hpdef]; linarith
      exact mul_le_mul_of_nonneg_right this hβ0.le
    linarith
  obtain ⟨K₀, hK₀, henv⟩ := exists_global_envelope hHK hd hd3 hθ0 hθ1 p hp hpd hq T hT ν
    hmean (integrable_abs_rpow_of_exp ν hθ₀ hexp p (by linarith)) δ hδ
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro R hR
  refine ⟨{σ : Site d → ℝ | ∀ r ∈ Set.Icc (0:ℝ) T, ∀ w : Sandpile.Continuum.Space d,
      |linInterp d R (Sandpile.scenery d σ) r w| ≤ K₀ * (1 + ‖w‖)}, ?_, ?_⟩
  · refine le_trans (measure_mono ?_) (henv R hR)
    intro σ hσ
    by_contra hcon
    exact hσ (fun r hr w => not_lt.mp (fun hlt => hcon ⟨r, hr, w, hlt⟩))
  · intro σ hσ A hA r hr0 hrT y j hy
    have hbound := hσ r ⟨hr0, hrT⟩ y
    have houter : ‖y‖ < 2 ^ (j + 1) * A := hy.2
    have hA1 : (1:ℝ) ≤ 2 ^ (j + 1) * A := by
      have h1 : (1:ℝ) ≤ (2:ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have : K₀ * (1 + ‖y‖) ≤ 2 * K₀ * (2 ^ (j + 1) * A) := by nlinarith
    simpa only [pow_one] using le_trans hbound this

/-- **The dyadic-annulus bound for the mesh reward of the exact identity.**  This is the
hypothesis `hV` of `exists_walk_cutoff_stoppingSup_gap` at the reward the exact identity of
`sandpile.tex:1881-1890` produces, with power one; supplying it is what the unkilled route of
`thm:main-explosion`(i)(b) needed and the cube-killed route of `rem:dlt4-killed-scaling` got
for free from the confinement of the walk. -/
theorem exists_mesh_annulus_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∃ G : Set (Site d → ℝ),
      Sandpile.centeredMassLaw d ν Gᶜ ≤ ENNReal.ofReal δ ∧
      ∀ σ ∈ G, ∀ A : ℝ, 1 ≤ A → ∀ t : ℕ, (t : ℝ) ≤ R ^ 2 * T →
        ∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ t) → ∀ (X : ℕ → Site d) (j : ℕ),
          External.Lclt.scaledSite R (X (τ X)) ∈ Sandpile.Continuum.dyadicAnnulus A j →
          |(-Frozen.HeatPotentialInvariance.meshValue d R (Sandpile.scenery d σ)
              (t - τ X) (X (τ X)))| ≤ K * (2 ^ (j + 1) * A) ^ (1 : ℕ) := by
  obtain ⟨K, hK, hfield⟩ := exists_field_annulus_bound hHK hd hd3 hθ0 hθ1 ν hmean hθ₀ hexp
    T hT δ hδ
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨G, hGmeas, hG⟩ := hfield R hR
  refine ⟨G, hGmeas, ?_⟩
  intro σ hσ A hA t htT τ hτ X j hj
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hRne : R ≠ 0 := ne_of_gt hR0
  have hrep := Sandpile.linInterp_scaledSite R hRne (Sandpile.scenery d σ) t (τ X) (hτ X)
    (X (τ X))
  have hr0 : (0:ℝ) ≤ ((t : ℝ) - (τ X : ℝ)) / R ^ 2 := by
    have : ((τ X : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hτ X
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    exact div_nonneg (by linarith) hR2.le
  have hrT : ((t : ℝ) - (τ X : ℝ)) / R ^ 2 ≤ T := by
    have hR2 : (0:ℝ) < R ^ 2 := by positivity
    rw [div_le_iff₀ hR2]
    have hτ0 : (0:ℝ) ≤ ((τ X : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (t : ℝ) - (τ X : ℝ) ≤ (t : ℝ) := by linarith
      _ ≤ R ^ 2 * T := htT
      _ = T * R ^ 2 := by ring
  have h := hG σ hσ A hA (((t : ℝ) - (τ X : ℝ)) / R ^ 2) hr0 hrT
    (External.Lclt.scaledSite R (X (τ X))) j hj
  rw [abs_neg]
  rwa [hrep] at h

end Sandpile.Support
