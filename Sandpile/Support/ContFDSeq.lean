/-
The finite-dimensional heat-potential limit along a SEQUENCE of laws.

Every finite-dimensional convergence in this development fixes one law:
`heat_potential_fd_of_continuum`, `heat_potential_fd_of`,
`tendstoInDistribution_vector_pick_mass` and `weighted_iid_central_limit_pick` all
conclude at `fun _ => centeredMassLaw d ν`.  The sequential step of the dimension
two and three percolation theorem needs the same limit along laws `ν n` that vary
with the scale, and the Lindeberg step underneath does not uniformise: it goes
through a characteristic-function estimate that is a little-o at a single law.

This is the paper's own statement along a sequence, not a result from the
literature, so it is ordinary support.  What makes it available is the common
exponential moment: the sequence is assumed to carry one bound `K₀` at one rate
`θ₀`, which gives a cubic remainder in the characteristic function uniform in `n`,
and that is exactly what the single-law estimate lacks.

The coefficient inputs do not depend on the law.  They should be reused from the
fixed-law proof rather than rebuilt: only the Lindeberg step changes.
-/
import Sandpile.Support.ContFDFromContinuum
import Sandpile.Support.ExponentialMoments
import Sandpile.Support.ExpMomentRpow

open LatticeProb.CramerWold

open LatticeProb

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The uniform characteristic-function estimate -/

/-- A crude third-order Taylor bound for `exp (i x)`, valid for every real `x`. -/
private theorem norm_exp_mul_I_taylor_le (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have hn : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
    have h := Complex.exp_bound (x := (x : ℂ) * Complex.I) (by rw [hn]; exact hx) (n := 3)
      (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
        = 1 + x * Complex.I - (x : ℂ) ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial, mul_pow]
      ring
    rw [hs, hn] at h
    refine h.trans ?_
    have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))⁻¹ ≤ 4 := by
      norm_num [Nat.factorial]
    calc |x| ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))⁻¹)
        ≤ |x| ^ 3 * 4 := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 4 * |x| ^ 3 := by ring
  · have hx := not_le.mp hx
    have h1 : 1 ≤ |x| ^ 3 := one_le_pow₀ hx.le
    have h1' : 1 ≤ |x| ^ 2 := one_le_pow₀ hx.le
    have h2 : |x| ≤ |x| ^ 3 := by
      calc |x| = |x| * 1 := (mul_one _).symm
        _ ≤ |x| * |x| ^ 2 := mul_le_mul_of_nonneg_left h1' (abs_nonneg x)
        _ = |x| ^ 3 := by ring
    have h3 : |x| ^ 2 ≤ |x| ^ 3 := by
      calc |x| ^ 2 = |x| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |x| ^ 2 * |x| := mul_le_mul_of_nonneg_left hx.le (by positivity)
        _ = |x| ^ 3 := by ring
    have hE : ‖Complex.exp (x * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have hP : ‖1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖ ≤ 1 + |x| + |x| ^ 2 / 2 := by
      calc ‖1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖
          ≤ ‖1 + (x : ℂ) * Complex.I‖ + ‖(x : ℂ) ^ 2 / 2‖ := norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖) + ‖(x : ℂ) ^ 2 / 2‖ := by
          gcongr
          exact norm_add_le _ _
        _ = 1 + |x| + |x| ^ 2 / 2 := by simp
    calc ‖Complex.exp (x * Complex.I) - (1 + x * Complex.I - (x : ℂ) ^ 2 / 2)‖
        ≤ ‖Complex.exp (x * Complex.I)‖ + ‖1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖ :=
          norm_sub_le _ _
      _ ≤ 1 + (1 + |x| + |x| ^ 2 / 2) := by rw [hE]; gcongr
      _ ≤ 4 * |x| ^ 3 := by nlinarith

/-- **The cubic remainder of the characteristic function, uniform over the class.**
For a centred law with exponential moment `K` at rate `θ`, the characteristic function
differs from `1 - (∫ z ^ 2 ∂ν) t ^ 2 / 2` by at most `C |t| ^ 3`, where `C` depends on
`θ` and `K` alone.  This is the estimate the single-law `charFun_second_order` lacks:
there the remainder is a little-o at one law, here it is a cubic bound that is the
same for every law of the sequence. -/
private theorem charFun_cubic_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ K : ℝ) (hθ : 0 < θ) (hmean : ∫ z, z ∂ν = 0)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hK : ∫ z, Real.exp (θ * |z|) ∂ν ≤ K) (t : ℝ) :
    ‖charFun ν t - (1 - ((∫ z, z ^ 2 ∂ν : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)‖
      ≤ 4 * ((3 / θ) ^ (3 : ℝ) * K) * |t| ^ 3 := by
  have hi1 : Integrable (fun z : ℝ => (z : ℂ)) ν :=
    (LatticeProb.integrable_id_of_exp_moment ν θ hθ hexp).ofReal
  have hi2 : Integrable (fun z : ℝ => ((z ^ 2 : ℝ) : ℂ)) ν :=
    (LatticeProb.integrable_sq_of_exp hθ hexp).ofReal
  have hi3 : Integrable (fun z : ℝ => |z| ^ (3 : ℝ)) ν :=
    Sandpile.integrable_abs_rpow_of_exp_moment ν θ hθ hexp 3 (by norm_num)
  have hiE : Integrable (fun z : ℝ => Complex.exp (t * z * Complex.I)) ν := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun z => ?_)
    have : (t : ℂ) * z * Complex.I = ((t * z : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  set f : ℝ → ℂ := fun z =>
    Complex.exp (t * z * Complex.I) - (1 + (t * z : ℝ) * Complex.I - ((t * z : ℝ) : ℂ) ^ 2 / 2)
    with hf
  have hfint : Integrable f ν := by
    refine hiE.sub ?_
    refine ((integrable_const (1 : ℂ)).add ?_).sub ?_
    · have := (hi1.const_mul ((t : ℂ) * Complex.I))
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Complex.ofReal_mul]
      ring
    · have := (hi2.const_mul ((t : ℂ) ^ 2 / 2))
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [Complex.ofReal_mul, Complex.ofReal_pow]
      ring
  have hint : ∫ z, f z ∂ν
      = charFun ν t - (1 - ((∫ z, z ^ 2 ∂ν : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    have hm : ∫ z : ℝ, (z : ℂ) ∂ν = 0 :=
      (integral_ofReal (𝕜 := ℂ) (μ := ν) (f := fun z : ℝ => z)).trans (by rw [hmean]; simp)
    have hm2 : ∫ z : ℝ, ((z ^ 2 : ℝ) : ℂ) ∂ν = ((∫ z : ℝ, z ^ 2 ∂ν : ℝ) : ℂ) :=
      integral_ofReal (𝕜 := ℂ) (μ := ν) (f := fun z : ℝ => z ^ 2)
    have hexpand : f = fun z : ℝ => Complex.exp (t * z * Complex.I) - (1 : ℂ)
        - ((t : ℂ) * Complex.I) * (z : ℂ) + ((t : ℂ) ^ 2 / 2) * ((z ^ 2 : ℝ) : ℂ) := by
      funext z
      simp only [hf, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [hexpand]
    beta_reduce
    have hA : Integrable (fun z : ℝ => Complex.exp (t * z * Complex.I) - (1 : ℂ)) ν :=
      hiE.sub (integrable_const _)
    have hB : Integrable (fun z : ℝ => ((t : ℂ) * Complex.I) * (z : ℂ)) ν := hi1.const_mul _
    have hC : Integrable (fun z : ℝ => ((t : ℂ) ^ 2 / 2) * ((z ^ 2 : ℝ) : ℂ)) ν :=
      hi2.const_mul _
    have hAB : Integrable (fun z : ℝ => Complex.exp (t * z * Complex.I) - (1 : ℂ)
        - ((t : ℂ) * Complex.I) * (z : ℂ)) ν := hA.sub hB
    rw [integral_add hAB hC, integral_sub hA hB, integral_sub hiE (integrable_const _),
      integral_const_mul, integral_const_mul, hm, hm2, charFun_apply_real]
    simp
    ring
  have hbound : ∀ z, ‖f z‖ ≤ 4 * |t| ^ 3 * |z| ^ (3 : ℝ) := by
    intro z
    have h := norm_exp_mul_I_taylor_le (t * z)
    have hz : (t : ℂ) * z * Complex.I = ((t * z : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [hf, hz]
    refine h.trans ?_
    rw [abs_mul, mul_pow, show (|z| ^ (3 : ℝ)) = |z| ^ 3 from by
      rw [← Real.rpow_natCast]; norm_num]
    ring_nf
    exact le_rfl
  have hmom : ∫ z, |z| ^ (3 : ℝ) ∂ν ≤ (3 / θ) ^ (3 : ℝ) * K := by
    calc (∫ z, |z| ^ (3 : ℝ) ∂ν) ≤ ∫ z, (3 / θ) ^ (3 : ℝ) * Real.exp (θ * |z|) ∂ν := by
          apply integral_mono hi3 (hexp.const_mul _)
          intro z
          simpa only [abs_of_pos hθ] using
            rpow_abs_le_mul_exp_abs z (show (0 : ℝ) ≤ 3 by norm_num) hθ.ne'
      _ = (3 / θ) ^ (3 : ℝ) * ∫ z, Real.exp (θ * |z|) ∂ν := integral_const_mul _ _
      _ ≤ (3 / θ) ^ (3 : ℝ) * K := mul_le_mul_of_nonneg_left hK (by positivity)
  rw [← hint]
  calc ‖∫ z, f z ∂ν‖ ≤ ∫ z, 4 * |t| ^ 3 * |z| ^ (3 : ℝ) ∂ν :=
        norm_integral_le_of_norm_le (hi3.const_mul _) (Filter.Eventually.of_forall hbound)
    _ = 4 * |t| ^ 3 * ∫ z, |z| ^ (3 : ℝ) ∂ν := integral_const_mul _ _
    _ ≤ 4 * |t| ^ 3 * ((3 / θ) ^ (3 : ℝ) * K) :=
        mul_le_mul_of_nonneg_left hmom (by positivity)
    _ = 4 * ((3 / θ) ^ (3 : ℝ) * K) * |t| ^ 3 := by ring

/-- **The Gaussian comparison, uniform over the class.**  Along a sequence of centred laws
with a common exponential moment and variances converging to `v`, the characteristic
function is within `ε u ^ 2` of the Gaussian one at variance `v`, for all `|u| ≤ δ`, for
all large `n`, with `δ` independent of `n`. -/
private theorem charFun_gaussian_uniform_littleO (θ K v : ℝ) (hθ : 0 < θ) (hv : 0 < v)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ * |z|)) (ν n))
    (hK : ∀ n, ∫ z, Real.exp (θ * |z|) ∂(ν n) ≤ K)
    (hvar : Tendsto (fun n => ∫ z, z ^ 2 ∂(ν n)) atTop (𝓝 v)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ δ →
      ‖charFun (ν n) u - Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)‖ ≤ ε * u ^ 2 := by
  have hK0 : 0 ≤ K := (integral_nonneg fun z => (Real.exp_pos _).le).trans (hK 0)
  set C : ℝ := 4 * ((3 / θ) ^ (3 : ℝ) * K) with hCdef
  have hC : 0 ≤ C := by positivity
  set δ : ℝ := min 1 (min (1 / (v + 1)) (ε / (4 * (C + v ^ 2 + 1)))) with hδdef
  have hδ : 0 < δ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (v + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ ε / (4 * (C + v ^ 2 + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hδ2' : δ * (v + 1) ≤ 1 := by
    have := (le_div_iff₀ (show (0 : ℝ) < v + 1 by positivity)).mp hδ2
    exact this
  have hδ3' : (C + v ^ 2 + 1) * δ ≤ ε / 4 := by
    have := (le_div_iff₀ (show (0 : ℝ) < 4 * (C + v ^ 2 + 1) by positivity)).mp hδ3
    linarith
  have hCδ : C * δ ≤ ε / 4 := by nlinarith [sq_nonneg v]
  have hvδ : v ^ 2 * δ ≤ ε / 4 := by nlinarith [sq_nonneg v]
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hvar.eventually (Metric.ball_mem_nhds v (half_pos hε))] with n hn u hu
  have hσ : |(∫ z, z ^ 2 ∂(ν n)) - v| < ε / 2 := by
    rwa [Real.dist_eq] at hn
  set σ : ℝ := ∫ z, z ^ 2 ∂(ν n) with hσdef
  have hcb := charFun_cubic_bound (ν n) θ K hθ (hmean n) (hexp n) (hK n) u
  have hu1 : |u| ≤ 1 := hu.trans hδ1
  have hu2 : u ^ 2 ≤ δ := by
    calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
      _ = |u| * |u| := sq _
      _ ≤ 1 * δ := mul_le_mul hu1 hu (abs_nonneg u) zero_le_one
      _ = δ := one_mul _
  have hu3 : |u| ^ 3 ≤ δ * u ^ 2 := by
    rw [show |u| ^ 3 = |u| * u ^ 2 by rw [← sq_abs u]; ring]
    exact mul_le_mul_of_nonneg_right hu (sq_nonneg u)
  have hz : v * u ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg u]
  -- the three comparisons
  have hzeq : -(v : ℂ) * (u : ℂ) ^ 2 / 2 = ((-(v * u ^ 2 / 2) : ℝ) : ℂ) := by push_cast; ring
  have hznorm : ‖-(v : ℂ) * (u : ℂ) ^ 2 / 2‖ = v * u ^ 2 / 2 := by
    rw [hzeq, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
  have h3 : ‖(1 - (v : ℂ) * (u : ℂ) ^ 2 / 2) - Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)‖
      ≤ (v * u ^ 2 / 2) ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le
      (x := -(v : ℂ) * (u : ℂ) ^ 2 / 2) (by rw [hznorm]; linarith)
    rw [hznorm] at h
    have heq : (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2) - Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)
        = -(Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2) - 1 - (-(v : ℂ) * (u : ℂ) ^ 2 / 2)) := by
      ring
    rw [heq, norm_neg]
    exact h
  have h2 : ‖(1 - (σ : ℂ) * (u : ℂ) ^ 2 / 2) - (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2)‖
      ≤ (ε / 4) * u ^ 2 := by
    have heq : (1 - (σ : ℂ) * (u : ℂ) ^ 2 / 2) - (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2)
        = (((v - σ) * u ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_sq,
      abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_sub_comm]
    have := mul_le_mul_of_nonneg_right hσ.le (sq_nonneg u)
    nlinarith
  have h3' : (v * u ^ 2 / 2) ^ 2 ≤ (v ^ 2 * δ / 4) * u ^ 2 := by
    have : (v * u ^ 2 / 2) ^ 2 = (v ^ 2 / 4) * u ^ 2 * u ^ 2 := by ring
    rw [this]
    have h4 : u ^ 2 * u ^ 2 ≤ δ * u ^ 2 := mul_le_mul_of_nonneg_right hu2 (sq_nonneg u)
    nlinarith [sq_nonneg v]
  have hsplit := norm_sub_le_norm_sub_add_norm_sub (charFun (ν n) u)
    (1 - (σ : ℂ) * (u : ℂ) ^ 2 / 2) (Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))
  have hsplit2 := norm_sub_le_norm_sub_add_norm_sub (1 - (σ : ℂ) * (u : ℂ) ^ 2 / 2)
    (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2) (Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))
  have hCu : C * |u| ^ 3 ≤ C * δ * u ^ 2 := by
    calc C * |u| ^ 3 ≤ C * (δ * u ^ 2) := mul_le_mul_of_nonneg_left hu3 hC
      _ = C * δ * u ^ 2 := by ring
  have hsq0 := sq_nonneg u
  have hfin : (C * δ) * u ^ 2 + (ε / 4) * u ^ 2 + (v ^ 2 * δ / 4) * u ^ 2 ≤ ε * u ^ 2 := by
    have : C * δ + ε / 4 + v ^ 2 * δ / 4 ≤ ε := by nlinarith
    nlinarith
  linarith

/-- Products of contractions with quadratic contact that is uniform along a sequence of
factors, over an array with small coefficients and bounded square sums, have the same
limit. -/
private theorem tendsto_prod_sub_prod_of_uniform_quadratic (N : ℕ → ℕ)
    (a : (n : ℕ) → Fin (N n) → ℝ) (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ)
    (hf : ∀ n u, ‖f n u‖ ≤ 1) (hg : ∀ u, ‖g u‖ ≤ 1)
    (hfg : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ δ →
      ‖f n u - g u‖ ≤ ε * u ^ 2)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (B : ℝ) (hB : 0 < B) (hbound : ∀ᶠ n : ℕ in atTop, ∑ i, a n i ^ 2 ≤ B) :
    Tendsto (fun n : ℕ => (∏ i, f n (a n i)) - ∏ i, g (a n i)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hev⟩ := hfg (ε / (2 * B)) (by positivity)
  filter_upwards [hsmall δ hδ, hbound, hev] with n hn hb hn'
  rw [dist_zero_right]
  have hprod := LatticeProb.norm_prod_sub_prod_le_sum Finset.univ (fun i => f n (a n i))
    (fun i => g (a n i)) (fun i _ => hf _ _) (fun i _ => hg _)
  have hsum : ∑ i, ‖f n (a n i) - g (a n i)‖ ≤ ε / (2 * B) * B := by
    calc ∑ i, ‖f n (a n i) - g (a n i)‖ ≤ ∑ i, ε / (2 * B) * a n i ^ 2 :=
          Finset.sum_le_sum fun i _ => hn' _ (hn i)
      _ = ε / (2 * B) * ∑ i, a n i ^ 2 := (Finset.mul_sum ..).symm
      _ ≤ ε / (2 * B) * B := mul_le_mul_of_nonneg_left hb (by positivity)
  have heq : ε / (2 * B) * B = ε / 2 := by field_simp
  rw [heq] at hsum
  linarith

/-- The product of the characteristic functions of a weighted row along a sequence of
laws converges to the Gaussian one at the LIMIT variance. -/
private theorem tendsto_prod_charFun_seq (θ K v : ℝ) (hθ : 0 < θ) (hv : 0 < v)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ * |z|)) (ν n))
    (hK : ∀ n, ∫ z, Real.exp (θ * |z|) ∂(ν n) ≤ K)
    (hvar : Tendsto (fun n => ∫ z, z ^ 2 ∂(ν n)) atTop (𝓝 v))
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun n => ∑ i, a n i ^ 2) atTop (𝓝 Q)) (t : ℝ) :
    Tendsto (fun n : ℕ => ∏ i, charFun (ν n) (a n i * t)) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2))) := by
  set B := |Q| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hQB : Q < B := by dsimp [B]; linarith [le_abs_self Q]
  have hbound : ∀ᶠ n : ℕ in atTop, ∑ i, (a n i * t) ^ 2 ≤ B * (t ^ 2 + 1) := by
    filter_upwards [hQ.eventually (gt_mem_nhds hQB)] with n hn
    have hsum : ∑ i, (a n i * t) ^ 2 = (∑ i, a n i ^ 2) * t ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.sum_mul]
    rw [hsum]
    have := mul_le_mul_of_nonneg_right hn.le (sq_nonneg t)
    nlinarith
  have hsmall' : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i * t| ≤ δ := by
    intro δ hδ
    filter_upwards [hsmall (δ / (|t| + 1)) (by positivity)] with n hn i
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right (hn i) (abs_nonneg t)
    have htpos : 0 < |t| + 1 := by positivity
    have h' : δ / (|t| + 1) * |t| ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ htpos]
      nlinarith
    exact h.trans h'
  have hg : ∀ u : ℝ, ‖Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2)‖ ≤ 1 := by
    intro u
    have he : -(v : ℂ) * (u : ℂ) ^ 2 / 2 = ((-v * u ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv.le) (sq_nonneg u)) (by norm_num))
  have hd := tendsto_prod_sub_prod_of_uniform_quadratic N (fun n i => a n i * t)
    (fun n => charFun (ν n)) (fun u => Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2))
    (fun n u => norm_charFun_le_one u) hg
    (fun ε hε => charFun_gaussian_uniform_littleO θ K v hθ hv ν hmean hexp hK hvar ε hε)
    hsmall' (B * (t ^ 2 + 1)) (by positivity) hbound
  have hgauss : Tendsto (fun n : ℕ => ∏ i,
      Complex.exp (-(v : ℂ) * ((a n i * t : ℝ) : ℂ) ^ 2 / 2)) atTop
      (𝓝 (Complex.exp (-(v : ℂ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    have he (n : ℕ) : (∏ i, Complex.exp (-(v : ℂ) * ((a n i * t : ℝ) : ℂ) ^ 2 / 2)) =
        Complex.exp (-(v : ℂ) * ((∑ i, a n i ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [he]
    exact (((Complex.continuous_ofReal.tendsto Q).comp hQ).const_mul (-(v : ℂ))).mul_const
      ((t : ℂ) ^ 2) |>.div_const 2 |>.cexp
  have h := hd.add hgauss
  simpa only [sub_add_cancel, zero_add] using h

/-! ### The Gaussian limit at the limit variance -/

/-- **The scalar Lindeberg step along a sequence of laws.**  A weighted row of a scenery
whose one-site law `ν n` varies with `n`, but carries one exponential moment, has the
centred Gaussian of variance `v Q` as its limit on the centred mass law, where `v` is the
limit of the variances of the laws and `Q` the limit of the sums of squares of the
weights. -/
private theorem tendstoInDistribution_linear_pick_mass_seq (hd : 1 ≤ d) (θ K v : ℝ)
    (hθ : 0 < θ) (hv : 0 < v)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ * |z|)) (ν n))
    (hK : ∀ n, ∫ z, Real.exp (θ * |z|) ∂(ν n) ≤ K)
    (hvar : Tendsto (fun n => ∫ z, z ^ 2 ∂(ν n)) atTop (𝓝 v))
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin (N n) → ℝ)
    (e : (n : ℕ) → Fin (N n) → Site d) (he : ∀ n, Function.Injective (e n))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ i, |a n i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun n => ∑ i, a n i ^ 2) atTop (𝓝 Q)) :
    TendstoInDistribution
      (fun (n : ℕ) (σ : Site d → ℝ) => ∑ i, a n i * Sandpile.scenery d σ (e n i))
      atTop (id : ℝ → ℝ) (fun n => Sandpile.centeredMassLaw d (ν n))
      (gaussianReal 0 (Real.toNNReal (v * Q))) := by
  have hm (n : ℕ) :
      Measurable (fun σ : Site d → ℝ => ∑ i, a n i * Sandpile.scenery d σ (e n i)) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul ((measurable_pi_apply (e n i)).comp (Sandpile.measurable_scenery d))
  have hG (n : ℕ) : Measurable (fun ξ : Fin (N n) → ℝ => ∑ i, a n i * ξ i) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply i)
  have hmap (n : ℕ) : (Sandpile.centeredMassLaw d (ν n)).map
        (fun σ : Site d → ℝ => ∑ i, a n i * Sandpile.scenery d σ (e n i))
      = (Measure.pi fun _ : Fin (N n) => ν n).map (fun ξ => ∑ i, a n i * ξ i) := by
    have hmp : MeasurePreserving (Sandpile.scenery d) (Sandpile.centeredMassLaw d (ν n))
        (LatticeProb.iidLaw d (ν n)) :=
      ⟨Sandpile.measurable_scenery d, Sandpile.map_scenery_centeredMassLaw d (ν n) hd⟩
    have hcomp := (LatticeProb.measurePreserving_pick _ (ν n) (e n) (he n)).comp hmp
    have h := Measure.map_map (μ := Sandpile.centeredMassLaw d (ν n)) (hG n) hcomp.measurable
    rw [hcomp.map_eq] at h
    exact h.symm
  refine ⟨fun n => (hm n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hv0 : 0 ≤ v := hv.le
  have hQ0 : 0 ≤ Q := ge_of_tendsto hQ (Eventually.of_forall fun n =>
    Finset.sum_nonneg fun i _ => sq_nonneg (a n i))
  have hvQ : 0 ≤ v * Q := mul_nonneg hv0 hQ0
  have h := tendsto_prod_charFun_seq θ K v hθ hv ν hmean hexp hK hvar N a hsmall Q hQ t
  change Tendsto (fun n => charFun ((Sandpile.centeredMassLaw d (ν n)).map
    (fun σ : Site d → ℝ => ∑ i, a n i * Sandpile.scenery d σ (e n i))) t) atTop
      (𝓝 (charFun ((gaussianReal 0 (Real.toNNReal (v * Q))).map id) t))
  simp_rw [hmap, LatticeProb.charFun_weighted_pi]
  rw [Measure.map_id, charFun_gaussianReal]
  have he' : Complex.exp (-(v : ℂ) * (Q : ℂ) * (t : ℂ) ^ 2 / 2) =
      Complex.exp ((t : ℂ) * (0 : ℝ) * Complex.I -
        (Real.toNNReal (v * Q) : ℝ) * (t : ℂ) ^ 2 / 2) := by
    congr 1
    rw [Real.coe_toNNReal _ hvQ]
    push_cast
    ring
  rw [← he']
  exact h

/-! ### The vector lift by Cramér-Wold -/

/-- The Cramér-Wold device along a sequence of laws: the proof of
`tendstoInDistribution_of_forall_inner` does not use that the law is the same at every
index. -/
private theorem tendstoInDistribution_of_forall_inner_seq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (X : ℕ → Ω → E) (Z : Ω' → E) (P : ℕ → Measure Ω) (Q : Measure Ω')
    [∀ n, IsProbabilityMeasure (P n)] [IsProbabilityMeasure Q]
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hZ : AEMeasurable Z Q)
    (h : ∀ t : E, TendstoInDistribution
        (fun (n : ℕ) (ω : Ω) => (inner ℝ (X n ω) t : ℝ)) atTop
        (fun ω => (inner ℝ (Z ω) t : ℝ)) P Q) :
    TendstoInDistribution X atTop Z P Q := by
  refine ⟨hX, hZ, ?_⟩
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have h1 := (h t).tendsto
  rw [MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun] at h1
  have h2 := h1 1
  have hgoal : (fun n : ℕ => charFun ((P n).map (X n)) t)
      = fun n : ℕ => charFun ((P n).map fun ω => (inner ℝ (X n ω) t : ℝ)) 1 := by
    funext n; exact charFun_map_inner (P n) (X n) (hX n) t
  show Tendsto (fun n : ℕ => charFun ((P n).map (X n)) t) atTop (𝓝 (charFun (Q.map Z) t))
  rw [hgoal, charFun_map_inner Q Z hZ t]
  exact h2

/-- The Cramér-Wold device on `Fin m → ℝ` with the product measurable structure, along a
sequence of laws, with the projections written as dot products. -/
private theorem tendstoInDistribution_pi_of_forall_dot_seq {m : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (X : ℕ → Ω → (Fin m → ℝ))
    (Z : Ω' → (Fin m → ℝ)) (P : ℕ → Measure Ω) (Q : Measure Ω')
    [∀ n, IsProbabilityMeasure (P n)] [IsProbabilityMeasure Q]
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hZ : AEMeasurable Z Q)
    (h : ∀ t : Fin m → ℝ, TendstoInDistribution
        (fun (n : ℕ) (ω : Ω) => ∑ i, X n ω i * t i) atTop
        (fun ω => ∑ i, Z ω i * t i) P Q) :
    TendstoInDistribution X atTop Z P Q := by
  set e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ with he
  have key : TendstoInDistribution (fun (n : ℕ) (ω : Ω) => e.symm (X n ω)) atTop
      (fun ω => e.symm (Z ω)) P Q := by
    refine tendstoInDistribution_of_forall_inner_seq _ _ P Q
      (fun n => e.symm.continuous.measurable.comp_aemeasurable (hX n))
      (e.symm.continuous.measurable.comp_aemeasurable hZ) ?_
    intro t
    have ht := h (e t)
    have h1 : (fun (n : ℕ) (ω : Ω) => (inner ℝ (e.symm (X n ω)) t : ℝ))
        = fun (n : ℕ) (ω : Ω) => ∑ i, X n ω i * (e t) i := by
      funext n ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (fun ω : Ω' => (inner ℝ (e.symm (Z ω)) t : ℝ))
        = fun ω : Ω' => ∑ i, Z ω i * (e t) i := by
      funext ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, h2]
    exact ht
  have hfin := key.continuous_comp (g := fun x : EuclideanSpace ℝ (Fin m) => e x) e.continuous
  simpa [Function.comp_def] using hfin

/-- Convergence in distribution to a law is convergence in distribution to any random
variable carrying that law, along a sequence of laws. -/
private theorem tendstoInDistribution_of_map_eq_seq {F : Type*} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace F] [TopologicalSpace F]
    [OpensMeasurableSpace F] {X : ℕ → Ω → F} {P : ℕ → Measure Ω}
    [∀ n, IsProbabilityMeasure (P n)]
    {μ' : Measure F} [IsProbabilityMeasure μ'] {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (h : TendstoInDistribution X atTop (id : F → F) P μ')
    (Y : Ω' → F) (hY : AEMeasurable Y Q) (hmap : Q.map Y = μ') :
    TendstoInDistribution X atTop Y P Q := by
  refine ⟨h.forall_aemeasurable, hY, ?_⟩
  have h2 : Q.map Y = μ'.map id := by rw [MeasureTheory.Measure.map_id]; exact hmap
  convert h.tendsto using 2
  exact Subtype.ext h2

/-- **The vector Lindeberg-Feller step along a sequence of laws.** -/
private theorem tendstoInDistribution_vector_pick_mass_seq (hd : 1 ≤ d) (θ K v : ℝ)
    (hθ : 0 < θ) (hv : 0 < v)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ * |z|)) (ν n))
    (hK : ∀ n, ∫ z, Real.exp (θ * |z|) ∂(ν n) ≤ K)
    (hvar : Tendsto (fun n => ∫ z, z ^ 2 ∂(ν n)) atTop (𝓝 v))
    {m : ℕ} (F : ℕ → (Site d → ℝ) → Fin m → ℝ)
    (N : ℕ → ℕ) (a : (n : ℕ) → Fin m → Fin (N n) → ℝ)
    (e : (n : ℕ) → Fin (N n) → Site d) (he : ∀ n, Function.Injective (e n))
    (hF : ∀ (n : ℕ) (σ : Site d → ℝ) (i : Fin m),
      F n σ i = ∑ k, a n i k * Sandpile.scenery d σ (e n k))
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (g : Fin m → Space d → ℝ) (hg : ∀ i, MemLp (g i) 2 (volume : Measure (Space d)))
    (Q : (Fin m → ℝ) → ℝ)
    (hsmall : ∀ (t : Fin m → ℝ) (δ : ℝ), 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ k, |∑ i, t i * a n i k| ≤ δ)
    (hQlim : ∀ t : Fin m → ℝ,
      Tendsto (fun n : ℕ => ∑ k, (∑ i, t i * a n i k) ^ 2) atTop (𝓝 (Q t)))
    (hQvar : ∀ t : Fin m → ℝ, v * Q t
      = ∫ y : Space d, (∑ i, t i * g i y) * ∑ i, t i * g i y) :
    TendstoInDistribution F atTop (fun (ω : ΩW) (i : Fin m) => W (g i) ω)
      (fun n => Sandpile.centeredMassLaw d (ν n)) PW := by
  classical
  have hmeasF : ∀ n : ℕ, AEMeasurable (F n) (Sandpile.centeredMassLaw d (ν n)) := by
    intro n
    refine Measurable.aemeasurable (measurable_pi_lambda _ fun i => ?_)
    have hfun : (fun σ : Site d → ℝ => F n σ i)
        = fun σ : Site d → ℝ => ∑ k, a n i k * Sandpile.scenery d σ (e n k) :=
      funext fun σ => hF n σ i
    rw [hfun]
    refine Finset.measurable_sum _ fun k _ => measurable_const.mul ?_
    exact (measurable_pi_apply (e n k)).comp (Sandpile.measurable_scenery d)
  have hmeasZ : AEMeasurable (fun (ω : ΩW) (i : Fin m) => W (g i) ω) PW :=
    (measurable_pi_lambda _ fun i => hW.meas (g i) (hg i)).aemeasurable
  refine tendstoInDistribution_pi_of_forall_dot_seq F
    (fun (ω : ΩW) (i : Fin m) => W (g i) ω) (fun n => Sandpile.centeredMassLaw d (ν n)) PW
    hmeasF hmeasZ ?_
  intro t
  have hfam : (fun (n : ℕ) (σ : Site d → ℝ) => ∑ i, F n σ i * t i)
      = fun (n : ℕ) (σ : Site d → ℝ) =>
        ∑ k, (∑ i, t i * a n i k) * Sandpile.scenery d σ (e n k) := by
    funext n σ
    simp only [hF]
    exact sum_dot_eq_sum_pick t (a n) (fun k => Sandpile.scenery d σ (e n k))
  rw [hfam]
  have hclt := tendstoInDistribution_linear_pick_mass_seq hd θ K v hθ hv ν hmean hexp hK hvar N
    (fun n k => ∑ i, t i * a n i k) e he (hsmall t) (Q t) (hQlim t)
  have hZmeas : AEMeasurable (fun ω : ΩW => ∑ i, W (g i) ω * t i) PW := by
    refine Measurable.aemeasurable (Finset.measurable_sum _ fun i _ => ?_)
    exact (hW.meas (g i) (hg i)).mul_const _
  refine tendstoInDistribution_of_map_eq_seq hclt _ hZmeas ?_
  have hcomb := map_whiteNoise_combination W PW hW t g hg
  have hfun2 : (fun ω : ΩW => ∑ i, W (g i) ω * t i)
      = fun ω : ΩW => ∑ i, t i * W (g i) ω := by
    funext ω
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hfun2, hcomb, hQvar t]

/-- **The finite-dimensional limit along a sequence of laws.**  The rescaled
interpolated potential, read at finitely many times and places, converges to the
Gaussian potential at the LIMIT variance, when the laws carry a common
exponential moment and their variances converge. -/
theorem heat_potential_fd_seq
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hMCT : ContinuumDoubleTimeLimit d)
    (θ₀ K₀ v : ℝ) (hθ₀ : 0 < θ₀) (hv : 0 < v)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (hmean : ∀ n, ∫ z, z ∂(ν n) = 0)
    (hexp : ∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (ν n))
    (hK₀ : ∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(ν n) ≤ K₀)
    (hvar : Tendsto (fun n => variance (id : ℝ → ℝ) (ν n)) atTop (𝓝 v))
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ L) :
    TendstoInDistribution
      (fun (n : ℕ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n) (Sandpile.scenery d σ)
          (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d v W (r i) (w i) ω)
      (fun n => Sandpile.centeredMassLaw d (ν n)) PW := by
  classical
  -- the exponential moment gives square integrability, and the variance is `∫ z ^ 2`
  have hsq : ∀ n, MemLp (id : ℝ → ℝ) 2 (ν n) := fun n =>
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      (LatticeProb.integrable_sq_of_exp hθ₀ (hexp n))
  have hvar2 : ∀ n, ∫ z, z ^ 2 ∂(ν n) = variance (id : ℝ → ℝ) (ν n) := by
    intro n
    rw [ProbabilityTheory.variance_eq_sub (hsq n)]
    have h1 : ∫ z, ((id : ℝ → ℝ) ^ 2) z ∂(ν n) = ∫ z, z ^ 2 ∂(ν n) := rfl
    have h2 : ∫ z, (id : ℝ → ℝ) z ∂(ν n) = 0 := hmean n
    rw [h1, h2]
    ring
  have hvar' : Tendsto (fun n => ∫ z, z ^ 2 ∂(ν n)) atTop (𝓝 v) := by
    simpa only [hvar2] using hvar
  set c : ℝ := Real.sqrt v with hc
  set g : Fin m → Space d → ℝ :=
    fun i y => c * Sandpile.Continuum.greenTimeBM d (r i) (w i) y with hgdef
  have hmemg : ∀ i, MemLp (fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y) 2
      (volume : Measure (Space d)) := fun i => memLp_greenTimeBM hd hd3 (hr i) (w i)
  have hgmem : ∀ i, MemLp (g i) 2 (volume : Measure (Space d)) := fun i =>
    (hmemg i).const_mul c
  -- the coefficient inputs are those of the fixed-law proof: they do not see the law
  set Q : (Fin m → ℝ) → ℝ := fun t => ∑ i, ∑ j, t i * t j *
    ∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
      Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j) with hQdef
  have hQlimR : ∀ t : Fin m → ℝ, Tendsto (fun R : ℝ => ∑ k : Fin (interpBox d R L r).card,
      (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2)
      atTop (𝓝 (Q t)) := by
    intro t
    have heq : ∀ᶠ R : ℝ in atTop,
        (∑ i, ∑ j, t i * t j * interpDoubleTimeSum d R (r i) (r j) (w i) (w j))
          = ∑ k : Fin (interpBox d R L r).card,
            (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
      exact (sum_interp_sq_eq' d hRpos L r w hw t).symm
    refine Tendsto.congr' heq ?_
    exact tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ =>
        (tendsto_interpDoubleTimeSum_of_continuum hLCLT hd hd3 hMCT (hr i) (hr j)
          (w i) (w j)).const_mul (t i * t j)
  have hQvar : ∀ t : Fin m → ℝ, v * Q t
      = ∫ y : Space d, (∑ i, t i * g i y) * ∑ i, t i * g i y := by
    intro t
    have hsq2 : c * c = v := Real.mul_self_sqrt hv.le
    have hI : ∫ y : Space d, (∑ i, t i * g i y) * ∑ i, t i * g i y
        = ∑ i, ∑ j, (t i * c) * (t j * c) *
          ∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
            Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j) :=
      integral_sum_greenTimeBM_sq_eq hd hd3 r hr w t c
    rw [hI, hQdef]
    simp only []
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-(t i * t j * (∫ s in (0 : ℝ)..(r i), ∫ u in (0 : ℝ)..(r j),
      Sandpile.Continuum.heatKernelBM d (s + u) (w i) (w j)))) * hsq2
  have hvec := tendstoInDistribution_vector_pick_mass_seq hd θ₀ K₀ v hθ₀ hv ν hmean hexp hK₀
    hvar'
    (fun (n : ℕ) (σ : Site d → ℝ) (i : Fin m) =>
      Sandpile.Frozen.HeatPotentialInvariance.linInterp d (R n) (Sandpile.scenery d σ)
        (r i) (w i))
    (fun n => (interpBox d (R n) L r).card)
    (fun n i k => interpCoeff d (R n) (r i) (w i) (siteEnum (interpBox d (R n) L r) k))
    (fun n => siteEnum (interpBox d (R n) L r))
    (fun n => siteEnum_injective _)
    (fun n σ i => linInterp_eq_sum_interpBox (R n) L r w hw (Sandpile.scenery d σ) i)
    PW W hW g hgmem Q
    (fun t δ hδ => hR.eventually (interp_hsmall hd hd3 r hr w L t δ hδ))
    (fun t => (hQlimR t).comp hR) hQvar
  refine hvec.congr (fun n => Filter.EventuallyEq.refl _ _) ?_
  have hsm : ∀ i, W (g i) =ᵐ[PW] fun ω =>
      Sandpile.Continuum.gaussianPotential d v W (r i) (w i) ω := by
    intro i
    have hfun : g i = c • fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y := by
      funext y
      simp [hgdef]
    rw [hfun]
    exact hW.smul c (fun y => Sandpile.Continuum.greenTimeBM d (r i) (w i) y) (hmemg i)
  have := (MeasureTheory.ae_all_iff (ι := Fin m)
    (p := fun ω i => W (g i) ω =
      Sandpile.Continuum.gaussianPotential d v W (r i) (w i) ω)).mpr hsm
  filter_upwards [this] with ω hω
  funext i
  exact hω i

end Sandpile.Support
