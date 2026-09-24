/-
A Bernstein-type exponential concentration inequality for a bounded, coordinatewise
Lipschitz function of independent coordinates.

`LatticeProb.exp_conc_pi` proves the sub-Gaussian bound by splitting off one coordinate at a
time and applying, at the head, a sub-Gaussian estimate for a Lipschitz function of one
coordinate.  That estimate needs an exponential moment of the one-site law, uniform in the
coordinate, and the heavy-tailed case has none: the scenery truncated from below at
`-t/c_z` has a one-site law whose exponential moment blows up as `c_z` shrinks.  What the
truncated field does have is a bounded OSCILLATION per coordinate: `c_z` times the range of
the truncated value, at most `t + c_zM` uniformly in `z`.  The same coordinate induction
with the Bernstein moment generating function bound `LatticeProb.mgf_le_of_bounded` at the
head therefore goes through and produces the Bernstein exponent, whose quadratic term is
the second moment of the one-site law times the square sum of the Lipschitz coefficients
and whose linear term is the oscillation.
-/
import LatticeProb.Prob.EfronStein
import LatticeProb.Prob.Bernstein

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- Expanding a mean square deviation against a probability measure. -/
theorem integral_sub_const_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → ℝ) (hint : Integrable h μ)
    (hsq : Integrable (fun ω => h ω ^ 2) μ) (c : ℝ) :
    ∫ ω, (h ω - c) ^ 2 ∂μ = (∫ ω, h ω ^ 2 ∂μ) - 2 * c * (∫ ω, h ω ∂μ) + c ^ 2 := by
  have hpt : ∀ ω, (h ω - c) ^ 2 = h ω ^ 2 + ((-(2 * c)) * h ω + c ^ 2) := fun ω => by ring
  have e0 : ∫ ω, (h ω - c) ^ 2 ∂μ = ∫ ω, (h ω ^ 2 + ((-(2 * c)) * h ω + c ^ 2)) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have e1 : ∫ ω, (h ω ^ 2 + ((-(2 * c)) * h ω + c ^ 2)) ∂μ
      = (∫ ω, h ω ^ 2 ∂μ) + ∫ ω, ((-(2 * c)) * h ω + c ^ 2) ∂μ :=
    integral_add hsq ((hint.const_mul (-(2 * c))).add (integrable_const _))
  have e2 : ∫ ω, ((-(2 * c)) * h ω + c ^ 2) ∂μ
      = (∫ ω, (-(2 * c)) * h ω ∂μ) + ∫ _ω, c ^ 2 ∂μ :=
    integral_add (hint.const_mul (-(2 * c))) (integrable_const _)
  rw [e0, e1, e2, integral_const_mul]
  simp
  ring

/-- The variance is the least mean square deviation, so any constant gives an upper bound
on it. -/
theorem integral_centred_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → ℝ) (hint : Integrable h μ)
    (hsq : Integrable (fun ω => h ω ^ 2) μ) (c : ℝ) :
    ∫ ω, (h ω - ∫ ω', h ω' ∂μ) ^ 2 ∂μ ≤ ∫ ω, (h ω - c) ^ 2 ∂μ := by
  rw [integral_sub_const_sq μ h hint hsq c,
    integral_sub_const_sq μ h hint hsq (∫ ω', h ω' ∂μ)]
  nlinarith [sq_nonneg ((∫ ω', h ω' ∂μ) - c)]

/-- **The Bernstein exponential concentration inequality on a finite product.**  A bounded,
coordinatewise Lipschitz function whose oscillation in each coordinate is at most `b`
satisfies, for `0 < λ` with `λb < 3`,
`E e^{λ(F-EF)} ≤ exp(λ²(s∑ℓ_i²)/(2(1-λb/3)))`, where `s` bounds the second moment of the
one-site law.  The proof is the coordinate induction of `LatticeProb.exp_conc_pi` with
`LatticeProb.mgf_le_of_bounded` as the one-dimensional input. -/
theorem exp_conc_bdd_pi (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsqν : Integrable (fun y : ℝ => y ^ 2) ν) (s : ℝ) (hs : ∫ y, y ^ 2 ∂ν ≤ s)
    (b lam : ℝ) (hlam : 0 < lam) (hb : 0 ≤ b) (hlb : lam * b < 3) :
    ∀ (M : ℕ) (F : (Fin M → ℝ) → ℝ), Measurable F → ∀ A : ℝ, (∀ ξ, |F ξ| ≤ A) →
      ∀ ℓ : Fin M → ℝ, (∀ i, 0 ≤ ℓ i) →
      (∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
        |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
      (∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ), |F ξ - F (Function.update ξ i y)| ≤ b) →
        ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin M => ν)))
            ∂(Measure.pi fun _ : Fin M => ν)
          ≤ Real.exp (lam ^ 2 / (2 * (1 - lam * b / 3)) * (s * ∑ i, ℓ i ^ 2)) := by
  have hden : (0 : ℝ) < 1 - lam * b / 3 := by linarith
  set C : ℝ := lam ^ 2 / (2 * (1 - lam * b / 3)) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hs0 : 0 ≤ s := le_trans (integral_nonneg fun y => sq_nonneg y) hs
  intro M
  induction M with
  | zero =>
      intro F hFm A hA ℓ hℓ hLip hOsc
      have hconst : ∀ η : Fin 0 → ℝ, F η = F (fun _ => 0) := fun η => by
        congr 1
        exact Subsingleton.elim η _
      have hI : ∫ η, F η ∂(Measure.pi fun _ : Fin 0 => ν) = F (fun _ => 0) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hconst)]
        simp
      rw [hI]
      have hzero : ∀ ξ : Fin 0 → ℝ, Real.exp (lam * (F ξ - F (fun _ => 0))) = 1 := by
        intro ξ
        rw [hconst ξ]
        simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hzero)]
      simp
  | succ N ih =>
      intro F hFm A hA ℓ hℓ hLip hOsc
      have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
      have hFint : Integrable F (Measure.pi fun _ : Fin (N + 1) => ν) :=
        Integrable.mono' (integrable_const A) hFm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => by
            rw [Real.norm_eq_abs]; exact hA ξ)
      set μ0 : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hμ0
      set G : ℝ → ℝ := fun y => ∫ η, F (Fin.cons y η) ∂μ0 with hGdef
      have hGm : Measurable G := by
        have hfm : Measurable fun p : ℝ × (Fin N → ℝ) => F (Fin.cons p.1 p.2) :=
          hFm.comp LatticeProb.measurable_cons_pair
        exact (hfm.stronglyMeasurable.integral_prod_right').measurable
      set EF : ℝ := ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin (N + 1) => ν) with hEFdef
      have hEF : EF = ∫ y, G y ∂ν := LatticeProb.integral_pi_succ ν F hFint
      have hconsm : ∀ y : ℝ, Measurable fun η : Fin N → ℝ => F (Fin.cons y η) :=
        fun y => hFm.comp (LatticeProb.measurable_cons y)
      have hconsLip : ∀ y : ℝ, ∀ (η : Fin N → ℝ) (j : Fin N) (z : ℝ),
          |F (Fin.cons y η) - F (Fin.cons y (Function.update η j z))|
            ≤ ℓ j.succ * |η j - z| := by
        intro y η j z
        rw [LatticeProb.cons_update_succ]
        have h := hLip (Fin.cons y η) j.succ z
        simpa using h
      have hconsOsc : ∀ y : ℝ, ∀ (η : Fin N → ℝ) (j : Fin N) (z : ℝ),
          |F (Fin.cons y η) - F (Fin.cons y (Function.update η j z))| ≤ b := by
        intro y η j z
        rw [LatticeProb.cons_update_succ]
        exact hOsc (Fin.cons y η) j.succ z
      have hinner : ∀ y : ℝ,
          ∫ η, Real.exp (lam * (F (Fin.cons y η) - G y)) ∂μ0
            ≤ Real.exp (C * (s * ∑ j : Fin N, ℓ j.succ ^ 2)) :=
        fun y => ih (fun η => F (Fin.cons y η)) (hconsm y) A (fun η => hA _)
          (fun j => ℓ j.succ) (fun j => hℓ _) (hconsLip y) (hconsOsc y)
      have hGbd : ∀ y, |G y| ≤ A := by
        intro y
        have hint : Integrable (fun η => F (Fin.cons y η)) μ0 :=
          Integrable.mono' (integrable_const A) (hconsm y).aestronglyMeasurable
            (Filter.Eventually.of_forall fun η => by rw [Real.norm_eq_abs]; exact hA _)
        calc |G y| ≤ ∫ η, |F (Fin.cons y η)| ∂μ0 := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := μ0) (f := fun η => F (Fin.cons y η))
          _ ≤ ∫ _η : Fin N → ℝ, A ∂μ0 :=
              integral_mono hint.abs (integrable_const A) (fun η => hA _)
          _ = A := by simp
      have hGcons : ∀ y : ℝ, Integrable (fun η => F (Fin.cons y η)) μ0 := fun y =>
        Integrable.mono' (integrable_const A) (hconsm y).aestronglyMeasurable
          (Filter.Eventually.of_forall fun η => by rw [Real.norm_eq_abs]; exact hA _)
      have hGlip : ∀ y z : ℝ, |G y - G z| ≤ ℓ 0 * |y - z| := by
        intro y z
        have hrep : G y - G z = ∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0 := by
          rw [integral_sub (hGcons y) (hGcons z)]
        rw [hrep]
        calc |∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0|
            ≤ ∫ η, |F (Fin.cons y η) - F (Fin.cons z η)| ∂μ0 := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := μ0) (f := fun η => F (Fin.cons y η) - F (Fin.cons z η))
          _ ≤ ∫ _η : Fin N → ℝ, ℓ 0 * |y - z| ∂μ0 := by
              refine integral_mono ((hGcons y).sub (hGcons z)).abs (integrable_const _)
                fun η => ?_
              have h := hLip (Fin.cons y η) 0 z
              rw [LatticeProb.cons_update_zero] at h
              simpa using h
          _ = ℓ 0 * |y - z| := by simp
      have hGosc : ∀ y z : ℝ, |G y - G z| ≤ b := by
        intro y z
        have hrep : G y - G z = ∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0 := by
          rw [integral_sub (hGcons y) (hGcons z)]
        rw [hrep]
        calc |∫ η, (F (Fin.cons y η) - F (Fin.cons z η)) ∂μ0|
            ≤ ∫ η, |F (Fin.cons y η) - F (Fin.cons z η)| ∂μ0 := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := μ0) (f := fun η => F (Fin.cons y η) - F (Fin.cons z η))
          _ ≤ ∫ _η : Fin N → ℝ, b ∂μ0 := by
              refine integral_mono ((hGcons y).sub (hGcons z)).abs (integrable_const _)
                fun η => ?_
              have h := hOsc (Fin.cons y η) 0 z
              rw [LatticeProb.cons_update_zero] at h
              simpa using h
          _ = b := by simp
      have hGint : Integrable G ν :=
        Integrable.mono' (integrable_const A) hGm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hGbd y)
      have hWbd : ∀ y, |G y - EF| ≤ b := by
        intro y
        rw [hEF]
        have hrep : G y - ∫ z, G z ∂ν = ∫ z, (G y - G z) ∂ν := by
          rw [integral_sub (integrable_const _) hGint]
          simp
        rw [hrep]
        calc |∫ z, (G y - G z) ∂ν| ≤ ∫ z, |G y - G z| ∂ν := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
                (μ := ν) (f := fun z => G y - G z)
          _ ≤ ∫ _z : ℝ, b ∂ν :=
              integral_mono ((integrable_const _).sub hGint).abs (integrable_const b)
                (fun z => hGosc y z)
          _ = b := by simp
      have hWint : Integrable (fun y => G y - EF) ν := hGint.sub (integrable_const _)
      have hWsq : Integrable (fun y => (G y - EF) ^ 2) ν :=
        Integrable.mono' (integrable_const (b ^ 2))
          ((hGm.sub_const EF).pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hWbd y, abs_nonneg (G y - EF), sq_abs (G y - EF)])
      have hWmean : ∫ y, (G y - EF) ∂ν = 0 := by
        rw [integral_sub hGint (integrable_const _), ← hEF]
        simp
      have hGsq : Integrable (fun y => G y ^ 2) ν :=
        Integrable.mono' (integrable_const (A ^ 2)) (hGm.pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hGbd y, abs_nonneg (G y), sq_abs (G y)])
      have hWsq_le : ∫ y, (G y - EF) ^ 2 ∂ν ≤ s * ℓ 0 ^ 2 := by
        have h1 : ∫ y, (G y - EF) ^ 2 ∂ν ≤ ∫ y, (G y - G 0) ^ 2 ∂ν := by
          rw [hEF]
          exact integral_centred_sq_le ν G hGint hGsq (G 0)
        have h2 : Integrable (fun y => (G y - G 0) ^ 2) ν :=
          Integrable.mono' (integrable_const ((2 * A) ^ 2))
            ((hGm.sub_const (G 0)).pow_const 2).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              nlinarith [hGbd y, hGbd 0, abs_nonneg (G y), abs_nonneg (G 0),
                neg_abs_le (G y), le_abs_self (G y), neg_abs_le (G 0), le_abs_self (G 0),
                hA0])
        have h3 : ∫ y, (G y - G 0) ^ 2 ∂ν ≤ ∫ y, ℓ 0 ^ 2 * y ^ 2 ∂ν := by
          refine integral_mono h2 (hsqν.const_mul _) fun y => ?_
          have h := hGlip y 0
          rw [sub_zero] at h
          have hsq' : (G y - G 0) ^ 2 ≤ (ℓ 0 * |y|) ^ 2 := by
            nlinarith [abs_nonneg (G y - G 0), sq_abs (G y - G 0), h,
              mul_nonneg (hℓ 0) (abs_nonneg y)]
          calc (G y - G 0) ^ 2 ≤ (ℓ 0 * |y|) ^ 2 := hsq'
            _ = ℓ 0 ^ 2 * y ^ 2 := by rw [mul_pow, sq_abs]
        have hnn : (0 : ℝ) ≤ ∫ y, y ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg y
        have h4 : ∫ y, ℓ 0 ^ 2 * y ^ 2 ∂ν ≤ s * ℓ 0 ^ 2 := by
          rw [integral_const_mul]
          nlinarith [hs, sq_nonneg (ℓ 0), hnn]
        linarith
      have houter : ∫ y, Real.exp (lam * (G y - EF)) ∂ν
          ≤ Real.exp (C * (s * ℓ 0 ^ 2)) := by
        have hmgf := LatticeProb.mgf_le_of_bounded ν (fun y => G y - EF) hWint hWmean b
          (Filter.Eventually.of_forall hWbd) hWsq lam hlam hlb
        have hq : lam ^ 2 * (∫ y, (G y - EF) ^ 2 ∂ν) / (2 * (1 - lam * b / 3))
            ≤ C * (s * ℓ 0 ^ 2) := by
          have hnum : lam ^ 2 * (∫ y, (G y - EF) ^ 2 ∂ν) ≤ lam ^ 2 * (s * ℓ 0 ^ 2) :=
            mul_le_mul_of_nonneg_left hWsq_le (by positivity)
          have hCval : C * (s * ℓ 0 ^ 2)
              = lam ^ 2 * (s * ℓ 0 ^ 2) / (2 * (1 - lam * b / 3)) := by
            rw [hCdef]; ring
          rw [hCval]
          exact div_le_div_of_nonneg_right hnum (by linarith)
        exact le_trans hmgf (Real.exp_le_exp.mpr hq)
      have hexpint : Integrable (fun ξ => Real.exp (lam * (F ξ - EF)))
          (Measure.pi fun _ : Fin (N + 1) => ν) := by
        refine Integrable.mono' (integrable_const (Real.exp (lam * (A + |EF|))))
          ((Real.measurable_exp.comp ((hFm.sub_const EF).const_mul lam))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have h1 : F ξ - EF ≤ A + |EF| := by
          have := hA ξ
          have h2 := le_abs_self (F ξ)
          have h3 := neg_abs_le EF
          linarith [abs_nonneg EF]
        nlinarith [hlam.le]
      have hsplit : ∫ ξ, Real.exp (lam * (F ξ - EF)) ∂(Measure.pi fun _ : Fin (N + 1) => ν)
          = ∫ y, (∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ∂ν :=
        LatticeProb.integral_pi_succ ν _ hexpint
      have hfactor : ∀ y : ℝ, ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0
          = Real.exp (lam * (G y - EF)) *
            ∫ η, Real.exp (lam * (F (Fin.cons y η) - G y)) ∂μ0 := by
        intro y
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        show Real.exp (lam * (F (Fin.cons y η) - EF))
          = Real.exp (lam * (G y - EF)) * Real.exp (lam * (F (Fin.cons y η) - G y))
        rw [← Real.exp_add]
        congr 1
        ring
      have hbig : ∀ y : ℝ, ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0
          ≤ Real.exp (lam * (G y - EF)) *
            Real.exp (C * (s * ∑ j : Fin N, ℓ j.succ ^ 2)) := by
        intro y
        rw [hfactor y]
        exact mul_le_mul_of_nonneg_left (hinner y) (Real.exp_pos _).le
      have hLint : Integrable
          (fun y => ∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ν :=
        LatticeProb.integrable_integral_cons ν _ hexpint
      have hGexpint : Integrable (fun y => Real.exp (lam * (G y - EF))) ν := by
        refine Integrable.mono' (integrable_const (Real.exp (lam * b)))
          ((Real.measurable_exp.comp ((hGm.sub_const EF).const_mul lam))).aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        nlinarith [(abs_le.mp (hWbd y)).2, hlam.le]
      rw [hsplit]
      calc ∫ y, (∫ η, Real.exp (lam * (F (Fin.cons y η) - EF)) ∂μ0) ∂ν
          ≤ ∫ y, Real.exp (lam * (G y - EF)) *
              Real.exp (C * (s * ∑ j : Fin N, ℓ j.succ ^ 2)) ∂ν :=
            integral_mono hLint (hGexpint.mul_const _) hbig
        _ = (∫ y, Real.exp (lam * (G y - EF)) ∂ν) *
              Real.exp (C * (s * ∑ j : Fin N, ℓ j.succ ^ 2)) := integral_mul_const _ _
        _ ≤ Real.exp (C * (s * ℓ 0 ^ 2)) *
              Real.exp (C * (s * ∑ j : Fin N, ℓ j.succ ^ 2)) :=
            mul_le_mul_of_nonneg_right houter (Real.exp_pos _).le
        _ = Real.exp (C * (s * ∑ i : Fin (N + 1), ℓ i ^ 2)) := by
            rw [← Real.exp_add, Fin.sum_univ_succ]
            congr 1
            ring

/-- The lower deviation form of `exp_conc_bdd_pi`, by Chernoff's bound applied to `-F`. -/
theorem measure_le_mean_sub (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsqν : Integrable (fun y : ℝ => y ^ 2) ν)
    (b lam : ℝ) (hlam : 0 < lam) (hb : 0 ≤ b) (hlb : lam * b < 3)
    (M : ℕ) (F : (Fin M → ℝ) → ℝ) (hFm : Measurable F) (A : ℝ) (hA : ∀ ξ, |F ξ| ≤ A)
    (ℓ : Fin M → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i)
    (hLip : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|)
    (hOsc : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ), |F ξ - F (Function.update ξ i y)| ≤ b)
    (r : ℝ) :
    (Measure.pi fun _ : Fin M => ν)
        {ξ | F ξ ≤ (∫ η, F η ∂(Measure.pi fun _ : Fin M => ν)) - r}
      ≤ ENNReal.ofReal (Real.exp (-(lam * r) +
          lam ^ 2 / (2 * (1 - lam * b / 3)) * ((∫ y, y ^ 2 ∂ν) * ∑ i, ℓ i ^ 2))) := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  set μ : Measure (Fin M → ℝ) := Measure.pi fun _ : Fin M => ν with hμ
  set EF : ℝ := ∫ η, F η ∂μ with hEFdef
  set X : (Fin M → ℝ) → ℝ := fun ξ => -(F ξ - EF) with hXdef
  have hnegA : ∀ ξ, |(-F) ξ| ≤ A := fun ξ => by
    show |-F ξ| ≤ A
    rw [abs_neg]; exact hA ξ
  have hnegLip : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
      |(-F) ξ - (-F) (Function.update ξ i y)| ≤ ℓ i * |ξ i - y| := by
    intro ξ i y
    show |-F ξ - -F (Function.update ξ i y)| ≤ _
    rw [neg_sub_neg, abs_sub_comm]
    exact hLip ξ i y
  have hnegOsc : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
      |(-F) ξ - (-F) (Function.update ξ i y)| ≤ b := by
    intro ξ i y
    show |-F ξ - -F (Function.update ξ i y)| ≤ _
    rw [neg_sub_neg, abs_sub_comm]
    exact hOsc ξ i y
  have hFint : Integrable F μ :=
    Integrable.mono' (integrable_const A) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hA ξ)
  have hnegmean : ∫ η, (-F) η ∂μ = -EF := by
    show ∫ η, -F η ∂μ = -EF
    rw [integral_neg]
  have hconc := exp_conc_bdd_pi ν hsqν (∫ y, y ^ 2 ∂ν) le_rfl b lam hlam hb hlb M (-F)
    hFm.neg A hnegA ℓ hℓ hnegLip hnegOsc
  rw [hnegmean] at hconc
  have hmgf : mgf X μ lam
      ≤ Real.exp (lam ^ 2 / (2 * (1 - lam * b / 3)) * ((∫ y, y ^ 2 ∂ν) * ∑ i, ℓ i ^ 2)) := by
    refine le_trans (le_of_eq ?_) hconc
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.exp (lam * X ξ) = Real.exp (lam * ((-F) ξ - -EF))
    congr 1
    show lam * -(F ξ - EF) = lam * (-F ξ - -EF)
    ring
  have hXbd : ∀ ξ, |X ξ| ≤ A + |EF| := by
    intro ξ
    show |-(F ξ - EF)| ≤ A + |EF|
    rw [abs_neg]
    exact le_trans (abs_sub _ _) (add_le_add (hA ξ) le_rfl)
  have hi : Integrable (fun ξ => Real.exp (lam * X ξ)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (lam * (A + |EF|))))
      ((Real.measurable_exp.comp (((hFm.sub_const EF).neg).const_mul lam))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [(abs_le.mp (hXbd ξ)).2, hlam.le]
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) r hlam.le hi
  have he : {ξ : Fin M → ℝ | r ≤ X ξ} = {ξ | F ξ ≤ EF - r} := by
    ext ξ
    simp only [hXdef, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [he] at hch
  have hfin : (μ {ξ : Fin M → ℝ | F ξ ≤ EF - r}).toReal
      ≤ Real.exp (-(lam * r) +
        lam ^ 2 / (2 * (1 - lam * b / 3)) * ((∫ y, y ^ 2 ∂ν) * ∑ i, ℓ i ^ 2)) := by
    refine hch.trans ?_
    have hb2 := mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg (-lam * r))
    refine hb2.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  have hne : μ {ξ : Fin M → ℝ | F ξ ≤ EF - r} ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hfin


end Sandpile
