/-
The spatial modulus of the ball-stopped kernel.

The kernel of the ball-stopped field is `g_T(u,·)` minus the expected Green kernel from
the stopped position.  The first term has the Green kernel's own spatial modulus
(`MeanAIncrement.lean`).  The second term is an expectation along a motion started at `u`,
so two centres are compared along two different motions; what makes them comparable is
that the expectation of a bounded continuous reward of the stopped state does not depend
on the motion, only on its starting point (`LimStoppedTransfer.lean`).  Pairing the kernel
with a square integrable test function turns the Green kernel into such a reward, since
the pairing is bounded and continuous in the stopped state by the Green kernel's `L²`
modulus, and the transfer then rewrites the two expectations along one common motion,
where the two rewards differ only by a shift of the starting point.

The result is a modulus of exponent `1/8` in `L²` for the ball-stopped kernel, with a
constant that grows with the horizon but only polynomially.
-/
import Sandpile.Support.LimStoppedKernel
import Sandpile.Support.LimStoppedTransfer
import Sandpile.Support.MeanAIncrement
import Sandpile.Support.LimKernelShift
import Sandpile.Support.LimStoppedContinuity

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

/-! ### A quadratic bound for a pairing -/

theorem abs_mul_le_quad {f g a b : ℝ} (ha : 0 < a) (hab : a * b = 1) :
    |f * g| ≤ (a * f ^ 2 + b * g ^ 2) / 2 := by
  have h1 : (0 : ℝ) ≤ (a * |f| - |g|) ^ 2 := sq_nonneg _
  have h2 : |f| ^ 2 = f ^ 2 := sq_abs f
  have h3 : |g| ^ 2 = g ^ 2 := sq_abs g
  have habg : a * (b * g ^ 2) = g ^ 2 := by
    rw [← mul_assoc, hab, one_mul]
  have key : 2 * a * (|f| * |g|) ≤ a * (a * f ^ 2 + b * g ^ 2) := by
    have hexp : a * (a * f ^ 2 + b * g ^ 2) = a ^ 2 * f ^ 2 + g ^ 2 := by
      rw [mul_add, habg]
      ring
    rw [hexp]
    nlinarith [h1, h2, h3]
  rw [abs_mul]
  nlinarith [key, ha, mul_nonneg (abs_nonneg f) (abs_nonneg g)]

theorem abs_integral_mul_le_quad {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    {a b : ℝ} (ha : 0 < a) (hab : a * b = 1) :
    |∫ x, f x * g x ∂μ| ≤ (a * (∫ x, f x ^ 2 ∂μ) + b * ∫ x, g x ^ 2 ∂μ) / 2 := by
  have hb0 : 0 < b := by
    rcases lt_trichotomy b 0 with h | h | h
    · nlinarith
    · rw [h, mul_zero] at hab; norm_num at hab
    · exact h
  have hdom : ∀ x, ‖f x * g x‖ ≤ (a * f x ^ 2 + b * g x ^ 2) / 2 := by
    intro x
    rw [Real.norm_eq_abs]
    exact abs_mul_le_quad ha hab
  have hrhs : Integrable (fun x => (a * f x ^ 2 + b * g x ^ 2) / 2) μ :=
    (((hf.const_mul a).add (hg.const_mul b)).div_const 2)
  have hfg : Integrable (fun x => f x * g x) μ :=
    Integrable.mono' hrhs (hfm.mul hgm) (Eventually.of_forall hdom)
  have h1 : |∫ x, f x * g x ∂μ| ≤ ∫ x, ‖f x * g x‖ ∂μ := by
    simpa [Real.norm_eq_abs] using abs_integral_le_integral_abs (f := fun x => f x * g x)
  refine h1.trans ?_
  have h2 := integral_mono hfg.norm hrhs (fun x => hdom x)
  refine h2.trans (le_of_eq ?_)
  rw [integral_div, integral_add (hf.const_mul a) (hg.const_mul b), integral_const_mul,
    integral_const_mul]


/-! ### An explicit modulus constant for the Green kernel -/

section GreenFactor

variable {d : ℕ}

/-- The time factor `T^{1-(2d+1)/8}/(1-(2d+1)/8)` bounding `∫_0^T s^{-(2d+1)/8} ds`. -/
noncomputable def greenModulusFactor (d : ℕ) (T : ℝ) : ℝ :=
  T ^ (1 - (2 * (d : ℝ) + 1) / 8) / (1 - (2 * (d : ℝ) + 1) / 8)

theorem greenModulusFactor_nonneg (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ greenModulusFactor d T := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
  rw [greenModulusFactor]
  exact div_nonneg (Real.rpow_nonneg hT _) hc.le

theorem integral_Ioo_rpow_le_modulusFactor (hd3 : d ≤ 3) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8)) ≤ greenModulusFactor d T := by
  have hd' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hexp : (-1 : ℝ) < -(2 * (d : ℝ) + 1) / 8 := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hc : (0 : ℝ) < 1 - (2 * (d : ℝ) + 1) / 8 := by linarith
  have heq : (∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8))
      = ∫ s in (0 : ℝ)..t, s ^ (-(2 * (d : ℝ) + 1) / 8) := by
    rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  rw [heq, integral_rpow (Or.inl hexp)]
  have hval : -(2 * (d : ℝ) + 1) / 8 + 1 = 1 - (2 * (d : ℝ) + 1) / 8 := by ring
  rw [hval, Real.zero_rpow (by linarith), sub_zero, greenModulusFactor]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow ht htT hc.le) hc.le

/-- The explicit modulus constant of the Green kernel on `[0,T]`: it grows with the
horizon only polynomially. -/
noncomputable def greenModulusConst (d : ℕ) (T : ℝ) : ℝ :=
  2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) * greenModulusFactor d T ^ 2

theorem greenModulusConst_nonneg (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ greenModulusConst d T := by
  have h1 := (greenDiffConst_pos hd).le
  have h2 := greenModulusFactor_nonneg (d := d) hd3 hT
  rw [greenModulusConst]
  positivity

/-- **The spatial modulus of the Green kernel with an explicit constant.** -/
theorem integral_greenTimeBM_sub_sq_le' (hd : 1 ≤ d) (hd3 : d ≤ 3) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (x y : Space d) :
    (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d t y w) ^ 2)
      ≤ greenModulusConst d T * ‖x - y‖ ^ ((1 : ℝ) / 2) := by
  have hbase := integral_greenTimeBM_sub_sq_le hd hd3 ht x y
  refine hbase.trans ?_
  have hfac := integral_Ioo_rpow_le_modulusFactor (d := d) hd3 ht htT
  have hfac0 : (0 : ℝ) ≤ ∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg hr.1.le _
  have hC0 : (0 : ℝ) ≤ 2 * (greenDiffConst d * (2 : ℝ) ^ (-(2 * (d : ℝ) + 1) / 4)) := by
    have := (greenDiffConst_pos hd).le
    positivity
  have hx0 : (0 : ℝ) ≤ ‖x - y‖ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hsq : (∫ s in Set.Ioo (0 : ℝ) t, s ^ (-(2 * (d : ℝ) + 1) / 8)) ^ 2
      ≤ greenModulusFactor d T ^ 2 := by
    have hnn := greenModulusFactor_nonneg (d := d) hd3 (le_trans ht htT)
    nlinarith
  rw [greenModulusConst]
  nlinarith [hsq, hC0, hx0, mul_nonneg hC0 hx0]

end GreenFactor

/-! ### The pairing with the stopped Green kernel -/

section Pairing

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The uniform `L²` bound on the Green kernels up to the horizon. -/
noncomputable def greenSqBound (d : ℕ) (T : ℝ) : ℝ :=
  (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) *
    (greenTimeFactor d T * greenTimeFactor d T)

theorem integral_greenTimeBM_sq_le' (hd : 1 ≤ d) (hd3 : d ≤ 3) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (x : Space d) :
    (∫ w : Space d, greenTimeBM d t x w ^ 2) ≤ greenSqBound d T := by
  have h := integral_greenTimeBM_sq_le hd hd3 ht htT x
  have hrw : (∫ w : Space d, greenTimeBM d t x w ^ 2)
      = ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w := by
    simp_rw [sq]
  rw [hrw, greenSqBound]
  exact h

/-- **The pairing of a test function with an expected Green kernel** is the mean of its
pairings with the Green kernel from the sampled space-time point. -/
theorem integral_mul_expectedGreenKernel (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] (q : ΩB → ℝ≥0 × Space d) (hq : Measurable q) {T : ℝ}
    (hqT : ∀ b, ((q b).1 : ℝ) ≤ T) {ψ : Space d → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d))) :
    (∫ y : Space d, ψ y * ∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB)
      = ∫ b, (∫ y : Space d, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y) ∂PB := by
  classical
  have hjoint : Measurable
      (fun p : ΩB × Space d => greenTimeBM d ((q p.1).1 : ℝ) (q p.1).2 p.2) := by
    have hq' : Measurable (fun p : ΩB × Space d => (q p.1, p.2)) :=
      (hq.comp measurable_fst).prodMk measurable_snd
    have hm := (measurable_uncurry_greenTimeBM d).comp hq'
    exact hm
  have hfsq : ∀ b, Integrable (fun y : Space d => greenTimeBM d ((q b).1 : ℝ) (q b).2 y ^ 2)
      (volume : Measure (Space d)) := by
    intro b
    have hmem := memLp_greenTimeBM hd hd3 (q b).1.property (q b).2
    exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have hfbound : ∀ b, (∫ y : Space d, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ^ 2)
      ≤ greenSqBound d T := fun b =>
    integral_greenTimeBM_sq_le' hd hd3 (q b).1.property (hqT b) (q b).2
  have hdom : ∀ (b : ΩB) (y : Space d),
      ‖ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y‖
        ≤ (ψ y ^ 2 + greenTimeBM d ((q b).1 : ℝ) (q b).2 y ^ 2) / 2 := by
    intro b y
    rw [Real.norm_eq_abs]
    have h := abs_mul_le_quad (f := ψ y) (g := greenTimeBM d ((q b).1 : ℝ) (q b).2 y)
      one_pos (by norm_num : (1 : ℝ) * 1 = 1)
    simpa using h
  have hslice : ∀ b, Integrable
      (fun y : Space d => ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y)
      (volume : Measure (Space d)) := by
    intro b
    refine Integrable.mono' ((hψ.add (hfsq b)).div_const 2)
      ((hψm.mul (measurable_greenTimeBM (q b).1.property (q b).2)).aestronglyMeasurable) ?_
    filter_upwards with y
    exact hdom b y
  have hnormint : Integrable
      (fun b => ∫ y : Space d, ‖ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y‖) PB := by
    have hmeas : StronglyMeasurable
        (fun b => ∫ y : Space d, ‖ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y‖) := by
      have h : StronglyMeasurable
          (fun p : ΩB × Space d => ‖ψ p.2 * greenTimeBM d ((q p.1).1 : ℝ) (q p.1).2 p.2‖) :=
        (((hψm.comp measurable_snd).mul hjoint).norm).stronglyMeasurable
      exact h.integral_prod_right'
    refine Integrable.mono' (integrable_const
      (((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2)) hmeas.aestronglyMeasurable ?_
    filter_upwards with b
    have hle : (∫ y : Space d, ‖ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y‖)
        ≤ ((∫ y : Space d, ψ y ^ 2)
            + ∫ y : Space d, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ^ 2) / 2 := by
      have hmono := integral_mono (hslice b).norm ((hψ.add (hfsq b)).div_const 2) (hdom b)
      refine hmono.trans (le_of_eq ?_)
      simp only [Pi.add_apply]
      rw [integral_div, integral_add hψ (hfsq b)]
    have hnn : (0 : ℝ) ≤ ∫ y : Space d, ‖ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y‖ :=
      integral_nonneg fun y => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    refine hle.trans ?_
    have := hfbound b
    linarith
  have hprod : Integrable (Function.uncurry
      (fun b (y : Space d) => ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y))
      (PB.prod (volume : Measure (Space d))) := by
    refine (integrable_prod_iff ?_).mpr ⟨Eventually.of_forall hslice, hnormint⟩
    exact ((hψm.comp measurable_snd).mul hjoint).aestronglyMeasurable
  have hswap := integral_integral_swap hprod
  have hinner : ∀ y : Space d, ψ y * (∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB)
      = ∫ b, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB := by
    intro y
    rw [integral_const_mul]
  calc (∫ y : Space d, ψ y * ∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB)
      = ∫ y : Space d, (∫ b, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB) :=
        integral_congr_ae (Eventually.of_forall hinner)
    _ = ∫ b, (∫ y : Space d, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y) ∂PB := hswap.symm

end Pairing

/-! ### The pairing as a reward of the stopped state -/

/-- The pairing of a test function with the Green kernel of the remaining time from a
space-time point, as a function of the stopped state. -/
noncomputable def greenReward (d : ℕ) (ψ : Space d → ℝ) (T : ℝ) (x : Space d)
    (p : ℝ≥0 × Space d) : ℝ :=
  ∫ y : Space d, ψ y * greenTimeBM d (max (T - (p.1 : ℝ)) 0) (x + p.2) y

section Reward

variable {d : ℕ}

theorem abs_greenReward_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T) {ψ : Space d → ℝ}
    (hψm : Measurable ψ) (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d)))
    (x : Space d) (p : ℝ≥0 × Space d) :
    |greenReward d ψ T x p| ≤ ((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2 := by
  have ht0 : (0 : ℝ) ≤ max (T - (p.1 : ℝ)) 0 := le_max_right _ _
  have htT : max (T - (p.1 : ℝ)) 0 ≤ T := by
    refine max_le ?_ hT
    have : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property
    linarith
  have hmem := memLp_greenTimeBM hd hd3 ht0 (x + p.2)
  have hgsq : Integrable (fun y : Space d => greenTimeBM d (max (T - (p.1 : ℝ)) 0) (x + p.2) y ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
  have h := abs_integral_mul_le_quad (f := ψ)
    (g := fun y : Space d => greenTimeBM d (max (T - (p.1 : ℝ)) 0) (x + p.2) y)
    hψ hgsq hψm.aestronglyMeasurable
    (measurable_greenTimeBM ht0 (x + p.2)).aestronglyMeasurable one_pos
    (by norm_num : (1 : ℝ) * 1 = 1)
  simp only [one_mul] at h
  refine h.trans ?_
  have hb := integral_greenTimeBM_sq_le' hd hd3 ht0 htT (x + p.2)
  have : (0 : ℝ) ≤ 2 := by norm_num
  linarith [hb]

/-- The general bound on an increment of the reward: the `L²` distance of the two Green
kernels, paired against the test function. -/
theorem abs_greenReward_sub_le_general (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (_hT : 0 ≤ T)
    {ψ : Space d → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d)))
    (x x' : Space d) (p p' : ℝ≥0 × Space d) {a b : ℝ} (ha : 0 < a) (hab : a * b = 1) :
    |greenReward d ψ T x p - greenReward d ψ T x' p'|
      ≤ (a * (∫ y : Space d, ψ y ^ 2)
          + b * ∫ y : Space d, (greenTimeBM d (max (T - (p.1 : ℝ)) 0) (x + p.2) y
              - greenTimeBM d (max (T - (p'.1 : ℝ)) 0) (x' + p'.2) y) ^ 2) / 2 := by
  set t : ℝ := max (T - (p.1 : ℝ)) 0 with htdef
  set t' : ℝ := max (T - (p'.1 : ℝ)) 0 with ht'def
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have ht0' : (0 : ℝ) ≤ t' := le_max_right _ _
  have hmem := memLp_greenTimeBM hd hd3 ht0 (x + p.2)
  have hmem' := memLp_greenTimeBM hd hd3 ht0' (x' + p'.2)
  have hgsq : Integrable
      (fun y : Space d => (greenTimeBM d t (x + p.2) y - greenTimeBM d t' (x' + p'.2) y) ^ 2)
      (volume : Measure (Space d)) := by
    have hsub : MemLp (fun y : Space d =>
        greenTimeBM d t (x + p.2) y - greenTimeBM d t' (x' + p'.2) y) 2
        (volume : Measure (Space d)) := hmem.sub hmem'
    exact (memLp_two_iff_integrable_sq hsub.aestronglyMeasurable).mp hsub
  have hmeas : Measurable (fun y : Space d =>
      greenTimeBM d t (x + p.2) y - greenTimeBM d t' (x' + p'.2) y) :=
    (measurable_greenTimeBM ht0 (x + p.2)).sub (measurable_greenTimeBM ht0' (x' + p'.2))
  have hslice : ∀ (r : ℝ) (hr : 0 ≤ r) (z : Space d),
      Integrable (fun y : Space d => ψ y * greenTimeBM d r z y) (volume : Measure (Space d)) := by
    intro r hr z
    have hm := memLp_greenTimeBM hd hd3 hr z
    have hgs : Integrable (fun y : Space d => greenTimeBM d r z y ^ 2)
        (volume : Measure (Space d)) :=
      (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm
    refine Integrable.mono' ((hψ.add hgs).div_const 2)
      ((hψm.mul (measurable_greenTimeBM hr z)).aestronglyMeasurable) ?_
    filter_upwards with y
    have h := abs_mul_le_quad (f := ψ y) (g := greenTimeBM d r z y) one_pos
      (by norm_num : (1 : ℝ) * 1 = 1)
    simpa using h
  have hsub : greenReward d ψ T x p - greenReward d ψ T x' p'
      = ∫ y : Space d, ψ y * (greenTimeBM d t (x + p.2) y - greenTimeBM d t' (x' + p'.2) y) := by
    rw [greenReward, greenReward, ← integral_sub (hslice t ht0 (x + p.2))
      (hslice t' ht0' (x' + p'.2))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [hsub]
  exact abs_integral_mul_le_quad (f := ψ)
    (g := fun y : Space d => greenTimeBM d t (x + p.2) y - greenTimeBM d t' (x' + p'.2) y)
    hψ hgsq hψm.aestronglyMeasurable hmeas.aestronglyMeasurable ha hab

/-- The increment of the reward between two centres is controlled by the Green kernel's
own spatial modulus, with the explicit constant. -/
theorem abs_greenReward_sub_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T)
    {ψ : Space d → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d)))
    (x x' : Space d) (p : ℝ≥0 × Space d) :
    |greenReward d ψ T x p - greenReward d ψ T x' p|
      ≤ ((∫ y : Space d, ψ y ^ 2)
          + greenModulusConst d T * ‖x - x'‖ ^ ((1 : ℝ) / 2)) / 2 := by
  have hgen := abs_greenReward_sub_le_general hd hd3 hT hψm hψ x x' p p one_pos
    (by norm_num : (1 : ℝ) * 1 = 1)
  simp only [one_mul] at hgen
  refine hgen.trans ?_
  set t : ℝ := max (T - (p.1 : ℝ)) 0 with htdef
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have htT : t ≤ T := by
    refine max_le ?_ hT
    have : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property
    linarith
  have hmod := integral_greenTimeBM_sub_sq_le' hd hd3 ht0 htT (x + p.2) (x' + p.2)
  have hdiff : (x + p.2) - (x' + p.2) = x - x' := by abel
  rw [hdiff] at hmod
  linarith

/-- **The reward is continuous**, by the Green kernel's `L²` modulus. -/
theorem continuous_greenReward (hd : 1 ≤ d) (hd3 : d ≤ 3) {T : ℝ} (hT : 0 ≤ T)
    {ψ : Space d → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d)))
    {M : ℝ} (hM : 0 ≤ M)
    (hMod : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y : Space d,
      (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d s y w) ^ 2)
        ≤ M * (max |t - s| ‖x - y‖) ^ ((1 : ℝ) / 4))
    (x : Space d) : Continuous (greenReward d ψ T x) := by
  have hA0 : (0 : ℝ) ≤ ∫ y : Space d, ψ y ^ 2 := integral_nonneg fun y => sq_nonneg _
  rw [Metric.continuous_iff]
  intro p₀ ε hε
  set A : ℝ := ∫ y : Space d, ψ y ^ 2 with hAdef
  set lam : ℝ := ε / (A + 1) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef]
    positivity
  refine ⟨min 1 ((lam * ε / (M + 1)) ^ 4), by positivity, ?_⟩
  intro p hp
  have hp1 : dist p p₀ < 1 := lt_of_lt_of_le hp (min_le_left _ _)
  have hp2 : dist p p₀ < (lam * ε / (M + 1)) ^ 4 := lt_of_lt_of_le hp (min_le_right _ _)
  -- the two space-time points
  set t : ℝ := max (T - (p.1 : ℝ)) 0 with htdef
  set t₀ : ℝ := max (T - (p₀.1 : ℝ)) 0 with ht₀def
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have ht₀0 : (0 : ℝ) ≤ t₀ := le_max_right _ _
  have htT : t ≤ T := by
    refine max_le ?_ hT
    have : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.property
    linarith
  have ht₀T : t₀ ≤ T := by
    refine max_le ?_ hT
    have : (0 : ℝ) ≤ (p₀.1 : ℝ) := p₀.1.property
    linarith
  have hdt : |t - t₀| ≤ dist p p₀ := by
    have h1 : |t - t₀| ≤ |(T - (p.1 : ℝ)) - (T - (p₀.1 : ℝ))| := by
      rw [htdef, ht₀def]
      exact abs_sup_sub_sup_le_abs _ _ _
    have h2 : |(T - (p.1 : ℝ)) - (T - (p₀.1 : ℝ))| = |(p.1 : ℝ) - (p₀.1 : ℝ)| := by
      rw [show (T - (p.1 : ℝ)) - (T - (p₀.1 : ℝ)) = -((p.1 : ℝ) - (p₀.1 : ℝ)) by ring, abs_neg]
    rw [h2] at h1
    refine h1.trans ?_
    have hd1 : dist p.1 p₀.1 ≤ dist p p₀ := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    rwa [NNReal.dist_eq] at hd1
  have hdz : ‖(x + p.2) - (x + p₀.2)‖ ≤ dist p p₀ := by
    have hrw : (x + p.2) - (x + p₀.2) = p.2 - p₀.2 := by abel
    rw [hrw, ← dist_eq_norm]
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hmod := hMod t ⟨ht0, htT⟩ t₀ ⟨ht₀0, ht₀T⟩ (x + p.2) (x + p₀.2)
  have hmax : max |t - t₀| ‖(x + p.2) - (x + p₀.2)‖ ≤ dist p p₀ := max_le hdt hdz
  have hgen := abs_greenReward_sub_le_general hd hd3 hT hψm hψ x x p p₀ hlam
    (by field_simp : lam * lam⁻¹ = 1)
  rw [dist_eq_norm, ← Real.norm_eq_abs] at *
  have hbound : ‖greenReward d ψ T x p - greenReward d ψ T x p₀‖
      ≤ (lam * A + lam⁻¹ * (M * (dist p p₀) ^ ((1 : ℝ) / 4))) / 2 := by
    refine hgen.trans ?_
    have hstep : (∫ y : Space d, (greenTimeBM d t (x + p.2) y
        - greenTimeBM d t₀ (x + p₀.2) y) ^ 2) ≤ M * (dist p p₀) ^ ((1 : ℝ) / 4) := by
      refine hmod.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hM
      refine Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg _)) hmax (by norm_num)
    have hinv : (0 : ℝ) < lam⁻¹ := inv_pos.mpr hlam
    have := mul_le_mul_of_nonneg_left hstep hinv.le
    linarith
  refine lt_of_le_of_lt hbound ?_
  have h1 : lam * A < ε := by
    rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have h2 : lam⁻¹ * (M * (dist p p₀) ^ ((1 : ℝ) / 4)) ≤ ε := by
    have hd0 : (0 : ℝ) ≤ dist p p₀ := dist_nonneg
    have hle : (dist p p₀) ^ ((1 : ℝ) / 4) ≤ lam * ε / (M + 1) := by
      have hpow : (dist p p₀) ^ ((1 : ℝ) / 4)
          ≤ (((lam * ε / (M + 1)) ^ 4) : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hd0 hp2.le (by norm_num)
      refine hpow.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast (lam * ε / (M + 1)) 4, ← Real.rpow_mul (by positivity)]
      norm_num
    have hM1 : (0 : ℝ) < M + 1 := by linarith
    have hstep : M * (dist p p₀) ^ ((1 : ℝ) / 4) ≤ M * (lam * ε / (M + 1)) :=
      mul_le_mul_of_nonneg_left hle hM
    have hstep2 : M * (lam * ε / (M + 1)) ≤ lam * ε := by
      rw [mul_div_assoc'] at *
      rw [div_le_iff₀ hM1]
      nlinarith [mul_pos hlam hε]
    have hinv : (0 : ℝ) < lam⁻¹ := inv_pos.mpr hlam
    calc lam⁻¹ * (M * (dist p p₀) ^ ((1 : ℝ) / 4)) ≤ lam⁻¹ * (lam * ε) := by
          refine mul_le_mul_of_nonneg_left (hstep.trans hstep2) hinv.le
      _ = ε := by field_simp
  linarith

end Reward

/-! ### The modulus of the stopped Green kernel -/

section Modulus

variable {ΩB : Type} [MeasurableSpace ΩB] {d : ℕ}

theorem stronglyMeasurable_stoppedGreenKernel (_hd : 1 ≤ d) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 ≤ T) (u : Space 2) :
    StronglyMeasurable (stoppedGreenKernel d PB B s T u) := by
  have hτm : Measurable (ballStopTime d B s T u) := measurable_ballStopTime hBc hBm s T u
  have hτT : ∀ b, ballStopTime d B s T u b ≤ T.toNNReal := ballStopTime_le B s T u
  set q : ΩB → ℝ≥0 × Space d := fun b =>
    ((⟨((T.toNNReal : ℝ≥0) : ℝ) - ballStopTime d B s T u b,
        sub_nonneg.mpr (by exact_mod_cast hτT b)⟩ : ℝ≥0),
      B (planePoint u) (ballStopTime d B s T u b) b) with hqdef
  have hq : Measurable q :=
    measurable_stopped_spaceTime (B (planePoint u)) (hBc _) (hBm _)
      (ballStopTime d B s T u) hτm T.toNNReal hτT
  have hqreal : ∀ b, ((q b).1 : ℝ) = T - (ballStopTime d B s T u b : ℝ) := by
    intro b
    show ((T.toNNReal : ℝ≥0) : ℝ) - (ballStopTime d B s T u b : ℝ) = _
    rw [Real.coe_toNNReal T hT]
  have hqsnd : ∀ b, (q b).2 = B (planePoint u) (ballStopTime d B s T u b) b := fun b => rfl
  have hm := (measurable_uncurry_greenTimeBM d).comp
    ((hq.comp (measurable_snd (α := Space d) (β := ΩB))).prodMk measurable_fst)
  have hres := hm.stronglyMeasurable.integral_prod_right' (ν := PB)
  have hco : stoppedGreenKernel d PB B s T u
      = fun y : Space d => ∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB := by
    funext y
    show (∫ b, greenTimeBM d (T - (ballStopTime d B s T u b : ℝ))
        (B (planePoint u) (ballStopTime d B s T u b) b) y ∂PB) = _
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    show greenTimeBM d (T - (ballStopTime d B s T u b : ℝ))
        (B (planePoint u) (ballStopTime d B s T u b) b) y
      = greenTimeBM d ((q b).1 : ℝ) (q b).2 y
    rw [hqreal b, hqsnd b]
  rw [hco]
  exact hres

/-- The pairing with the stopped Green kernel is the mean of the reward at the stopped
state. -/
theorem integral_mul_stoppedGreenKernel_eq (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hBc : ∀ y ω, Continuous fun t => B y t ω) (hBm : ∀ y t, StronglyMeasurable (B y t))
    {s T : ℝ} (hT : 0 ≤ T) (u : Space 2) {ψ : Space d → ℝ} (hψm : Measurable ψ)
    (hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d))) :
    (∫ y : Space d, ψ y * stoppedGreenKernel d PB B s T u y)
      = ∫ b, greenReward d ψ T (planePoint u)
          (ballStopTime d B s T u b,
            B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) ∂PB := by
  have hτm : Measurable (ballStopTime d B s T u) := measurable_ballStopTime hBc hBm s T u
  have hτT : ∀ b, ballStopTime d B s T u b ≤ T.toNNReal := ballStopTime_le B s T u
  have hτreal : ∀ b, ((ballStopTime d B s T u b : ℝ)) ≤ T := fun b =>
    ballStopTime_le_real B hT u b
  have hq : Measurable (fun b : ΩB =>
      ((⟨((T.toNNReal : ℝ≥0) : ℝ) - ballStopTime d B s T u b,
          sub_nonneg.mpr (by exact_mod_cast hτT b)⟩ : ℝ≥0),
        B (planePoint u) (ballStopTime d B s T u b) b)) :=
    measurable_stopped_spaceTime (B (planePoint u)) (hBc _) (hBm _)
      (ballStopTime d B s T u) hτm T.toNNReal hτT
  set q : ΩB → ℝ≥0 × Space d := fun b =>
    ((⟨((T.toNNReal : ℝ≥0) : ℝ) - ballStopTime d B s T u b,
        sub_nonneg.mpr (by exact_mod_cast hτT b)⟩ : ℝ≥0),
      B (planePoint u) (ballStopTime d B s T u b) b) with hqdef
  have hqreal : ∀ b, ((q b).1 : ℝ) = T - (ballStopTime d B s T u b : ℝ) := by
    intro b
    show ((T.toNNReal : ℝ≥0) : ℝ) - (ballStopTime d B s T u b : ℝ)
      = T - (ballStopTime d B s T u b : ℝ)
    rw [Real.coe_toNNReal T hT]
  have hqsnd : ∀ b, (q b).2 = B (planePoint u) (ballStopTime d B s T u b) b := fun b => rfl
  have hqT : ∀ b, ((q b).1 : ℝ) ≤ T := by
    intro b
    rw [hqreal b]
    have : (0 : ℝ) ≤ (ballStopTime d B s T u b : ℝ) := (ballStopTime d B s T u b).property
    linarith
  have hmain := integral_mul_expectedGreenKernel hd hd3 PB q hq (T := T) hqT hψm hψ
  have hleft : (∫ y : Space d, ψ y * stoppedGreenKernel d PB B s T u y)
      = ∫ y : Space d, ψ y * ∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show ψ y * stoppedGreenKernel d PB B s T u y
        = ψ y * ∫ b, greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB
    congr 1
    show (∫ b, greenTimeBM d (T - (ballStopTime d B s T u b : ℝ))
        (B (planePoint u) (ballStopTime d B s T u b) b) y ∂PB) = _
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    show greenTimeBM d (T - (ballStopTime d B s T u b : ℝ))
        (B (planePoint u) (ballStopTime d B s T u b) b) y
      = greenTimeBM d ((q b).1 : ℝ) (q b).2 y
    rw [hqreal b]
  have hright : ∀ b, (∫ y : Space d, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y)
      = greenReward d ψ T (planePoint u)
          (ballStopTime d B s T u b,
            B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) := by
    intro b
    have h1 : ((q b).1 : ℝ) = max (T - (ballStopTime d B s T u b : ℝ)) 0 := by
      rw [hqreal b]
      exact (max_eq_left (by linarith [hτreal b])).symm
    have h2 : (q b).2
        = planePoint u + (B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) := by
      rw [hqsnd b]
      abel
    show (∫ y : Space d, ψ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y)
        = ∫ y : Space d, ψ y * greenTimeBM d
            (max (T - (ballStopTime d B s T u b : ℝ)) 0)
            (planePoint u + (B (planePoint u) (ballStopTime d B s T u b) b - planePoint u)) y
    rw [h1, h2]
  rw [hleft, hmain]
  exact integral_congr_ae (Eventually.of_forall hright)

/-- **The spatial modulus of the stopped Green kernel**: the `L²` distance of the kernels
at two centres is controlled by the Green kernel's own modulus. -/
theorem integral_sq_stoppedGreenKernel_sub_le (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u v : Space 2) :
    (∫ y : Space d, (stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y) ^ 2)
      ≤ greenModulusConst d T * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 2) := by
  classical
  obtain ⟨M, hM, hMod⟩ := exists_greenTimeBM_holder hd hd3 hT
  set ψ : Space d → ℝ := fun y =>
    stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y with hψdef
  have hsmU := stronglyMeasurable_stoppedGreenKernel hd PB hBc hBm (s := s) hT.le u
  have hsmV := stronglyMeasurable_stoppedGreenKernel hd PB hBc hBm (s := s) hT.le v
  have hψm : Measurable ψ := hsmU.measurable.sub hsmV.measurable
  have hmemU := memLp_stoppedGreenKernel hd hd3 PB hBc hBm (s := s) hT.le u
  have hmemV := memLp_stoppedGreenKernel hd hd3 PB hBc hBm (s := s) hT.le v
  have hψmem : MemLp ψ 2 (volume : Measure (Space d)) := hmemU.sub hmemV
  have hψ : Integrable (fun y => ψ y ^ 2) (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hψmem.aestronglyMeasurable).mp hψmem
  have hUsq : Integrable (fun y => stoppedGreenKernel d PB B s T u y ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemU.aestronglyMeasurable).mp hmemU
  have hVsq : Integrable (fun y => stoppedGreenKernel d PB B s T v y ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemV.aestronglyMeasurable).mp hmemV
  -- the two pairings are integrable
  have hmulU : Integrable (fun y => ψ y * stoppedGreenKernel d PB B s T u y)
      (volume : Measure (Space d)) := by
    refine Integrable.mono' ((hψ.add hUsq).div_const 2)
      ((hψm.mul hsmU.measurable).aestronglyMeasurable) ?_
    filter_upwards with y
    have h := abs_mul_le_quad (f := ψ y) (g := stoppedGreenKernel d PB B s T u y) one_pos
      (by norm_num : (1 : ℝ) * 1 = 1)
    simpa using h
  have hmulV : Integrable (fun y => ψ y * stoppedGreenKernel d PB B s T v y)
      (volume : Measure (Space d)) := by
    refine Integrable.mono' ((hψ.add hVsq).div_const 2)
      ((hψm.mul hsmV.measurable).aestronglyMeasurable) ?_
    filter_upwards with y
    have h := abs_mul_le_quad (f := ψ y) (g := stoppedGreenKernel d PB B s T v y) one_pos
      (by norm_num : (1 : ℝ) * 1 = 1)
    simpa using h
  have hsplit : (∫ y : Space d, ψ y ^ 2)
      = (∫ y : Space d, ψ y * stoppedGreenKernel d PB B s T u y)
        - ∫ y : Space d, ψ y * stoppedGreenKernel d PB B s T v y := by
    rw [← integral_sub hmulU hmulV]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hψdef]
    ring
  -- the pairings as rewards, and the transfer
  have hpairU := integral_mul_stoppedGreenKernel_eq hd hd3 PB hBc hBm (s := s) hT.le u hψm hψ
  have hpairV := integral_mul_stoppedGreenKernel_eq hd hd3 PB hBc hBm (s := s) hT.le v hψm hψ
  have hcont := continuous_greenReward hd hd3 hT.le hψm hψ hM hMod (planePoint u)
  have hbdd : ∀ p, |greenReward d ψ T (planePoint u) p|
      ≤ ((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2 :=
    fun p => abs_greenReward_le hd hd3 hT.le hψm hψ (planePoint u) p
  have hTne : T.toNNReal ≠ 0 := by
    simp only [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hT
  have htrans0 := integral_stoppedState_eq (hB (planePoint u)) (hB (planePoint v))
    (hBm _) (hBm _) (hBc _) (hBc _) (s := s) hTne hcont hbdd
  have htrans : (∫ b, greenReward d ψ T (planePoint u)
        (ballStopTime d B s T u b,
          B (planePoint u) (ballStopTime d B s T u b) b - planePoint u) ∂PB)
      = ∫ b, greenReward d ψ T (planePoint u)
        (ballStopTime d B s T v b,
          B (planePoint v) (ballStopTime d B s T v b) b - planePoint v) ∂PB := htrans0
  -- both rewards at the `v` state are integrable
  have hstateV := measurable_stoppedState hBc hBm s T v
  have hintU : Integrable (fun b => greenReward d ψ T (planePoint u)
      (ballStopTime d B s T v b,
        B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)) PB := by
    refine Integrable.mono' (integrable_const (((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2))
      ((hcont.measurable.comp hstateV).aestronglyMeasurable) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs]
    exact hbdd _
  have hcontV := continuous_greenReward hd hd3 hT.le hψm hψ hM hMod (planePoint v)
  have hbddV : ∀ p, |greenReward d ψ T (planePoint v) p|
      ≤ ((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2 :=
    fun p => abs_greenReward_le hd hd3 hT.le hψm hψ (planePoint v) p
  have hintV : Integrable (fun b => greenReward d ψ T (planePoint v)
      (ballStopTime d B s T v b,
        B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)) PB := by
    refine Integrable.mono' (integrable_const (((∫ y : Space d, ψ y ^ 2) + greenSqBound d T) / 2))
      ((hcontV.measurable.comp hstateV).aestronglyMeasurable) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs]
    exact hbddV _
  have hkey : (∫ y : Space d, ψ y ^ 2)
      = ∫ b, (greenReward d ψ T (planePoint u)
            (ballStopTime d B s T v b,
              B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)
          - greenReward d ψ T (planePoint v)
            (ballStopTime d B s T v b,
              B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)) ∂PB := by
    rw [integral_sub hintU hintV, hsplit, hpairU, hpairV, htrans]
  -- the uniform bound on the reward increment
  have hunif : ∀ b, |greenReward d ψ T (planePoint u)
      (ballStopTime d B s T v b,
        B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)
      - greenReward d ψ T (planePoint v)
      (ballStopTime d B s T v b,
        B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)|
      ≤ ((∫ y : Space d, ψ y ^ 2)
          + greenModulusConst d T
            * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 2)) / 2 :=
    fun b => abs_greenReward_sub_le hd hd3 hT.le hψm hψ (planePoint u) (planePoint v) _
  have h1 : (∫ y : Space d, ψ y ^ 2)
      ≤ ∫ b, |greenReward d ψ T (planePoint u)
            (ballStopTime d B s T v b,
              B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)
          - greenReward d ψ T (planePoint v)
            (ballStopTime d B s T v b,
              B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)| ∂PB := by
    rw [hkey]
    exact le_trans (le_abs_self _) abs_integral_le_integral_abs
  have h2 : (∫ b, |greenReward d ψ T (planePoint u)
        (ballStopTime d B s T v b,
          B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)
      - greenReward d ψ T (planePoint v)
        (ballStopTime d B s T v b,
          B (planePoint v) (ballStopTime d B s T v b) b - planePoint v)| ∂PB)
      ≤ ((∫ y : Space d, ψ y ^ 2)
          + greenModulusConst d T
            * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 2)) / 2 := by
    refine le_trans (integral_mono (hintU.sub hintV).abs (integrable_const _) hunif) ?_
    rw [integral_const, measureReal_def, measure_univ]
    simp
  have hbound := h1.trans h2
  linarith

/-- **The spatial modulus of the ball-stopped kernel.** -/
theorem integral_sq_ballStoppedKernel_sub_le (hd : 1 ≤ d) (hd3 : d ≤ 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u v : Space 2) :
    (∫ y : Space d, (ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) ^ 2)
      ≤ 4 * greenModulusConst d T
          * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 2) := by
  have hgreen := integral_greenTimeBM_sub_sq_le' hd hd3 hT.le le_rfl
    (planePoint (d := d) u) (planePoint (d := d) v)
  have hstop := integral_sq_stoppedGreenKernel_sub_le hd hd3 PB hB hBc hBm (s := s) hT u v
  have hmemG : MemLp (fun w : Space d =>
      greenTimeBM d T (planePoint u) w - greenTimeBM d T (planePoint v) w) 2
      (volume : Measure (Space d)) :=
    (memLp_greenTimeBM hd hd3 hT.le (planePoint u)).sub
      (memLp_greenTimeBM hd hd3 hT.le (planePoint v))
  have hmemS : MemLp (fun y : Space d =>
      stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y) 2
      (volume : Measure (Space d)) :=
    (memLp_stoppedGreenKernel hd hd3 PB hBc hBm (s := s) hT.le u).sub
      (memLp_stoppedGreenKernel hd hd3 PB hBc hBm (s := s) hT.le v)
  have hmemK : MemLp (fun y : Space d =>
      ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) 2
      (volume : Measure (Space d)) :=
    (memLp_ballStoppedKernel hd hd3 PB hBc hBm hT.le u).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hT.le v)
  have hGint : Integrable (fun w : Space d =>
      (greenTimeBM d T (planePoint u) w - greenTimeBM d T (planePoint v) w) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemG.aestronglyMeasurable).mp hmemG
  have hSint : Integrable (fun y : Space d =>
      (stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemS.aestronglyMeasurable).mp hmemS
  have hKint : Integrable (fun y : Space d =>
      (ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemK.aestronglyMeasurable).mp hmemK
  have hpt : ∀ y : Space d,
      (ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) ^ 2
        ≤ 2 * (greenTimeBM d T (planePoint u) y - greenTimeBM d T (planePoint v) y) ^ 2
          + 2 * (stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y) ^ 2 := by
    intro y
    have hrw : ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y
        = (greenTimeBM d T (planePoint u) y - greenTimeBM d T (planePoint v) y)
          - (stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y) := by
      show (greenTimeBM d T (planePoint u) y - stoppedGreenKernel d PB B s T u y)
          - (greenTimeBM d T (planePoint v) y - stoppedGreenKernel d PB B s T v y) = _
      ring
    rw [hrw]
    nlinarith [sq_nonneg ((greenTimeBM d T (planePoint u) y - greenTimeBM d T (planePoint v) y)
      + (stoppedGreenKernel d PB B s T u y - stoppedGreenKernel d PB B s T v y))]
  have hmono := integral_mono hKint ((hGint.const_mul 2).add (hSint.const_mul 2)) hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hGint.const_mul 2) (hSint.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- **The spatial modulus of the kernel of the difference field.**  The kernel of
`2d(𝒳_{s,T} − 𝒳_s)` at two centres differs in `L²` by the sum of the ball kernel's own
modulus and the ball-stopped kernel's, the second constant growing with the horizon only
polynomially. -/
theorem integral_sq_diffKernel_sub_le (hdd : d = 2 ∨ d = 3) (PB : Measure ΩB)
    [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hs : 0 < s) (hT : 0 < T)
    (u v : Space 2)
    (hw1 : ‖planePoint (d := d) u - planePoint (d := d) v‖ ≤ s)
    (hw2 : ‖planePoint (d := d) u - planePoint (d := d) v‖ ≤ 1) :
    (∫ y : Space d, ((2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
      ≤ 2 * (2 * (d : ℝ)) ^ 2 * kernelShiftL2Const d s
          * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 3)
        + 8 * greenModulusConst d T
          * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 2) := by
  have hd : 1 ≤ d := by rcases hdd with rfl | rfl <;> norm_num
  have hd3 : d ≤ 3 := by rcases hdd with rfl | rfl <;> norm_num
  have hball := integral_sq_ballKernel_sub_le hdd hs u v hw1 hw2
  have hstop := integral_sq_ballStoppedKernel_sub_le hd hd3 PB hB hBc hBm (s := s) hT u v
  have hmemB : MemLp (fun y : Space d => ballKernel d s u y - ballKernel d s v y) 2
      (volume : Measure (Space d)) := (memLp_ballKernel hdd hs u).sub (memLp_ballKernel hdd hs v)
  have hmemK : MemLp (fun y : Space d =>
      ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) 2
      (volume : Measure (Space d)) :=
    (memLp_ballStoppedKernel hd hd3 PB hBc hBm hT.le u).sub
      (memLp_ballStoppedKernel hd hd3 PB hBc hBm hT.le v)
  have hmemD : MemLp (fun y : Space d =>
      (2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) 2
      (volume : Measure (Space d)) := by
    have h1 : MemLp (fun y : Space d => 2 * (d : ℝ) * (ballKernel d s u y - ballKernel d s v y)) 2
        (volume : Measure (Space d)) := hmemB.const_mul _
    have hthis := h1.sub hmemK
    refine MemLp.ae_eq ?_ hthis
    filter_upwards with y
    simp only [Pi.sub_apply]
    ring
  have hBint : Integrable (fun y : Space d => (ballKernel d s u y - ballKernel d s v y) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemB.aestronglyMeasurable).mp hmemB
  have hKint : Integrable (fun y : Space d =>
      (ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemK.aestronglyMeasurable).mp hmemK
  have hDint : Integrable (fun y : Space d =>
      ((2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2)
      (volume : Measure (Space d)) :=
    (memLp_two_iff_integrable_sq hmemD.aestronglyMeasurable).mp hmemD
  have hpt : ∀ y : Space d,
      ((2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) ^ 2
        ≤ 2 * (2 * (d : ℝ)) ^ 2 * (ballKernel d s u y - ballKernel d s v y) ^ 2
          + 2 * (ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y) ^ 2 := by
    intro y
    set a : ℝ := 2 * (d : ℝ) * (ballKernel d s u y - ballKernel d s v y) with hadef
    set b : ℝ := ballStoppedKernel d PB B s T u y - ballStoppedKernel d PB B s T v y with hbdef
    have hrw : ((2 * (d : ℝ) * ballKernel d s u y - ballStoppedKernel d PB B s T u y)
        - (2 * (d : ℝ) * ballKernel d s v y - ballStoppedKernel d PB B s T v y)) = a - b := by
      rw [hadef, hbdef]
      ring
    have hasq : a ^ 2 = (2 * (d : ℝ)) ^ 2 * (ballKernel d s u y - ballKernel d s v y) ^ 2 := by
      rw [hadef]
      ring
    rw [hrw]
    nlinarith [sq_nonneg (a + b), hasq]
  have hmono := integral_mono hDint
    ((hBint.const_mul (2 * (2 * (d : ℝ)) ^ 2)).add (hKint.const_mul 2)) hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hBint.const_mul _) (hKint.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono
  have hb0 : (0 : ℝ) ≤ 2 * (2 * (d : ℝ)) ^ 2 := by positivity
  nlinarith [hmono, hball, hstop, mul_le_mul_of_nonneg_left hball hb0]


end Modulus

end Sandpile.Support
