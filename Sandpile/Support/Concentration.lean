import Sandpile.Support.FiniteCoord
import LatticeProb.Prob.LpSmooth
import LatticeProb.Prob.EfronSteinInequality
import LatticeProb.Prob.Harris
import LatticeProb.Prob.EfronSteinCov

/-!
# Concentration of the odometer at the fluctuation scale

Concentration of the odometer at the fluctuation scale.

`prop:finite-time-concentration-scale` (`sandpile.tex:1461-1486`) reads the
odometer as a coordinate-Lipschitz function of the scenery with the Green kernel
as its Lipschitz constants, and applies the square-function bound to it.  The
passage from the i.i.d. law of the field to the finite product the square
function bound is stated for is `Sandpile/Support/FiniteCoord.lean`; here that
passage is carried out.

The moment constant is `C = C(p, L(ζ(0)))` in the paper, with no dimension.  The
`_uniform` statements bind the constant before the dimension `k`, so that they
say this; the statements without the suffix fix the dimension `d` of the section
first and are read off from them.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The `p`-th moment of the fluctuation of a functional of the field that reads
`N` distinct sites, with the coordinate Lipschitz constants `ℓ`.  The constant
is bound before the dimension `k` of the lattice: it is the constant of the
`ℓ^p` square function bound, which does not see the lattice. -/
theorem exists_pick_moment_bound_uniform {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν →
      ∀ (N : ℕ) (e : Fin N → Site k), Function.Injective e →
      ∀ G : (Fin N → ℝ) → ℝ, Measurable G →
      ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) →
        (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
          |G ξ - G (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
        ∫ ζ, |G (fun i => ζ (e i)) -
            ∫ η, G (fun i => η (e i)) ∂(LatticeProb.iidLaw k ν)| ^ p
              ∂(LatticeProb.iidLaw k ν)
          ≤ C * pairMoment ν p * (∑ i, ℓ i ^ 2) ^ (p / 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨C₀, hC₀, hsq⟩ := exists_lp_square_pi hp
  refine ⟨C₀ ^ (p / 2), Real.rpow_pos_of_pos hC₀ _, ?_⟩
  intro k ν hν hmom N e he G hG ℓ hℓ hLip
  haveI := hν
  set P : Measure (Site k → ℝ) := LatticeProb.iidLaw k ν with hP
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hQ
  have hm : ∫ η, G (fun i => η (e i)) ∂P = ∫ η, G η ∂Q :=
    integral_pick ν e he G hG.aestronglyMeasurable
  have hGp : Measurable fun ξ : Fin N → ℝ => |G ξ - ∫ η, G η ∂Q| ^ p := by
    exact (hG.sub measurable_const).abs.pow_const p
  have htr : ∫ ζ, |G (fun i => ζ (e i)) - ∫ η, G (fun i => η (e i)) ∂P| ^ p ∂P
      = ∫ ξ, |G ξ - ∫ η, G η ∂Q| ^ p ∂Q := by
    rw [hm]
    exact integral_pick ν e he _ hGp.aestronglyMeasurable
  set A : ℝ := ∫ ξ, |G ξ - ∫ η, G η ∂Q| ^ p ∂Q with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hkey := hsq N (fun _ : Fin N => ν) (fun _ => hν) G hG ℓ hℓ hLip fun _ => hmom
  have hm0 : 0 ≤ pairMoment ν p := pairMoment_nonneg ν p
  have hS0 : 0 ≤ ∑ i, ℓ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : (∑ i, ℓ i ^ 2 * pairMoment ν p ^ (2 / p))
      = pairMoment ν p ^ (2 / p) * ∑ i, ℓ i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hkey' : A ^ (2 / p) ≤ C₀ * (pairMoment ν p ^ (2 / p) * ∑ i, ℓ i ^ 2) := by
    rw [← hsum]; exact hkey
  have hrhs0 : 0 ≤ C₀ * (pairMoment ν p ^ (2 / p) * ∑ i, ℓ i ^ 2) :=
    mul_nonneg hC₀.le (mul_nonneg (Real.rpow_nonneg hm0 _) hS0)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hkey' (by positivity : (0:ℝ) ≤ p / 2)
  have hleft : (A ^ (2 / p)) ^ (p / 2) = A := by
    rw [← Real.rpow_mul hA0]
    rw [show (2 / p) * (p / 2) = 1 by field_simp]
    exact Real.rpow_one A
  have hright : (C₀ * (pairMoment ν p ^ (2 / p) * ∑ i, ℓ i ^ 2)) ^ (p / 2)
      = C₀ ^ (p / 2) * pairMoment ν p * (∑ i, ℓ i ^ 2) ^ (p / 2) := by
    rw [Real.mul_rpow hC₀.le (mul_nonneg (Real.rpow_nonneg hm0 _) hS0),
      Real.mul_rpow (Real.rpow_nonneg hm0 _) hS0, ← Real.rpow_mul hm0,
      show (2 / p) * (p / 2) = 1 by field_simp, Real.rpow_one, mul_assoc]
  calc ∫ ζ, |G (fun i => ζ (e i)) - ∫ η, G (fun i => η (e i)) ∂P| ^ p ∂P
      = (A ^ (2 / p)) ^ (p / 2) := by rw [htr, hleft]
    _ ≤ (C₀ * (pairMoment ν p ^ (2 / p) * ∑ i, ℓ i ^ 2)) ^ (p / 2) := hpow
    _ = C₀ ^ (p / 2) * pairMoment ν p * (∑ i, ℓ i ^ 2) ^ (p / 2) := hright

/-- The `p`-th moment of the fluctuation of a functional of the field that reads
`N` distinct sites, with the coordinate Lipschitz constants `ℓ`, in a fixed
dimension. -/
theorem exists_pick_moment_bound {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν →
      ∀ (N : ℕ) (e : Fin N → Site d), Function.Injective e →
      ∀ G : (Fin N → ℝ) → ℝ, Measurable G →
      ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) →
        (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
          |G ξ - G (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
        ∫ ζ, |G (fun i => ζ (e i)) -
            ∫ η, G (fun i => η (e i)) ∂(LatticeProb.iidLaw d ν)| ^ p
              ∂(LatticeProb.iidLaw d ν)
          ≤ C * pairMoment ν p * (∑ i, ℓ i ^ 2) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_pick_moment_bound_uniform hp
  exact ⟨C, hC, hb d⟩

/-- Clause three of `prop:finite-time-concentration-scale`, still written in the
Green coefficients rather than in the membrane variance.  The constant is bound
before the dimension `k`. -/
theorem exists_odometer_moment_bound_uniform {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν → ∀ (t : ℕ) (x : Site k),
        ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t x ∂(LatticeProb.iidLaw k ν)| ^ p
            ∂(LatticeProb.iidLaw k ν)
          ≤ C * pairMoment ν p * (∑' z : Site k, greenTime k t x z ^ 2) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_pick_moment_bound_uniform hp
  refine ⟨C, hC, ?_⟩
  intro k ν hν hmom t x
  have h := hb k ν hν hmom (boxFinset x t).card (boxEnum x t) (boxEnum_injective x t)
    (boxOdometer t x) (measurable_boxOdometer t x)
    (fun i => greenTime k t x (boxEnum x t i)) (fun i => greenTime_nonneg t x _)
    (fun ξ i y => abs_boxOdometer_update_le t x ξ i y)
  simp only [boxOdometer_pick] at h
  have hsum : (∑ i : Fin (boxFinset x t).card, greenTime k t x (boxEnum x t i) ^ 2)
      = ∑' z : Site k, greenTime k t x z ^ 2 := by
    rw [sum_boxEnum x t fun z => greenTime k t x z ^ 2, tsum_greenTime_sq_eq_sum]
  rwa [hsum] at h

/-- Clause three of `prop:finite-time-concentration-scale`, still written in the
Green coefficients rather than in the membrane variance, in a fixed dimension. -/
theorem exists_odometer_moment_bound {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => |z| ^ p) ν → ∀ (t : ℕ) (x : Site d),
        ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t x ∂(LatticeProb.iidLaw d ν)| ^ p
            ∂(LatticeProb.iidLaw d ν)
          ≤ C * pairMoment ν p * (∑' z : Site d, greenTime d t x z ^ 2) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_odometer_moment_bound_uniform hp
  exact ⟨C, hC, hb d⟩

/-- If the one-site law has no variance, an independent pair of samples is
almost surely equal, so the resampling moment vanishes. -/
theorem pairMoment_eq_zero_of_variance_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp0 : 0 < p) (hMemLp : MemLp (id : ℝ → ℝ) 2 ν)
    (hvar : variance (id : ℝ → ℝ) ν = 0) : pairMoment ν p = 0 := by
  have hae := ae_eq_integral_of_variance_eq_zero hMemLp hvar
  have hinner : ∀ y : ℝ, ∫ z, |y - z| ^ p ∂ν = |y - ∫ w, w ∂ν| ^ p := by
    intro y
    have : ∫ z, |y - z| ^ p ∂ν = ∫ _z : ℝ, |y - ∫ w, w ∂ν| ^ p ∂ν := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      simp only [id_eq] at hz
      rw [hz]
    rw [this, integral_const]
    simp
  rw [pairMoment]
  have houter : ∫ y, ∫ z, |y - z| ^ p ∂ν ∂ν = ∫ _y : ℝ, (0 : ℝ) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [id_eq] at hy
    rw [hinner y, hy, sub_self, abs_zero, Real.zero_rpow (ne_of_gt hp0)]
  rw [houter, integral_zero]

/-- The square integrability of the one-site law that follows from a `p`-th
moment, `p ≥ 2`. -/
theorem memLp_two_of_moment (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 2 ≤ p)
    (hmom : Integrable (fun z => |z| ^ p) ν) : MemLp (id : ℝ → ℝ) 2 ν := by
  have hmom' : Integrable (fun z : ℝ => ‖(id z)‖ ^ p) ν := by
    simpa [Real.norm_eq_abs] using hmom
  have hint2 : Integrable (fun z : ℝ => ‖(id z)‖ ^ (2 : ℝ)) ν :=
    integrable_norm_rpow_of_le (f := (id : ℝ → ℝ)) aestronglyMeasurable_id
      (by norm_num) (by linarith) hp hmom'
  rw [← integrable_norm_rpow_iff (p := (2 : ℝ≥0∞)) aestronglyMeasurable_id (by simp) (by simp)]
  simpa using hint2

/-- Clause three of `prop:finite-time-concentration-scale`, in the membrane
variance the paper writes it with.  The constant depends on `p` and on the
one-site law, and is bound before the dimension `k`, as `C = C(p, L(ζ(0)))`
does not mention the dimension. -/
theorem exists_odometer_moment_variance_uniform (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 2 ≤ p) (hmom : Integrable (fun z => |z| ^ p) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (t : ℕ) (x : Site k),
      ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t x ∂(LatticeProb.iidLaw k ν)| ^ p
          ∂(LatticeProb.iidLaw k ν)
        ≤ C * variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw k ν) ^ (p / 2) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hMemLp := memLp_two_of_moment ν hp hmom
  obtain ⟨C₁, hC₁, hb⟩ := exists_odometer_moment_bound_uniform hp
  have hm0 := pairMoment_nonneg ν p
  by_cases hvar : variance (id : ℝ → ℝ) ν = 0
  · refine ⟨1, one_pos, fun k t x => ?_⟩
    have hb' := hb k ν ‹_› hmom t x
    rw [pairMoment_eq_zero_of_variance_zero ν hp0 hMemLp hvar, mul_zero, zero_mul] at hb'
    have hnn : (0 : ℝ) ≤
        variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw k ν) ^ (p / 2) :=
      Real.rpow_nonneg (variance_nonneg _ _) _
    linarith
  · have hvpos : 0 < variance (id : ℝ → ℝ) ν :=
      lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)
    have hnum : 0 < C₁ * pairMoment ν p + 1 := by nlinarith
    have hden : 0 < variance (id : ℝ → ℝ) ν ^ (p / 2) := Real.rpow_pos_of_pos hvpos _
    refine ⟨(C₁ * pairMoment ν p + 1) / variance (id : ℝ → ℝ) ν ^ (p / 2),
      div_pos hnum hden, fun k t x => ?_⟩
    have hb' := hb k ν ‹_› hmom t x
    rw [tsum_greenTime_sq_eq t x] at hb'
    have hS0 : (0 : ℝ) ≤ ∑' z : Site k, greenTime k t 0 z ^ 2 :=
      tsum_nonneg fun z => sq_nonneg _
    have hV : variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw k ν)
        = variance (id : ℝ → ℝ) ν * ∑' z : Site k, greenTime k t 0 z ^ 2 :=
      variance_membrane ν hMemLp t 0
    rw [hV, Real.mul_rpow hvpos.le hS0]
    have hEq : (C₁ * pairMoment ν p + 1) / variance (id : ℝ → ℝ) ν ^ (p / 2) *
        (variance (id : ℝ → ℝ) ν ^ (p / 2) * (∑' z : Site k, greenTime k t 0 z ^ 2) ^ (p / 2))
        = (C₁ * pairMoment ν p + 1) * (∑' z : Site k, greenTime k t 0 z ^ 2) ^ (p / 2) := by
      field_simp
    rw [hEq]
    have hSp : (0 : ℝ) ≤ (∑' z : Site k, greenTime k t 0 z ^ 2) ^ (p / 2) :=
      Real.rpow_nonneg hS0 _
    nlinarith [hb']

/-- Clause three of `prop:finite-time-concentration-scale`, in the membrane
variance the paper writes it with, in a fixed dimension. -/
theorem exists_odometer_moment_variance (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 2 ≤ p) (hmom : Integrable (fun z => |z| ^ p) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (x : Site d),
      ∫ ζ, |odometerOf ζ t x - ∫ η, odometerOf η t x ∂(LatticeProb.iidLaw d ν)| ^ p
          ∂(LatticeProb.iidLaw d ν)
        ≤ C * variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw d ν) ^ (p / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_odometer_moment_variance_uniform ν hp hmom
  exact ⟨C, hC, hb d⟩

/-- Clause two of `prop:finite-time-concentration-scale`: the odometer is
Lipschitz in the scenery for the `ℓ²` norm, with the `ℓ²` mass of the Green
coefficients as its constant. -/
theorem abs_odometerOf_sub_le_l2 (t : ℕ) (x : Site d) (ζ η : Site d → ℝ)
    (h : Summable fun z : Site d => (ζ z - η z) ^ 2) :
    |odometerOf ζ t x - odometerOf η t x|
      ≤ Real.sqrt (∑' z : Site d, greenTime d t x z ^ 2) *
        Real.sqrt (∑' z : Site d, (ζ z - η z) ^ 2) :=
  le_trans (abs_odometerOf_sub_le ζ η t x)
    (tsum_mul_le_sqrt_mul_sqrt (boxFinset x t) (greenTime d t x) (fun z => ζ z - η z)
      (fun z => greenTime_nonneg t x z)
      (fun z hz => by
        by_contra hne
        exact hz (mem_boxFinset (greenTime_support t x hne))) h)

/-! ### The odometer is nondecreasing in the scenery -/

/-- The odometer is nondecreasing in the scenery. -/
theorem odometerOf_mono : ∀ (t : ℕ) (x : Site d) {ζ η : Site d → ℝ}, (∀ z, ζ z ≤ η z) →
    odometerOf ζ t x ≤ odometerOf η t x := by
  intro t
  induction t with
  | zero => intro x ζ η _; simp [odometerOf]
  | succ n ih =>
      intro x ζ η h
      have havg : avg (odometerOf ζ n) x ≤ avg (odometerOf η n) x := by
        show (∑ i : Fin d, (odometerOf ζ n (x + unit i) + odometerOf ζ n (x - unit i)))
            / (2 * (d : ℝ))
          ≤ (∑ i : Fin d, (odometerOf η n (x + unit i) + odometerOf η n (x - unit i)))
            / (2 * (d : ℝ))
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0; simp
        · have hc : (0 : ℝ) < 2 * (d : ℝ) := by
            have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
            linarith
          gcongr with i _
          · exact ih (x + unit i) h
          · exact ih (x - unit i) h
      show max 0 (ζ x + avg (odometerOf ζ n) x) ≤ max 0 (η x + avg (odometerOf η n) x)
      exact max_le_max (le_refl 0) (add_le_add (h x) havg)

/-- `odometerOf_mono` repackaged as a `Monotone` statement: `ζ ↦ odometerOf ζ t x` is monotone
in the pointwise order on scenery configurations. -/
theorem monotone_odometerOf (t : ℕ) (x : Site d) :
    Monotone fun ζ : Site d → ℝ => odometerOf ζ t x :=
  fun _ _ h => odometerOf_mono t x fun z => h z

/-- The odometer at time `t` and site `x` depends only on the scenery values inside the box
`boxFinset x t`, proved by `odometerOf_congr_box`. -/
theorem dependsOn_odometerOf (t : ℕ) (x : Site d) :
    DependsOn (fun ζ : Site d → ℝ => odometerOf ζ t x) ↑(boxFinset x t) := by
  intro ζ η h
  exact odometerOf_congr_box t x ζ η fun z hz => h z (by simpa using mem_boxFinset hz)

/-- The second moment as an `rpow`, which is the form the `L^p` machinery uses. -/
theorem integrable_abs_rpow_two (ν : Measure ℝ) (hsq : Integrable (fun z => z ^ 2) ν) :
    Integrable (fun z => |z| ^ (2 : ℝ)) ν :=
  hsq.congr (Filter.Eventually.of_forall fun z => by
    show z ^ 2 = |z| ^ (2 : ℝ)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs])

/-- The odometer is square integrable as soon as the one-site law is. -/
theorem memLp_two_odometerOf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq' : Integrable (fun z => z ^ 2) ν) (t : ℕ) (x : Site d) :
    MemLp (fun ζ : Site d → ℝ => odometerOf ζ t x) 2 (LatticeProb.iidLaw d ν) := by
  have hsq := integrable_abs_rpow_two ν hsq'
  haveI : ∀ _i : Fin (boxFinset x t).card, IsProbabilityMeasure ((fun _ => ν) _i) :=
    fun _ => ‹IsProbabilityMeasure ν›
  have hint := integrable_rpow_of_lip_fam (fun _ : Fin (boxFinset x t).card => ν)
    (p := 2) (by norm_num) (fun _ => hsq) (boxOdometer t x) (measurable_boxOdometer t x)
    (fun i => greenTime d t x (boxEnum x t i)) (fun i => greenTime_nonneg t x _)
    (fun ξ i y => abs_boxOdometer_update_le t x ξ i y)
  have hmem : MemLp (boxOdometer t x) 2
      (Measure.pi fun _ : Fin (boxFinset x t).card => ν) := by
    rw [← integrable_norm_rpow_iff (p := (2 : ℝ≥0∞))
      (measurable_boxOdometer t x).aestronglyMeasurable (by simp) (by simp)]
    simpa [Real.norm_eq_abs] using hint
  have := hmem.comp_measurePreserving
    (LatticeProb.measurePreserving_pick _ ν (boxEnum x t) (boxEnum_injective x t))
  simpa [Function.comp_def, boxOdometer_pick] using this

/-! ### The Harris lower bound on the covariance -/

/-- The lower bound of clause four of `prop:finite-time-concentration-scale`:
the odometer is nondecreasing in the scenery, so two odometers are positively
correlated. -/
theorem covariance_odometerOf_nonneg (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (n m : ℕ) (x y : Site d) :
    0 ≤ covariance (fun ζ => odometerOf ζ n x) (fun ζ => odometerOf ζ m y)
      (LatticeProb.iidLaw d ν) := by
  classical
  set P : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hP
  set f : (Site d → ℝ) → ℝ := fun ζ => odometerOf ζ n x with hf
  set g : (Site d → ℝ) → ℝ := fun ζ => odometerOf ζ m y with hg
  have hfL : MemLp f 2 P := memLp_two_odometerOf ν hsq n x
  have hgL : MemLp g 2 P := memLp_two_odometerOf ν hsq m y
  have hf0 : ∀ ζ, 0 ≤ f ζ := fun ζ => odometerOf_nonneg ζ n x
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ => odometerOf_nonneg ζ m y
  have hfm : Measurable f := measurable_odometerOf n x
  have hgm : Measurable g := measurable_odometerOf m y
  have hfi : Integrable f P := hfL.integrable (by norm_num)
  have hgi : Integrable g P := hgL.integrable (by norm_num)
  have hfg : Integrable (fun ζ => f ζ * g ζ) P :=
    MemLp.integrable_mul hfL hgL
  set s : Finset (Site d) := boxFinset x n ∪ boxFinset y m with hs
  -- the truncations
  have hharris : ∀ M : ℕ, (∫ ζ, min (f ζ) (M : ℝ) ∂P) * (∫ ζ, min (g ζ) (M : ℝ) ∂P)
      ≤ ∫ ζ, min (f ζ) (M : ℝ) * min (g ζ) (M : ℝ) ∂P := by
    intro M
    have hPi : P = Measure.infinitePi fun _ : Site d => ν := rfl
    rw [hPi]
    refine LatticeProb.infinitePi_harris_dependsOn (μ := fun _ : Site d => ν) s
      (C := (M : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun a b hab => min_le_min (monotone_odometerOf n x hab) (le_refl _)
    · exact fun a b hab => min_le_min (monotone_odometerOf m y hab) (le_refl _)
    · exact hfm.min measurable_const
    · exact hgm.min measurable_const
    · intro a b hab
      exact congrArg (fun r : ℝ => min r (M : ℝ))
        (DependsOn.mono (s := ↑(boxFinset x n))
          (by exact_mod_cast Finset.coe_subset.mpr Finset.subset_union_left)
          (dependsOn_odometerOf n x) hab)
    · intro a b hab
      exact congrArg (fun r : ℝ => min r (M : ℝ))
        (DependsOn.mono (s := ↑(boxFinset y m))
          (by exact_mod_cast Finset.coe_subset.mpr Finset.subset_union_right)
          (dependsOn_odometerOf m y) hab)
    · intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 ω) (Nat.cast_nonneg M))]
      exact min_le_right _ _
    · intro ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 ω) (Nat.cast_nonneg M))]
      exact min_le_right _ _
  have hconv : ∀ (h : (Site d → ℝ) → ℝ), (∀ ζ, 0 ≤ h ζ) →
      ∀ ζ, Filter.Tendsto (fun M : ℕ => min (h ζ) (M : ℝ)) Filter.atTop (nhds (h ζ)) := by
    intro h h0 ζ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈h ζ⌉₊) fun M hM => ?_
    exact min_eq_left (le_trans (Nat.le_ceil (h ζ)) (by exact_mod_cast hM))
  have hlim1 : Filter.Tendsto (fun M : ℕ => ∫ ζ, min (f ζ) (M : ℝ) ∂P) Filter.atTop
      (nhds (∫ ζ, f ζ ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence f
      (fun M => (hfm.min measurable_const).aestronglyMeasurable) hfi ?_
      (Filter.Eventually.of_forall (hconv f hf0))
    intro M
    refine Filter.Eventually.of_forall fun ζ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 ζ) (Nat.cast_nonneg M))]
    exact min_le_left _ _
  have hlim2 : Filter.Tendsto (fun M : ℕ => ∫ ζ, min (g ζ) (M : ℝ) ∂P) Filter.atTop
      (nhds (∫ ζ, g ζ ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence g
      (fun M => (hgm.min measurable_const).aestronglyMeasurable) hgi ?_
      (Filter.Eventually.of_forall (hconv g hg0))
    intro M
    refine Filter.Eventually.of_forall fun ζ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 ζ) (Nat.cast_nonneg M))]
    exact min_le_left _ _
  have hlim3 : Filter.Tendsto
      (fun M : ℕ => ∫ ζ, min (f ζ) (M : ℝ) * min (g ζ) (M : ℝ) ∂P) Filter.atTop
      (nhds (∫ ζ, f ζ * g ζ ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun ζ => f ζ * g ζ)
      (fun M => ((hfm.min measurable_const).mul (hgm.min measurable_const)).aestronglyMeasurable)
      hfg ?_ ?_
    · intro M
      refine Filter.Eventually.of_forall fun ζ => ?_
      have h1 : 0 ≤ min (f ζ) (M : ℝ) := le_min (hf0 ζ) (Nat.cast_nonneg M)
      have h2 : 0 ≤ min (g ζ) (M : ℝ) := le_min (hg0 ζ) (Nat.cast_nonneg M)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
      exact mul_le_mul (min_le_left _ _) (min_le_left _ _) h2 (hf0 ζ)
    · refine Filter.Eventually.of_forall fun ζ => ?_
      exact (hconv f hf0 ζ).mul (hconv g hg0 ζ)
  have hprod : (∫ ζ, f ζ ∂P) * (∫ ζ, g ζ ∂P) ≤ ∫ ζ, f ζ * g ζ ∂P :=
    le_of_tendsto_of_tendsto' (hlim1.mul hlim2) hlim3 hharris
  rw [covariance_eq_sub hfL hgL]
  have hmul : P[f * g] = ∫ ζ, f ζ * g ζ ∂P := by simp [Pi.mul_apply]
  rw [hmul]
  linarith

/-! ### The covariance form of Efron-Stein applied to two odometers -/

/-- The identity function is integrable whenever its square is, proved by comparing
`Integrable` norms with `integrable_abs_of_sq`. -/
theorem integrable_id_of_sq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) : Integrable (fun z : ℝ => z) ν :=
  (integrable_norm_iff (f := fun z : ℝ => z) measurable_id.aestronglyMeasurable).mp
    (by simpa [Real.norm_eq_abs] using integrable_abs_of_sq ν hsq)

/-- `E|ζ(0) - ζ'(0)|² = 2 Var(ζ(0))`. -/
theorem integral_pair_sq_id (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) :
    ∫ y, ∫ z, (y - z) ^ 2 ∂ν ∂ν = 2 * variance (id : ℝ → ℝ) ν := by
  have h := integral_pair_sq ν (fun z : ℝ => z) (integrable_id_of_sq ν hsq) hsq
  rw [h, variance_eq_integral measurable_id.aemeasurable]
  rfl

/-- The resampling square is integrable on the product, under a coordinate
Lipschitz bound and a second moment. -/
theorem integrable_resample_prod (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) {M : ℕ}
    (F : (Fin M → ℝ) → ℝ) (hFm : Measurable F) (ℓ : Fin M → ℝ)
    (hLip : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) (i : Fin M) :
    Integrable (fun q : (Fin M → ℝ) × ℝ => (F q.1 - F (Function.update q.1 i q.2)) ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := by
  have hid := integrable_id_of_sq ν hsq
  have h1 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.1 i ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := (integrable_eval_sq ν hsq i).comp_fst ν
  have h2 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.2 ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := hsq.comp_snd _
  have h3 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.1 i * q.2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) :=
    Integrable.mul_prod (integrable_eval_id ν hsq i) hid
  have hpair : Integrable (fun q : (Fin M → ℝ) × ℝ => (q.1 i - q.2) ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := by
    have := (h1.sub (h3.const_mul 2)).add h2
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  refine Integrable.mono' (hpair.const_mul (ℓ i ^ 2))
    (((hFm.comp measurable_fst).sub
      (hFm.comp (measurable_update_pair i))).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hLip q.1 i q.2
  have hsqle : (F q.1 - F (Function.update q.1 i q.2)) ^ 2 ≤ (ℓ i * |q.1 i - q.2|) ^ 2 := by
    rw [← sq_abs (F q.1 - F (Function.update q.1 i q.2))]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  calc (F q.1 - F (Function.update q.1 i q.2)) ^ 2 ≤ (ℓ i * |q.1 i - q.2|) ^ 2 := hsqle
    _ = ℓ i ^ 2 * (q.1 i - q.2) ^ 2 := by rw [mul_pow, sq_abs]

/-- The resampling energy of a coordinate-Lipschitz function is at most the
square of its constant times `E|ζ(0) - ζ'(0)|²`. -/
theorem resampleEnergy_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) {M : ℕ}
    (F : (Fin M → ℝ) → ℝ) (hFm : Measurable F) (ℓ : Fin M → ℝ)
    (hLip : ∀ (ξ : Fin M → ℝ) (i : Fin M) (y : ℝ),
      |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) (i : Fin M) :
    LatticeProb.resampleEnergy (fun _ : Fin M => ν) F i
      ≤ ℓ i ^ 2 * (2 * variance (id : ℝ → ℝ) ν) := by
  have hid := integrable_id_of_sq ν hsq
  have hres := integrable_resample_prod ν hsq F hFm ℓ hLip i
  have h1 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.1 i ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := (integrable_eval_sq ν hsq i).comp_fst ν
  have h2 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.2 ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := hsq.comp_snd _
  have h3 : Integrable (fun q : (Fin M → ℝ) × ℝ => q.1 i * q.2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) :=
    Integrable.mul_prod (integrable_eval_id ν hsq i) hid
  have hpair : Integrable (fun q : (Fin M → ℝ) × ℝ => (q.1 i - q.2) ^ 2)
      ((Measure.pi fun _ : Fin M => ν).prod ν) := by
    have := (h1.sub (h3.const_mul 2)).add h2
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hmp : MeasurePreserving
      (fun q : (Fin M → ℝ) × ℝ => (q.1 i, q.2))
      ((Measure.pi fun _ : Fin M => ν).prod ν) (ν.prod ν) :=
    (measurePreserving_eval (fun _ : Fin M => ν) i).prod (MeasurePreserving.id ν)
  have hval : ∫ q : (Fin M → ℝ) × ℝ, (q.1 i - q.2) ^ 2
      ∂((Measure.pi fun _ : Fin M => ν).prod ν) = 2 * variance (id : ℝ → ℝ) ν := by
    have hcomp : ∫ q : (Fin M → ℝ) × ℝ, (q.1 i - q.2) ^ 2
        ∂((Measure.pi fun _ : Fin M => ν).prod ν)
        = ∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 ∂(ν.prod ν) := by
      have hmapped := integral_map (μ := (Measure.pi fun _ : Fin M => ν).prod ν)
        (φ := fun q : (Fin M → ℝ) × ℝ => (q.1 i, q.2))
        (f := fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) hmp.measurable.aemeasurable
        (by
          rw [hmp.map_eq]
          exact ((measurable_fst.sub measurable_snd).pow_const 2).aestronglyMeasurable)
      rw [hmp.map_eq] at hmapped
      exact hmapped.symm
    rw [hcomp, integral_prod _ (by
      have h1' : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (ν.prod ν) := hsq.comp_fst ν
      have h2' : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (ν.prod ν) := hsq.comp_snd ν
      have h3' : Integrable (fun p : ℝ × ℝ => p.1 * p.2) (ν.prod ν) :=
        Integrable.mul_prod hid hid
      have := (h1'.sub (h3'.const_mul 2)).add h2'
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Pi.add_apply, Pi.sub_apply]
      ring), integral_pair_sq_id ν hsq]
  rw [LatticeProb.resampleEnergy]
  refine le_trans (integral_mono hres (hpair.const_mul (ℓ i ^ 2)) fun q => ?_) ?_
  · have h := hLip q.1 i q.2
    have hsqle : (F q.1 - F (Function.update q.1 i q.2)) ^ 2 ≤ (ℓ i * |q.1 i - q.2|) ^ 2 := by
      rw [← sq_abs (F q.1 - F (Function.update q.1 i q.2))]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (F q.1 - F (Function.update q.1 i q.2)) ^ 2 ≤ (ℓ i * |q.1 i - q.2|) ^ 2 := hsqle
      _ = ℓ i ^ 2 * (q.1 i - q.2) ^ 2 := by rw [mul_pow, sq_abs]
  · rw [integral_const_mul, hval]

/-- The covariance of two coordinate-Lipschitz functionals of finitely many
distinct sites of an i.i.d. field, bounded by the PAIRING of their coefficient
vectors.  This is `9b` of the library request file, in the form the paper uses. -/
theorem covariance_pick_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) {N : ℕ} (e : Fin N → Site d)
    (he : Function.Injective e) (F G : (Fin N → ℝ) → ℝ) (hFm : Measurable F)
    (hGm : Measurable G) (a b : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hFLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (z : ℝ),
      |F ξ - F (Function.update ξ i z)| ≤ a i * |ξ i - z|)
    (hGLip : ∀ (ξ : Fin N → ℝ) (i : Fin N) (z : ℝ),
      |G ξ - G (Function.update ξ i z)| ≤ b i * |ξ i - z|) :
    covariance (fun ζ : Site d → ℝ => F (fun i => ζ (e i)))
        (fun ζ : Site d → ℝ => G (fun i => ζ (e i))) (LatticeProb.iidLaw d ν)
      ≤ variance (id : ℝ → ℝ) ν * ∑ i, a i * b i := by
  have hV : 0 ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  have hmF : ∫ ζ, F (fun i => ζ (e i)) ∂(LatticeProb.iidLaw d ν)
      = ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin N => ν) :=
    integral_pick ν e he F hFm.aestronglyMeasurable
  have hmG : ∫ ζ, G (fun i => ζ (e i)) ∂(LatticeProb.iidLaw d ν)
      = ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin N => ν) :=
    integral_pick ν e he G hGm.aestronglyMeasurable
  have hprodm : Measurable fun ξ : Fin N → ℝ =>
      (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) *
        (G ξ - ∫ η, G η ∂(Measure.pi fun _ : Fin N => ν)) :=
    (hFm.sub measurable_const).mul (hGm.sub measurable_const)
  have hcov : covariance (fun ζ : Site d → ℝ => F (fun i => ζ (e i)))
      (fun ζ : Site d → ℝ => G (fun i => ζ (e i))) (LatticeProb.iidLaw d ν)
      = ∫ ξ, (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) *
          (G ξ - ∫ η, G η ∂(Measure.pi fun _ : Fin N => ν))
        ∂(Measure.pi fun _ : Fin N => ν) := by
    rw [covariance]
    simp only [hmF, hmG]
    exact integral_pick ν e he _ hprodm.aestronglyMeasurable
  have hFsq : Integrable (fun ξ => F ξ ^ 2) (Measure.pi fun _ : Fin N => ν) :=
    (integrable_sq_of_lip ν hsq F hFm a ha hFLip 0).congr
      (Filter.Eventually.of_forall fun ξ => by simp)
  have hGsq : Integrable (fun ξ => G ξ ^ 2) (Measure.pi fun _ : Fin N => ν) :=
    (integrable_sq_of_lip ν hsq G hGm b hb hGLip 0).congr
      (Filter.Eventually.of_forall fun ξ => by simp)
  have hkey := LatticeProb.efron_stein_cov N (fun _ : Fin N => ν) (fun _ => ‹_›) F G hFm hGm
    hFsq hGsq (fun i => integrable_resample_prod ν hsq F hFm a hFLip i)
    (fun i => integrable_resample_prod ν hsq G hGm b hGLip i)
  have hsqrt : ∀ i : Fin N,
      Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) F i)
        * Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i)
        ≤ a i * b i * (2 * variance (id : ℝ → ℝ) ν) := by
    intro i
    have hFe := resampleEnergy_le ν hsq F hFm a hFLip i
    have hGe := resampleEnergy_le ν hsq G hGm b hGLip i
    have h2V : (0 : ℝ) ≤ 2 * variance (id : ℝ → ℝ) ν := by linarith
    have hF' : Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) F i)
        ≤ a i * Real.sqrt (2 * variance (id : ℝ → ℝ) ν) := by
      refine le_trans (Real.sqrt_le_sqrt hFe) (le_of_eq ?_)
      rw [Real.sqrt_mul (sq_nonneg (a i)), Real.sqrt_sq (ha i)]
    have hG' : Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i)
        ≤ b i * Real.sqrt (2 * variance (id : ℝ → ℝ) ν) := by
      refine le_trans (Real.sqrt_le_sqrt hGe) (le_of_eq ?_)
      rw [Real.sqrt_mul (sq_nonneg (b i)), Real.sqrt_sq (hb i)]
    have hmul := mul_le_mul hF' hG' (Real.sqrt_nonneg _)
      (mul_nonneg (ha i) (Real.sqrt_nonneg _))
    refine le_trans hmul (le_of_eq ?_)
    have : Real.sqrt (2 * variance (id : ℝ → ℝ) ν) * Real.sqrt (2 * variance (id : ℝ → ℝ) ν)
        = 2 * variance (id : ℝ → ℝ) ν := Real.mul_self_sqrt h2V
    calc a i * Real.sqrt (2 * variance (id : ℝ → ℝ) ν) *
          (b i * Real.sqrt (2 * variance (id : ℝ → ℝ) ν))
        = a i * b i * (Real.sqrt (2 * variance (id : ℝ → ℝ) ν) *
            Real.sqrt (2 * variance (id : ℝ → ℝ) ν)) := by ring
      _ = a i * b i * (2 * variance (id : ℝ → ℝ) ν) := by rw [this]
  have hsum : (1 / 2 : ℝ) * ∑ i, Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) F i)
        * Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i)
      ≤ variance (id : ℝ → ℝ) ν * ∑ i, a i * b i := by
    have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hsqrt i
    have hrw : ∑ i, a i * b i * (2 * variance (id : ℝ → ℝ) ν)
        = 2 * variance (id : ℝ → ℝ) ν * ∑ i, a i * b i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw] at h
    linarith
  calc covariance (fun ζ : Site d → ℝ => F (fun i => ζ (e i)))
        (fun ζ : Site d → ℝ => G (fun i => ζ (e i))) (LatticeProb.iidLaw d ν)
      = ∫ ξ, (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) *
          (G ξ - ∫ η, G η ∂(Measure.pi fun _ : Fin N => ν))
        ∂(Measure.pi fun _ : Fin N => ν) := hcov
    _ ≤ |∫ ξ, (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) *
          (G ξ - ∫ η, G η ∂(Measure.pi fun _ : Fin N => ν))
        ∂(Measure.pi fun _ : Fin N => ν)| := le_abs_self _
    _ ≤ (1 / 2 : ℝ) * ∑ i, Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) F i)
          * Real.sqrt (LatticeProb.resampleEnergy (fun _ : Fin N => ν) G i) := hkey
    _ ≤ variance (id : ℝ → ℝ) ν * ∑ i, a i * b i := hsum

/-- The upper bound of clause four of `prop:finite-time-concentration-scale`:
two odometers of the same i.i.d. field have covariance at most
`2 Var(ζ(0)) ∑_z g_n(x,z) g_m(y,z)`. -/
theorem covariance_odometerOf_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) (n m : ℕ) (x y : Site d) :
    covariance (fun ζ => odometerOf ζ n x) (fun ζ => odometerOf ζ m y)
        (LatticeProb.iidLaw d ν)
      ≤ 2 * variance (id : ℝ → ℝ) ν *
        ∑' z : Site d, greenTime d n x z * greenTime d m y z := by
  classical
  have hsubx : boxFinset x n ⊆ boxFinset x n ∪ boxFinset y m := Finset.subset_union_left
  have hsuby : boxFinset y m ⊆ boxFinset x n ∪ boxFinset y m := Finset.subset_union_right
  have hkey := covariance_pick_le ν hsq
    (siteEnum (boxFinset x n ∪ boxFinset y m))
    (siteEnum_injective (boxFinset x n ∪ boxFinset y m))
    (sceneryOdometer (boxFinset x n ∪ boxFinset y m) n x)
    (sceneryOdometer (boxFinset x n ∪ boxFinset y m) m y)
    (measurable_sceneryOdometer _ n x) (measurable_sceneryOdometer _ m y)
    (fun i => greenTime d n x (siteEnum (boxFinset x n ∪ boxFinset y m) i))
    (fun i => greenTime d m y (siteEnum (boxFinset x n ∪ boxFinset y m) i))
    (fun i => greenTime_nonneg n x _) (fun i => greenTime_nonneg m y _)
    (fun ξ i z => abs_sceneryOdometer_update_le _ n x ξ i z)
    (fun ξ i z => abs_sceneryOdometer_update_le _ m y ξ i z)
  rw [sum_siteEnum_greenTime_mul hsubx] at hkey
  simp only [sceneryOdometer_pick hsubx, sceneryOdometer_pick hsuby] at hkey
  have hS : (0 : ℝ) ≤ ∑' z : Site d, greenTime d n x z * greenTime d m y z :=
    tsum_nonneg fun z => mul_nonneg (greenTime_nonneg _ _ _) (greenTime_nonneg _ _ _)
  have hV : (0 : ℝ) ≤ variance (id : ℝ → ℝ) ν := variance_nonneg _ _
  nlinarith [hkey]

end Sandpile
