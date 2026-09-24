/-
A white noise whose ball fields are almost surely continuous.

`Sandpile.Frozen.limiting_odometer_crossing` assumes this continuity as a bare
hypothesis, and nothing in the repository builds a noise that satisfies it: the
condition occurs only ever as a hypothesis.  The node is therefore sound as an
implication while its antecedent has no known instance, which for this program is
the same standing as an unchecked cited input.

The route is Kolmogorov-Chentsov, one scale at a time.  The `L²` modulus of the
ball kernel is already proved, so at each scale the field has a continuous
modification on the plane; transferring the modification back to the noise needs
the kernel to determine the scale and centre, and the congruence lemma for the
white-noise property.
-/
import Sandpile.Support.LimVacuity
import Sandpile.Support.LimKernelShift
import Sandpile.Continuum.WhiteNoiseExists
import Sandpile.Support.LimNoiseModification

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-! ### The ball kernel determines the scale and the centre -/

/-- The ball kernel is positive exactly on the punctured open ball: at the centre itself
the two dimensions take the junk values `0` and `-1/(4πs)`, neither positive. -/
theorem ballKernel_pos_iff {d : ℕ} {s : ℝ} (hs : 0 < s)
    (u : Space 2) (z : Space d) :
    0 < ballKernel d s u z ↔
      0 < ‖(planePoint (d := d) u) - z‖ ∧ ‖(planePoint (d := d) u) - z‖ < s := by
  have hr0 : 0 ≤ ‖(planePoint (d := d) u) - z‖ := norm_nonneg _
  unfold ballKernel
  generalize ‖(planePoint (d := d) u) - z‖ = r at hr0 ⊢
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  by_cases hrs : r < s
  · rw [if_pos hrs]
    by_cases hr : r = 0
    · subst hr
      by_cases hd2 : d = 2
      · rw [if_pos hd2, div_zero, Real.log_zero, mul_zero]
        exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h.1 (lt_irrefl _)⟩
      · rw [if_neg hd2, div_zero, zero_sub]
        have h2 : (1 / (4 * Real.pi)) * (-(1 / s)) < 0 :=
          mul_neg_of_pos_of_neg (by positivity) (neg_neg_of_pos (by positivity))
        exact ⟨fun h => absurd h (not_lt.mpr h2.le), fun h => absurd h.1 (lt_irrefl _)⟩
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
      refine ⟨fun _ => ⟨hrpos, hrs⟩, fun _ => ?_⟩
      by_cases hd2 : d = 2
      · rw [if_pos hd2]
        exact mul_pos (by positivity) (Real.log_pos ((one_lt_div hrpos).mpr hrs))
      · rw [if_neg hd2]
        exact mul_pos (by positivity) (sub_pos.mpr (one_div_lt_one_div_of_lt hrpos hrs))
  · rw [if_neg hrs]
    exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h.2 hrs⟩

/-- If the punctured ball of radius `s` about `c` lies inside the punctured ball of radius
`s'` about `c'`, then the first ball lies inside the second: `‖c - c'‖ + s ≤ s'`.  The
proof pushes a point of the first ball along the ray from `c'` through `c`. -/
theorem norm_sub_add_le_of_punctured_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c c' : E} {s s' : ℝ} (hs : 0 < s) (e0 : E) (he0 : ‖e0‖ = 1)
    (h : ∀ z : E, (0 < ‖c - z‖ ∧ ‖c - z‖ < s) → (0 < ‖c' - z‖ ∧ ‖c' - z‖ < s')) :
    ‖c - c'‖ + s ≤ s' := by
  obtain ⟨e, he, hce⟩ : ∃ e : E, ‖e‖ = 1 ∧ c - c' = ‖c - c'‖ • e := by
    by_cases ha : c - c' = 0
    · exact ⟨e0, he0, by rw [ha, norm_zero, zero_smul]⟩
    · refine ⟨‖c - c'‖⁻¹ • (c - c'), ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_smul]
  have hρ0 : 0 ≤ ‖c - c'‖ := norm_nonneg _
  by_contra hcon
  replace hcon := not_le.mp hcon
  set ρ : ℝ := ‖c - c'‖ with hρ
  set m : ℝ := max (s' - ρ) 0 with hm
  have hm_lt : m < s := max_lt (by linarith) hs
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : s' - ρ ≤ m := le_max_left _ _
  set t : ℝ := (m + s) / 2 with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have hts : t < s := by rw [ht]; linarith
  have hmt : m < t := by rw [ht]; linarith
  have h1 : ‖c - (c + t • e)‖ = t := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, he, mul_one, Real.norm_of_nonneg ht0.le]
  have h2 : ‖c' - (c + t • e)‖ = ρ + t := by
    have h3 : c' - (c + t • e) = -((ρ + t) • e) := by
      rw [add_smul, ← hce]
      abel
    rw [h3, norm_neg, norm_smul, he, mul_one, Real.norm_of_nonneg (add_nonneg hρ0 ht0.le)]
  have h4 := (h (c + t • e) ⟨by rw [h1]; exact ht0, by rw [h1]; exact hts⟩).2
  rw [h2] at h4
  linarith

/-- **The ball kernel determines its scale and its centre**, on the positive scales. -/
theorem ballKernel_injective {d : ℕ} (hd : d = 2 ∨ d = 3) {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') {u u' : Space 2} (h : ballKernel d s u = ballKernel d s' u') :
    s = s' ∧ u = u' := by
  have hd1 : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  set e0 : Space d := EuclideanSpace.single (⟨0, hd1⟩ : Fin d) (1 : ℝ) with he0def
  have he0 : ‖e0‖ = 1 := by simp [he0def]
  have hiff : ∀ z : Space d,
      (0 < ‖planePoint (d := d) u - z‖ ∧ ‖planePoint (d := d) u - z‖ < s) ↔
        (0 < ‖planePoint (d := d) u' - z‖ ∧ ‖planePoint (d := d) u' - z‖ < s') := by
    intro z
    rw [← ballKernel_pos_iff hs u z, ← ballKernel_pos_iff hs' u' z, h]
  have h1 := norm_sub_add_le_of_punctured_subset hs e0 he0 (fun z => (hiff z).1)
  have h2 := norm_sub_add_le_of_punctured_subset hs' e0 he0 (fun z => (hiff z).2)
  rw [norm_sub_rev] at h2
  have hρ0 : 0 ≤ ‖planePoint (d := d) u - planePoint (d := d) u'‖ := norm_nonneg _
  have hρ : ‖planePoint (d := d) u - planePoint (d := d) u'‖ = 0 := by linarith
  have hu : u = u' := by
    have h3 : ‖u - u'‖ = 0 := by rw [← norm_planePoint_sub hd2 u u']; exact hρ
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  exact ⟨by linarith, hu⟩

/-! ### The Kolmogorov condition of the ball field in the centre -/

/-- **The `L²` modulus of the ball kernel, globally**: the squared `L²` distance of two ball
kernels of the same scale is bounded by a constant times the `1/3` power of the distance
of the centres, with no restriction on the distance. -/
theorem exists_integral_sq_ballKernel_sub_le {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Space 2,
      (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2)
        ≤ C * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 3) := by
  set A : ℝ := ∫ y : Space d, centredKernel d s y ^ 2 with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => sq_nonneg _
  set R : ℝ := min s 1 with hR
  have hR0 : 0 < R := lt_min hs one_pos
  have hRpow : 0 < R ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hR0 _
  set C : ℝ := max (kernelShiftL2Const d s) (4 * A / R ^ ((1 : ℝ) / 3)) with hC
  have hC0 : 0 ≤ C := le_trans (by positivity) (le_max_right _ _)
  refine ⟨C, hC0, fun u v => ?_⟩
  by_cases hsmall : ‖planePoint (d := d) u - planePoint (d := d) v‖ ≤ R
  · exact (integral_sq_ballKernel_sub_le hd hs u v (hsmall.trans (min_le_left _ _))
      (hsmall.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))
  · replace hsmall := not_le.mp hsmall
    have hmu := memLp_ballKernel hd hs u
    have hmv := memLp_ballKernel hd hs v
    have hint_a : Integrable (fun y : Space d => ballKernel d s u y ^ 2) volume :=
      hmu.integrable_sq
    have hint_b : Integrable (fun y : Space d => ballKernel d s v y ^ 2) volume :=
      hmv.integrable_sq
    have hint_ab : Integrable
        (fun y : Space d => (ballKernel d s u y - ballKernel d s v y) ^ 2) volume :=
      (hmu.sub hmv).integrable_sq
    have hA_eq : ∀ x : Space 2, ∫ y : Space d, ballKernel d s x y ^ 2 = A := by
      intro x
      have hfun : (fun y : Space d => ballKernel d s x y ^ 2)
          = fun y : Space d => (fun z : Space d => centredKernel d s z ^ 2)
              (planePoint (d := d) x - y) := rfl
      rw [hfun]
      exact integral_sub_left_eq_self (fun z : Space d => centredKernel d s z ^ 2)
        (volume : Measure (Space d)) (planePoint (d := d) x)
    have hle : (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2) ≤ 4 * A := by
      calc (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2)
          ≤ ∫ y : Space d, (2 * ballKernel d s u y ^ 2 + 2 * ballKernel d s v y ^ 2) :=
            integral_mono hint_ab ((hint_a.const_mul 2).add (hint_b.const_mul 2))
              (fun y => by nlinarith [sq_nonneg (ballKernel d s u y + ballKernel d s v y)])
        _ = 2 * A + 2 * A := by
            rw [integral_add (hint_a.const_mul 2) (hint_b.const_mul 2), integral_const_mul,
              integral_const_mul, hA_eq, hA_eq]
        _ = 4 * A := by ring
    have hpow : R ^ ((1 : ℝ) / 3)
        ≤ ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hR0.le hsmall.le (by norm_num)
    calc (∫ y : Space d, (ballKernel d s u y - ballKernel d s v y) ^ 2) ≤ 4 * A := hle
      _ = (4 * A / R ^ ((1 : ℝ) / 3)) * R ^ ((1 : ℝ) / 3) := by
          rw [div_mul_cancel₀ _ hRpow.ne']
      _ ≤ C * ‖planePoint (d := d) u - planePoint (d := d) v‖ ^ ((1 : ℝ) / 3) :=
          mul_le_mul (le_max_right _ _) hpow hRpow.le hC0

/-- **The Kolmogorov condition of the ball field in the centre.**  The increment of the
field is a centred Gaussian whose variance is the squared `L²` distance of the kernels, so
the moment of order `24` is bounded by the fourth power of the distance of the centres, an
exponent above the dimension `2` of the index space. -/
theorem exists_isKolmogorovProcess_ballField {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ}
    (hs : 0 < s) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Space d → ℝ) → Ω → ℝ) (hW : IsWhiteNoise d W P) :
    ∃ M : ℝ≥0, IsKolmogorovProcess
      (fun (z : Fin 2 → ℝ) (ω : Ω) => ballField d W s (WithLp.toLp 2 z) ω) P 24 4 M := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_ballKernel_sub_le hd hs
  set B : ℝ := C * Real.sqrt 2 ^ ((1 : ℝ) / 3) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set Kc : ℝ := gaussAbsMoment 24 * B ^ ((24 : ℝ) / 2) with hKc
  have hKc0 : 0 ≤ Kc := mul_nonneg (gaussAbsMoment_nonneg 24) (Real.rpow_nonneg hB0 _)
  refine ⟨Real.toNNReal Kc, ?_⟩
  have hmeas : ∀ z : Fin 2 → ℝ, Measurable (fun ω => ballField d W s (WithLp.toLp 2 z) ω) :=
    fun z => hW.meas _ (memLp_ballKernel hd hs _)
  refine IsKolmogorovProcess.mk_of_secondCountableTopology hmeas (fun u v => ?_)
    (by norm_num) (by norm_num)
  show ∫⁻ ω, edist (ballField d W s (WithLp.toLp 2 u) ω)
      (ballField d W s (WithLp.toLp 2 v) ω) ^ (24 : ℝ) ∂P
    ≤ ((Real.toNNReal Kc : ℝ≥0) : ℝ≥0∞) * edist u v ^ (4 : ℝ)
  have hmu := memLp_ballKernel hd hs (WithLp.toLp 2 u)
  have hmv := memLp_ballKernel hd hs (WithLp.toLp 2 v)
  have hV0 : 0 ≤ ∫ y : Space d, (ballKernel d s (WithLp.toLp 2 u) y
      - ballKernel d s (WithLp.toLp 2 v) y) ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hV : (∫ y : Space d, (ballKernel d s (WithLp.toLp 2 u) y
      - ballKernel d s (WithLp.toLp 2 v) y) ^ 2) ≤ B * dist u v ^ ((1 : ℝ) / 3) := by
    refine (hC _ _).trans ?_
    have hr := norm_planePoint_sub_le hd u v
    have h1 : ‖planePoint (d := d) (WithLp.toLp 2 u) - planePoint (d := d) (WithLp.toLp 2 v)‖
        ^ ((1 : ℝ) / 3) ≤ (Real.sqrt 2 * dist u v) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (norm_nonneg _) hr (by norm_num)
    rw [Real.mul_rpow (Real.sqrt_nonneg 2) dist_nonneg] at h1
    calc C * ‖planePoint (d := d) (WithLp.toLp 2 u) - planePoint (d := d) (WithLp.toLp 2 v)‖
          ^ ((1 : ℝ) / 3)
        ≤ C * (Real.sqrt 2 ^ ((1 : ℝ) / 3) * dist u v ^ ((1 : ℝ) / 3)) :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ = B * dist u v ^ ((1 : ℝ) / 3) := by rw [hB]; ring
  have hbound : ∫ ω, |ballField d W s (WithLp.toLp 2 u) ω
      - ballField d W s (WithLp.toLp 2 v) ω| ^ (24 : ℝ) ∂P ≤ Kc * dist u v ^ (4 : ℝ) := by
    have hI := integral_abs_rpow_whiteNoise_sub P W hW _ _ hmu hmv (p := 24) (by norm_num)
    refine hI.trans_le ?_
    have h2 : (∫ y : Space d, (ballKernel d s (WithLp.toLp 2 u) y
        - ballKernel d s (WithLp.toLp 2 v) y) ^ 2) ^ ((24 : ℝ) / 2)
        ≤ (B * dist u v ^ ((1 : ℝ) / 3)) ^ ((24 : ℝ) / 2) :=
      Real.rpow_le_rpow hV0 hV (by norm_num)
    have h3 : (B * dist u v ^ ((1 : ℝ) / 3)) ^ ((24 : ℝ) / 2)
        = B ^ ((24 : ℝ) / 2) * dist u v ^ (4 : ℝ) := by
      rw [Real.mul_rpow hB0 (Real.rpow_nonneg dist_nonneg _),
        ← Real.rpow_mul dist_nonneg]
      norm_num
    rw [h3] at h2
    have hm0 := gaussAbsMoment_nonneg 24
    calc _ ≤ (B ^ ((24 : ℝ) / 2) * dist u v ^ (4 : ℝ)) * gaussAbsMoment 24 :=
          mul_le_mul_of_nonneg_right h2 hm0
      _ = Kc * dist u v ^ (4 : ℝ) := by rw [hKc]; ring
  have hint : Integrable (fun ω => |ballField d W s (WithLp.toLp 2 u) ω
      - ballField d W s (WithLp.toLp 2 v) ω| ^ (24 : ℝ)) P :=
    integrable_abs_rpow_whiteNoise_sub P W hW _ _ hmu hmv (by norm_num)
  have hlin : ∫⁻ ω, edist (ballField d W s (WithLp.toLp 2 u) ω)
      (ballField d W s (WithLp.toLp 2 v) ω) ^ (24 : ℝ) ∂P
      = ENNReal.ofReal (∫ ω, |ballField d W s (WithLp.toLp 2 u) ω
        - ballField d W s (WithLp.toLp 2 v) ω| ^ (24 : ℝ) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
    refine lintegral_congr fun ω => ?_
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  rw [hlin]
  calc ENNReal.ofReal (∫ ω, |ballField d W s (WithLp.toLp 2 u) ω
        - ballField d W s (WithLp.toLp 2 v) ω| ^ (24 : ℝ) ∂P)
      ≤ ENNReal.ofReal (Kc * dist u v ^ (4 : ℝ)) := ENNReal.ofReal_le_ofReal hbound
    _ = (Real.toNNReal Kc : ℝ≥0∞) * edist u v ^ (4 : ℝ) := by
        rw [ENNReal.ofReal_mul hKc0,
          ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg (x := u) (y := v)) (by norm_num),
          ← edist_dist]
        rfl

/-- **A continuous modification of the ball field at one scale.**  Kolmogorov-Chentsov on the
plane: at each positive scale the ball field has a modification, measurable at every centre,
whose every path is continuous. -/
theorem exists_continuous_modification_ballField {d : ℕ} (hd : d = 2 ∨ d = 3) {s : ℝ}
    (hs : 0 < s) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Space d → ℝ) → Ω → ℝ) (hW : IsWhiteNoise d W P) :
    ∃ Y : Space 2 → Ω → ℝ, (∀ u, Measurable (Y u)) ∧
      (∀ u, ballField d W s u =ᵐ[P] Y u) ∧ ∀ ω, Continuous fun u => Y u ω := by
  obtain ⟨M, hM⟩ := exists_isKolmogorovProcess_ballField hd hs P W hW
  obtain ⟨Y, hYm, hYmod, hYc⟩ := LatticeProb.exists_continuous_modification_pi_all hM
    (by norm_num : ((2 : ℕ) : ℝ) < 4)
  refine ⟨fun u ω => Y (WithLp.ofLp u) ω, fun u => hYm _, fun u => ?_, fun ω => ?_⟩
  · exact hYmod (WithLp.ofLp u)
  · exact (hYc ω).comp (PiLp.continuous_ofLp 2 fun _ => ℝ)

/-- **A white noise with almost surely continuous ball fields exists.**  This is
what makes `Sandpile.Frozen.limiting_odometer_crossing` applicable; without it the
crossing theorem is sound but has no instance. -/
theorem exists_whiteNoise_continuous_ballField (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ (ΩW : Type) (_ : MeasurableSpace ΩW) (PW : Measure ΩW) (_ : IsProbabilityMeasure PW)
      (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W PW ∧
      ∀ s : ℝ, 0 < s → ∀ᵐ ω ∂PW,
        Continuous fun u : Sandpile.Continuum.Space 2 =>
          Sandpile.Frozen.FixedScaleCrossings.ballField d W s u ω := by
  classical
  obtain ⟨ΩW, mΩ, PW, hPW, W, hW⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  -- step 3: one continuous modification per positive scale
  have hex : ∀ s : ℝ, ∃ Y : Space 2 → ΩW → ℝ, 0 < s →
      ((∀ u, Measurable (Y u)) ∧ (∀ u, ballField d W s u =ᵐ[PW] Y u) ∧
        ∀ ω, Continuous fun u => Y u ω) := by
    intro s
    by_cases hs : 0 < s
    · obtain ⟨Y, hY⟩ := exists_continuous_modification_ballField hd hs PW W hW
      exact ⟨Y, fun _ => hY⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hs⟩
  choose Y hY using hex
  -- step 4: change the noise at the ball kernels only
  obtain ⟨W', hW'def⟩ : ∃ W' : (Space d → ℝ) → ΩW → ℝ, ∀ f ω, W' f ω =
      if h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f
      then Y h.choose.1 h.choose.2 ω else W f ω :=
    ⟨fun f ω => if h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f
      then Y h.choose.1 h.choose.2 ω else W f ω, fun _ _ => rfl⟩
  have hpos : ∀ f, (h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f) →
      W' f = Y h.choose.1 h.choose.2 := fun f h => by
    funext ω
    rw [hW'def, dif_pos h]
  have hneg : ∀ f, ¬ (∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f) →
      W' f = W f := fun f h => by
    funext ω
    rw [hW'def, dif_neg h]
  have hkey : ∀ (f : Space d → ℝ) (p : ℝ × Space 2), 0 < p.1 →
      ballKernel d p.1 p.2 = f → W f =ᵐ[PW] Y p.1 p.2 := by
    rintro f ⟨s0, u0⟩ hs0 hk
    subst hk
    exact (hY s0 hs0).2.1 u0
  have heq : ∀ f, W f =ᵐ[PW] W' f := by
    intro f
    by_cases h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f
    · rw [hpos f h]
      exact hkey f h.choose h.choose_spec.1 h.choose_spec.2
    · rw [hneg f h]
  have hm : ∀ f, MemLp f 2 (volume : Measure (Space d)) → Measurable (W' f) := by
    intro f hf
    by_cases h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = f
    · rw [hpos f h]
      exact (hY _ h.choose_spec.1).1 _
    · rw [hneg f h]
      exact hW.meas f hf
  have hW'white : IsWhiteNoise d W' PW := Sandpile.Support.isWhiteNoise_congr hW heq hm
  -- at a ball kernel the new noise is the chosen modification, by injectivity of the kernel
  have hball : ∀ s : ℝ, 0 < s → ∀ u : Space 2, ballField d W' s u = Y s u := by
    intro s hs u
    have h : ∃ p : ℝ × Space 2, 0 < p.1 ∧ ballKernel d p.1 p.2 = ballKernel d s u :=
      ⟨(s, u), hs, rfl⟩
    have hspec := h.choose_spec
    obtain ⟨h1, h2⟩ := ballKernel_injective hd hspec.1 hs hspec.2
    have hp : h.choose = (s, u) := Prod.ext h1 h2
    show W' (ballKernel d s u) = Y s u
    rw [hpos _ h, hp]
  refine ⟨ΩW, mΩ, PW, hPW, W', hW'white, fun s hs => Filter.Eventually.of_forall fun ω => ?_⟩
  have hfun : (fun u : Space 2 => ballField d W' s u ω) = fun u => Y s u ω := by
    funext u
    exact congrFun (hball s hs u) ω
  rw [hfun]
  exact (hY s hs).2.2 ω

end Sandpile.Support
