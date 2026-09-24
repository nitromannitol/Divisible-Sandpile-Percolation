/-
A Brownian path which remains in a ball has one Gaussian coordinate in a
bounded interval. The Gaussian density bound yields a survival estimate tending
to zero, uniformly over the Brownian model, and almost-sure finiteness of exit.
-/
import Mathlib
import LatticeProb.Prob.BrownianExitTime
import LatticeProb.Prob.BrownianExit
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

theorem Sandpile.Support.gaussianReal_Icc_le_length {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    gaussianReal 0 v (Set.Icc a b) ≤
      ENNReal.ofReal (max (b - a) 0 / Real.sqrt (2 * Real.pi * (v : ℝ)))  := by
  rw [gaussianReal_apply_eq_integral 0 hv]
  apply ENNReal.ofReal_le_ofReal
  have hb : ∀ x : ℝ, gaussianPDFReal 0 v x ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
    intro x
    unfold gaussianPDFReal
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hi := setIntegral_mono_on (integrable_gaussianPDFReal 0 v).integrableOn
    (show IntegrableOn (fun _ : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹)
      (Set.Icc a b) volume from integrableOn_const (measure_Icc_lt_top.ne))
    measurableSet_Icc (fun x _ => hb x)
  refine hi.trans_eq ?_
  rw [setIntegral_const, Measure.real, Real.volume_Icc]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul, div_eq_mul_inv]


theorem Sandpile.Support.measure_ball_survival_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 0 < d)
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {u : EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d u B P)
    (hcont : ∀ ω, Continuous fun t => B t ω) (A : ℝ) (hA : 0 ≤ A)
    {T : ℝ≥0} (hT : 0 < T) :
    P {ω | (T : ℝ≥0∞) < LatticeProb.exitTime B u A ω} ≤
      ENNReal.ofReal (2 * (Real.sqrt (d : ℝ) * A) /
        Real.sqrt (2 * Real.pi * (T : ℝ)))  := by
  let i : Fin d := ⟨0, hd⟩
  let C : ℝ := Real.sqrt (d : ℝ) * A
  let X : Ω → ℝ := fun ω => Real.sqrt (d : ℝ) * (B T ω i - u i)
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hA
  have hsub : {ω | (T : ℝ≥0∞) < LatticeProb.exitTime B u A ω} ⊆
      {ω | X ω ∈ Set.Icc (-C) C} := by
    intro ω hω
    have hn : ‖B T ω - u‖ < A := by
      by_contra h
      have he : LatticeProb.exitTime B u A ω ≤ (T : ℝ≥0∞) :=
        (LatticeProb.exitTime_le_iff hcont u A ω T).2 ⟨T, le_rfl, le_of_not_gt h⟩
      exact not_lt_of_ge he hω
    have hi : |B T ω i - u i| ≤ A := by
      have h := PiLp.norm_apply_le (B T ω - u) i
      have hi0 : |B T ω i - u i| ≤ ‖B T ω - u‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h
      exact hi0.trans hn.le
    have hab : |X ω| ≤ C := by
      dsimp [X, C]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)
    exact abs_le.mp hab
  refine (measure_mono hsub).trans ?_
  have hl := (hB.coord i).hasLaw_eval T
  have he : P {ω | X ω ∈ Set.Icc (-C) C} = gaussianReal 0 T (Set.Icc (-C) C) :=
    hl.measure_eq measurableSet_Icc
  rw [he]
  have hb := Sandpile.Support.gaussianReal_Icc_le_length (ne_of_gt hT) (-C) C
  have hCC : 0 ≤ 2 * C := by positivity
  simpa only [sub_neg_eq_add, ← two_mul, max_eq_left hCC] using hb


theorem Sandpile.Support.exists_ball_survival_small_uniform (d : ℕ) (hd : 0 < d)
    (A : ℝ) (hA : 0 ≤ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ T →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        (u : EuclideanSpace ℝ (Fin d)) (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)),
        LatticeProb.IsBrownianSpace d u B P → (∀ ω, Continuous fun t => B t ω) →
        P {ω | (T : ℝ≥0∞) < LatticeProb.exitTime B u A ω} ≤ ENNReal.ofReal δ  := by
  have hcoe : Tendsto (fun T : ℝ≥0 => (T : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hden : Tendsto (fun T : ℝ≥0 => Real.sqrt (2 * Real.pi * (T : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hcoe.const_mul_atTop (by positivity))
  have hlim := hden.const_div_atTop (2 * (Real.sqrt (d : ℝ) * A))
  have hlt : ∀ᶠ T : ℝ≥0 in atTop,
      2 * (Real.sqrt (d : ℝ) * A) / Real.sqrt (2 * Real.pi * (T : ℝ)) < δ :=
    hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hlt.and (eventually_gt_atTop (0 : ℝ≥0)))
  refine ⟨T₀, (hT₀ T₀ le_rfl).2, ?_⟩
  intro T hT Ω mΩ P u B hB hcont
  exact (Sandpile.Support.measure_ball_survival_le hd hB hcont A hA (hT₀ T hT).2).trans
    (ENNReal.ofReal_le_ofReal (hT₀ T hT).1.le)


theorem Sandpile.Support.ae_ball_exitTime_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d : ℕ} (hd : 0 < d)
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)} {u : EuclideanSpace ℝ (Fin d)}
    (hB : LatticeProb.IsBrownianSpace d u B P)
    (hcont : ∀ ω, Continuous fun t => B t ω) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᵐ ω ∂P, LatticeProb.exitTime B u A ω < ⊤  := by
  apply ae_iff.mpr
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨T, _, hsmall⟩ := Sandpile.Support.exists_ball_survival_small_uniform d hd A hA
    (ε : ℝ) (by exact_mod_cast hε)
  have hle := hsmall T le_rfl Ω P u B hB hcont
  have hsub : {ω | ¬ LatticeProb.exitTime B u A ω < ⊤} ⊆
      {ω | (T : ℝ≥0∞) < LatticeProb.exitTime B u A ω} := by
    intro ω hω
    have he : LatticeProb.exitTime B u A ω = ⊤ := by
      simpa only [Set.mem_setOf_eq, lt_top_iff_ne_top, not_not] using hω
    simpa only [Set.mem_setOf_eq, he] using ENNReal.coe_lt_top (r := T)
  exact (measure_mono hsub).trans (by simpa using hle)

