/-
Concentration with an explicit factor two, coordinate conditioning, and the
transfer of uniform deviation bounds for spliced fields to conditional expectations.
-/
import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms
import Sandpile.Support.FiniteCoord
import LatticeProb.Prob.EfronSteinCountable

open LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Sandpile

theorem weighted_exp_conc_tail_two (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ r : ℝ, 0 ≤ r →
            (Measure.pi fun _ : Fin N => ν)
                {ξ | r ≤ |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
              ENNReal.ofReal (2 * Real.exp (-(c * min (r ^ 2 / lTwoNorm ℓ ^ 2)
                (r / lInfNorm ℓ)))) := by
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  set C₀ : ℝ := 16 * (Real.exp K * K) / θ₀ ^ 2 with hC₀def
  have hC₀ : 0 < C₀ := by
    rw [hC₀def]
    have : (0 : ℝ) < K := by linarith
    positivity
  refine ⟨min (1 / (4 * C₀)) (θ₀ / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro N ν hprob hexp hK' F hFm ℓ hℓ hne hLip r hr
  haveI := hprob
  have hKle : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K := le_trans hK' (le_max_left _ _)
  have hL0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
  have hL2 : 0 < lTwoNorm ℓ := lTwoNorm_pos ℓ hℓ hne
  set μ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hμdef
  have hSGgen : ∀ H : (Fin N → ℝ) → ℝ, Measurable H →
      (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
        |H ξ - H (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
      SubGaussianOn (fun ξ => H ξ - ∫ η, H η ∂μ) (C₀ * lTwoNorm ℓ ^ 2)
        (θ₀ / (2 * lInfNorm ℓ)) μ := by
    intro H hHm hHLip s hs
    have hprod : |s| * lInfNorm ℓ ≤ θ₀ / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * lInfNorm ℓ)] at hs
      have h2 : |s| * (2 * lInfNorm ℓ) = 2 * (|s| * lInfNorm ℓ) := by ring
      rw [h2] at hs
      linarith
    have hgap : ∀ i, |s| * ℓ i ≤ θ₀ - θ₀ / 2 := by
      intro i
      have h1 := mul_le_mul_of_nonneg_left (le_lInfNorm ℓ i) (abs_nonneg s)
      linarith
    have hgap' : ∀ i, |s| * ℓ i ≤ θ₀ := fun i => le_trans (hgap i) (by linarith)
    refine ⟨integrable_exp_lip ν θ₀ hexp H hHm ℓ hHLip s hgap' _, ?_⟩
    have h := exp_conc_pi ν θ₀ K (θ₀ / 2) hθ₀ (by linarith) (by linarith) hexp hKle s
      N H hHm ℓ hℓ hHLip hgap
    refine le_trans h (le_of_eq (congrArg Real.exp ?_))
    rw [hC₀def, lTwoNorm_sq]
    field_simp
    ring
  have hSG1 := hSGgen F hFm hLip
  have hSG2 := hSGgen (fun ξ => -F ξ) hFm.neg (fun ξ i y => by
    show |(-F ξ) - (-F (Function.update ξ i y))| ≤ ℓ i * |ξ i - y|
    have he : |(-F ξ) - (-F (Function.update ξ i y))|
        = |F ξ - F (Function.update ξ i y)| := by
      rw [← abs_neg]
      congr 1
      ring
    rw [he]
    exact hLip ξ i y)
  have hcpos : 0 < C₀ * lTwoNorm ℓ ^ 2 := by positivity
  have hs₀pos : 0 < θ₀ / (2 * lInfNorm ℓ) := by positivity
  have h1 := measure_ge_le_of_subGaussianOn μ _ _ _ hcpos hs₀pos hSG1 r hr
  have h2 := measure_ge_le_of_subGaussianOn μ _ _ _ hcpos hs₀pos hSG2 r hr
  set EF : ℝ := ∫ η, F η ∂μ with hEFdef
  have hnegint : ∫ η, (fun ξ => -F ξ) η ∂μ = -EF := by
    show ∫ η, -F η ∂μ = -EF
    rw [integral_neg, hEFdef]
  rw [hnegint] at h2
  set B : ℝ := Real.exp (-min (r ^ 2 / (4 * (C₀ * lTwoNorm ℓ ^ 2)))
    (θ₀ / (2 * lInfNorm ℓ) * r / 2)) with hBdef
  have hB1 : μ {ξ | r ≤ F ξ - EF} ≤ ENNReal.ofReal B :=
    measure_le_ofReal μ _ B h1
  have hB2 : μ {ξ | r ≤ -F ξ - -EF} ≤ ENNReal.ofReal B :=
    measure_le_ofReal μ _ B h2
  have hsubset : {ξ : Fin N → ℝ | r ≤ |F ξ - EF|}
      ⊆ {ξ | r ≤ F ξ - EF} ∪ {ξ | r ≤ -F ξ - -EF} := by
    intro ξ hξ
    rcases abs_cases (F ξ - EF) with ⟨he, _⟩ | ⟨he, _⟩
    · left
      show r ≤ F ξ - EF
      rw [← he]
      exact hξ
    · right
      show r ≤ -F ξ - -EF
      have : -F ξ - -EF = -(F ξ - EF) := by ring
      rw [this, ← he]
      exact hξ
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hfinal : B ≤ Real.exp (-(min (1 / (4 * C₀)) (θ₀ / 4) *
      min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ))) := by
    refine Real.exp_le_exp.mpr ?_
    have hmin0 : 0 ≤ min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ) :=
      le_min (by positivity) (by positivity)
    have hc0 : 0 ≤ min (1 / (4 * C₀)) (θ₀ / 4) :=
      le_min (by positivity) (by positivity)
    have hA : min (1 / (4 * C₀)) (θ₀ / 4) * min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
        ≤ r ^ 2 / (4 * (C₀ * lTwoNorm ℓ ^ 2)) := by
      have hstep : min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
          ≤ (1 / (4 * C₀)) * (r ^ 2 / lTwoNorm ℓ ^ 2) :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin0 (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      field_simp
    have hBb : min (1 / (4 * C₀)) (θ₀ / 4) * min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
        ≤ θ₀ / (2 * lInfNorm ℓ) * r / 2 := by
      have hstep : min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
          ≤ (θ₀ / 4) * (r / lInfNorm ℓ) :=
        mul_le_mul (min_le_right _ _) (min_le_right _ _) hmin0 (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      field_simp
      ring
    have := le_min hA hBb
    linarith
  calc μ {ξ : Fin N → ℝ | r ≤ |F ξ - EF|}
      ≤ μ ({ξ | r ≤ F ξ - EF} ∪ {ξ | r ≤ -F ξ - -EF}) := measure_mono hsubset
    _ ≤ μ {ξ | r ≤ F ξ - EF} + μ {ξ | r ≤ -F ξ - -EF} := measure_union_le _ _
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hB1 hB2
    _ = ENNReal.ofReal (2 * B) := by
        rw [← ENNReal.ofReal_add hB0 hB0]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [hfinal]

lemma weighted_exp_conc_tail_norms (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
      ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
      ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) →
        (∀ ξ i y, |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
      ∀ A B : ℝ, (∑ i, ℓ i ^ 2) ≤ A → (∀ i, ℓ i ≤ B) → ∀ a : ℝ, 0 ≤ a →
        (Measure.pi fun _ : Fin N => ν)
          {ξ | a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * min (a ^ 2 / A) (a / B)))) := by
  obtain ⟨c, hc, htail⟩ := weighted_exp_conc_tail_two θ K hθ
  refine ⟨c, hc, ?_⟩
  intro N ν hν hexp hK F hFm ℓ hℓ hLip A B hA hB a ha
  haveI := hν
  by_cases hne : ∃ i, ℓ i ≠ 0
  · haveI : Nonempty (Fin N) := ⟨hne.choose⟩
    have hInf0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
    have hTwo0 : 0 < lTwoNorm ℓ ^ 2 := sq_pos_of_pos (lTwoNorm_pos ℓ hℓ hne)
    have hTwo : lTwoNorm ℓ ^ 2 ≤ A := by rwa [lTwoNorm_sq]
    have hInf : lInfNorm ℓ ≤ B := ciSup_le hB
    have hmin : min (a ^ 2 / A) (a / B) ≤ min (a ^ 2 / lTwoNorm ℓ ^ 2) (a / lInfNorm ℓ) :=
      min_le_min (div_le_div_of_nonneg_left (sq_nonneg a) hTwo0 hTwo)
        (div_le_div_of_nonneg_left ha hInf0 hInf)
    have ht := htail N ν hν hexp hK F hFm ℓ hℓ hne hLip a ha
    refine (measure_mono (fun ξ (hξ : a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|) =>
      hξ.le)).trans (ht.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hmin hc.le))) (by norm_num)
  · have hz : ∀ i, ℓ i = 0 := by simpa using hne
    have hconst : ∀ ξ, F ξ = F 0 := by
      intro ξ
      have h := abs_sub_le_sum_lip F ℓ hLip ξ 0
      simp only [hz, zero_mul, Finset.sum_const_zero] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hm : (∫ ξ, F ξ ∂(Measure.pi fun _ : Fin N => ν)) = F 0 := by
      rw [integral_congr_ae (Eventually.of_forall hconst), integral_const]
      simp
    have he : {ξ : Fin N → ℝ | a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hξ
      change a < |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)| at hξ
      rw [hconst ξ, hm, sub_self, abs_zero] at hξ
      exact ha.not_gt hξ
    rw [he, measure_empty]
    exact bot_le

section Coordinates

variable {V : Type*} (S : Set V) [DecidablePred (· ∈ S)]

lemma coordAlg_eq_restriction : LatticeProb.coordAlg S =
    MeasurableSpace.comap (fun ω : V → ℝ => fun y : S => ω y) inferInstance := by
  let m := MeasurableSpace.comap (fun ω : V → ℝ => fun y : S => ω y) inferInstance
  apply le_antisymm
  · have hm : Measurable[m] (fun ω : V → ℝ => fun y : S => ω y) := Measurable.of_comap_le le_rfl
    have ht : @Measurable (V → ℝ) (V → ℝ) m MeasurableSpace.pi (LatticeProb.truncate S) := by
      refine @measurable_pi_lambda (V → ℝ) V (fun _ => ℝ) m (fun _ => Real.measurableSpace) _ ?_
      intro i
      by_cases hi : i ∈ S
      · simpa only [LatticeProb.truncate, LatticeProb.comb, hi, if_pos, Function.comp_def] using
          (measurable_pi_apply (⟨i, hi⟩ : S)).comp hm
      · simpa only [LatticeProb.truncate, LatticeProb.comb, hi, if_neg, not_false_iff, Pi.zero_apply] using
          (measurable_const : Measurable[m] (fun _ : V → ℝ => (0 : ℝ)))
    exact ht.comap_le
  · have hm : @Measurable (V → ℝ) (S → ℝ) (LatticeProb.coordAlg S) MeasurableSpace.pi
        (fun ω : V → ℝ => fun y : S => ω y) := by
      refine @measurable_pi_lambda (V → ℝ) S (fun _ => ℝ) (LatticeProb.coordAlg S)
        (fun _ => Real.measurableSpace) _ ?_
      intro y
      exact Measurable.of_comap_le (LatticeProb.comap_eval_le_coordAlg y.property)
    exact hm.comap_le

lemma partialInt_comb (ν : Measure ℝ) (F : (V → ℝ) → ℝ) (ω η : V → ℝ) :
    LatticeProb.partialInt (fun _ : V => ν) S F (LatticeProb.comb S ω η) =
      LatticeProb.partialInt (fun _ : V => ν) S F ω :=
  LatticeProb.partialInt_congr _ S F (fun _ hi => LatticeProb.comb_apply_of_mem hi)

lemma measure_deviation_partialInt_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {F : (V → ℝ) → ℝ} (hF : Measurable F) {a : ℝ} {B : ℝ≥0∞}
    (hB : ∀ ω : V → ℝ, (Measure.infinitePi fun _ : V => ν)
      {η | a < |F (LatticeProb.comb S ω η) - LatticeProb.partialInt (fun _ : V => ν) S F ω|} ≤ B) :
    (Measure.infinitePi fun _ : V => ν)
      {ω | a < |F ω - LatticeProb.partialInt (fun _ : V => ν) S F ω|} ≤ B := by
  let P := Measure.infinitePi (fun _ : V => ν)
  let E := {ω : V → ℝ | a < |F ω - LatticeProb.partialInt (fun _ : V => ν) S F ω|}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const ((hF.sub (LatticeProb.measurable_partialInt _ S hF)).abs)
  rw [← (LatticeProb.measurePreserving_comb (fun _ : V => ν) S).measure_preimage hE.nullMeasurableSet]
  rw [Measure.prod_apply ((LatticeProb.measurable_comb S) hE)]
  calc
    _ ≤ ∫⁻ _ : V → ℝ, B ∂P := by
      apply lintegral_mono
      intro ω
      change (Measure.infinitePi fun _ : V => ν)
        {η | a < |F (LatticeProb.comb S ω η) -
          LatticeProb.partialInt (fun _ : V => ν) S F (LatticeProb.comb S ω η)|} ≤ B
      simpa only [partialInt_comb] using hB ω
    _ = B := by simp [P]

lemma measure_deviation_condExp_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {F : (V → ℝ) → ℝ} (hF : Measurable F)
    (hFi : Integrable F (Measure.infinitePi fun _ : V => ν)) {a : ℝ} {B : ℝ≥0∞}
    (hB : ∀ ω : V → ℝ, (Measure.infinitePi fun _ : V => ν)
      {η | a < |F (LatticeProb.comb S ω η) - LatticeProb.partialInt (fun _ : V => ν) S F ω|} ≤ B) :
    (Measure.infinitePi fun _ : V => ν)
      {ω | a < |F ω - (MeasureTheory.condExp
        (MeasurableSpace.comap (fun ω : V → ℝ => fun y : S => ω y) inferInstance)
        (Measure.infinitePi fun _ : V => ν) F) ω|} ≤ B := by
  have he := LatticeProb.partialInt_ae_eq_condExp (S := S) ν hF hFi
  rw [coordAlg_eq_restriction] at he
  have hevent : {ω : V → ℝ | a < |F ω - (MeasureTheory.condExp
        (MeasurableSpace.comap (fun ω : V → ℝ => fun y : S => ω y) inferInstance)
        (Measure.infinitePi fun _ : V => ν) F) ω|}
      =ᵐ[Measure.infinitePi fun _ : V => ν]
      {ω : V → ℝ | a < |F ω - LatticeProb.partialInt (fun _ : V => ν) S F ω|} := by
    filter_upwards [he] with ω hω
    change (a < |F ω - (MeasureTheory.condExp
        (MeasurableSpace.comap (fun ω : V → ℝ => fun y : S => ω y) inferInstance)
        (Measure.infinitePi fun _ : V => ν) F) ω|) =
      (a < |F ω - LatticeProb.partialInt (fun _ : V => ν) S F ω|)
    exact congrArg (fun z : ℝ => a < |F ω - z|) hω.symm
  rw [measure_congr hevent]
  exact measure_deviation_partialInt_le S ν hF hB

end Coordinates

end Sandpile
