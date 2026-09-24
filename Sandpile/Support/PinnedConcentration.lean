/-
Conditional concentration for finite-coordinate scenery functionals. Coordinates
fixed by the conditioning receive zero Lipschitz weight.
-/
import Sandpile.Support.ConditionalConcentration

open LatticeProb

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

noncomputable def offWeight (S : Set (Site d)) (w : Site d → ℝ) (z : Site d) : ℝ := by
  classical
  exact if z ∈ S then 0 else w z

noncomputable def pinnedFunctional (S : Set (Site d)) (T : Finset (Site d))
    (F : (Site d → ℝ) → ℝ) (ω : Site d → ℝ) (ξ : Fin T.card → ℝ) : ℝ := by
  classical
  exact F (LatticeProb.comb S ω (siteExtend T ξ))

lemma measurable_pinnedFunctional (S : Set (Site d)) (T : Finset (Site d))
    {F : (Site d → ℝ) → ℝ} (hF : Measurable F) (ω : Site d → ℝ) :
    Measurable (pinnedFunctional S T F ω) := by
  classical
  exact hF.comp ((LatticeProb.measurable_comb S).comp (measurable_const.prodMk (measurable_siteExtend T)))

lemma pinnedFunctional_pick (S : Set (Site d)) [DecidablePred (· ∈ S)] (T : Finset (Site d))
    {F : (Site d → ℝ) → ℝ}
    (hF : ∀ ξ η, (∀ z ∈ T, ξ z = η z) → F ξ = F η) (ω η : Site d → ℝ) :
    pinnedFunctional S T F ω (fun i => η (siteEnum T i)) =
      F (LatticeProb.comb S ω η) := by
  classical
  apply hF
  intro z hz
  by_cases hS : z ∈ S
  · simp only [LatticeProb.comb, hS, if_pos]
  · simp only [LatticeProb.comb, hS, if_neg, not_false_iff]
    exact siteExtend_siteEnum T η hz

lemma comb_update_right {V : Type*} [DecidableEq V] (S : Set V) [DecidablePred (· ∈ S)]
    (ω η : V → ℝ) {v : V} (hv : v ∉ S) (a : ℝ) :
    LatticeProb.comb S ω (Function.update η v a) = Function.update (LatticeProb.comb S ω η) v a := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [LatticeProb.comb, hv]
  · by_cases hS : i ∈ S <;> simp [LatticeProb.comb, hS, Function.update_of_ne hi]

lemma comb_update_right_of_mem {V : Type*} [DecidableEq V] (S : Set V) [DecidablePred (· ∈ S)]
    (ω η : V → ℝ) {v : V} (hv : v ∈ S) (a : ℝ) :
    LatticeProb.comb S ω (Function.update η v a) = LatticeProb.comb S ω η := by
  funext i
  by_cases hi : i = v
  · subst i
    simp [LatticeProb.comb, hv]
  · by_cases hS : i ∈ S <;> simp [LatticeProb.comb, hS, Function.update_of_ne hi]

lemma abs_pinnedFunctional_update_le (S : Set (Site d)) (T : Finset (Site d))
    {F : (Site d → ℝ) → ℝ} {w : Site d → ℝ}
    (hLip : ∀ ω z a, |F ω - F (Function.update ω z a)| ≤ w z * |ω z - a|)
    (ω : Site d → ℝ) (ξ : Fin T.card → ℝ) (i : Fin T.card) (a : ℝ) :
    |pinnedFunctional S T F ω ξ - pinnedFunctional S T F ω (Function.update ξ i a)| ≤
      offWeight S w (siteEnum T i) * |ξ i - a| := by
  classical
  unfold pinnedFunctional
  rw [siteExtend_update]
  by_cases hi : siteEnum T i ∈ S
  · rw [comb_update_right_of_mem S ω (siteExtend T ξ) hi a]
    simp [offWeight, hi]
  · rw [comb_update_right S ω (siteExtend T ξ) hi a]
    have hval : LatticeProb.comb S ω (siteExtend T ξ) (siteEnum T i) = ξ i := by
      rw [LatticeProb.comb_apply_of_notMem hi]
      simp [siteExtend, siteEnum]
    simpa only [offWeight, hi, if_neg, not_false_iff, hval] using
      hLip (LatticeProb.comb S ω (siteExtend T ξ)) (siteEnum T i) a

lemma conditional_finite_concentration (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
      ∀ (T : Finset (Site d)) (S : Set (Site d)) (F : (Site d → ℝ) → ℝ),
        Measurable F → Integrable F (LatticeProb.iidLaw d ν) →
        (∀ ξ η, (∀ z ∈ T, ξ z = η z) → F ξ = F η) →
      ∀ w : Site d → ℝ, (∀ z, 0 ≤ w z) →
        (∀ ω z a, |F ω - F (Function.update ω z a)| ≤ w z * |ω z - a|) →
      ∀ A B : ℝ, (∑ z ∈ T, offWeight S w z ^ 2) ≤ A →
        (∀ z ∈ T, offWeight S w z ≤ B) → ∀ a : ℝ, 0 ≤ a →
        (LatticeProb.iidLaw d ν)
          {ω | a < |F ω - (MeasureTheory.condExp
            (MeasurableSpace.comap (fun ω : Site d → ℝ => fun y : S => ω y) inferInstance)
            (LatticeProb.iidLaw d ν) F) ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-(c * min (a ^ 2 / A) (a / B)))) := by
  classical
  obtain ⟨c, hc, htail⟩ := weighted_exp_conc_tail_norms θ K hθ
  refine ⟨c, hc, ?_⟩
  intro ν hν hexp hK T S F hFm hFi hFloc w hw hLip A B hA hB a ha
  haveI := hν
  apply measure_deviation_condExp_le S ν hFm hFi
  intro ω
  let G := pinnedFunctional S T F ω
  let ℓ := fun i : Fin T.card => offWeight S w (siteEnum T i)
  have hGm : Measurable G := measurable_pinnedFunctional S T hFm ω
  have hℓ : ∀ i, 0 ≤ ℓ i := by
    intro i
    dsimp [ℓ, offWeight]
    split_ifs
    · exact le_rfl
    · exact hw _
  have hTwo : ∑ i, ℓ i ^ 2 ≤ A := by
    rw [show (∑ i, ℓ i ^ 2) = ∑ z ∈ T, offWeight S w z ^ 2 from
      sum_siteEnum T (fun z => offWeight S w z ^ 2)]
    exact hA
  have hInf : ∀ i, ℓ i ≤ B := fun i => hB _ (siteEnum_mem T i)
  have ht := htail T.card ν hν hexp hK G hGm ℓ hℓ
    (abs_pinnedFunctional_update_le S T hLip ω) A B hTwo hInf a ha
  have hm : LatticeProb.partialInt (fun _ : Site d => ν) S F ω =
      ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin T.card => ν) := by
    rw [← integral_pick ν (siteEnum T) (siteEnum_injective T) G hGm.aestronglyMeasurable]
    apply integral_congr_ae
    exact Eventually.of_forall (fun η => (pinnedFunctional_pick S T hFloc ω η).symm)
  have hE : MeasurableSet {ξ : Fin T.card → ℝ |
      a < |G ξ - ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin T.card => ν)|} :=
    measurableSet_lt measurable_const (hGm.sub measurable_const).abs
  have he : {η : Site d → ℝ | a < |F (LatticeProb.comb S ω η) -
      LatticeProb.partialInt (fun _ : Site d => ν) S F ω|} =
      (fun η : Site d → ℝ => fun i => η (siteEnum T i)) ⁻¹'
        {ξ | a < |G ξ - ∫ ξ, G ξ ∂(Measure.pi fun _ : Fin T.card => ν)|} := by
    ext η
    simp only [Set.mem_preimage, Set.mem_setOf_eq, G, pinnedFunctional_pick S T hFloc, hm]
  rw [he]
  have hp := (LatticeProb.measurePreserving_pick _ ν (siteEnum T) (siteEnum_injective T)).measure_preimage hE.nullMeasurableSet
  change (Measure.infinitePi fun _ : Site d => ν) _ = _ at hp
  rw [hp]
  exact ht

end Sandpile
