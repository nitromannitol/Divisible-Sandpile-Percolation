import Sandpile.External.ContinuumRSW.SampledCrossing

/-!
# Limits of crossing comparisons

An increasing comparison passes through almost-sure lower and upper event
approximations under a probability measure.
-/

open Filter MeasureTheory Set Topology

namespace Sandpile.External.ContinuumRSW

open Sandpile Sandpile.Support

/-- A uniform comparison passes to events approximated almost surely from below
and above. -/
theorem comparison_of_eventual_event_bounds {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (A B : Set Ω) (E F : ℕ → Set Ω)
    (hEm : ∀ n, MeasurableSet (E n)) (hFm : ∀ n, MeasurableSet (F n))
    (hcomp : ∀ n, (ψ (probabilityInUnitInterval P (E n)) : ℝ) ≤ P.real (F n))
    (happrox : ∀ᵐ ω ∂P,
      (ω ∈ A → ∃ N, ∀ n ≥ N, ω ∈ E n) ∧
      ((∀ N, ∃ n ≥ N, ω ∈ F n) → ω ∈ B)) :
    (ψ (probabilityInUnitInterval P A) : ℝ) ≤ P.real B := by
  let D : ℕ → Set Ω := fun N => ⋂ n ≥ N, E n
  let C : ℕ → Set Ω := fun N => ⋃ n ≥ N, F n
  have hDm : ∀ N, MeasurableSet (D N) := fun N =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hEm n
  have hCm : ∀ N, MeasurableSet (C N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hFm n
  have hDmono : Monotone D := by
    intro N M hNM ω hω
    exact mem_iInter₂.mpr fun n hn => mem_iInter₂.mp hω n (hNM.trans hn)
  have hCanti : Antitone C := by
    intro N M hNM ω hω
    obtain ⟨n, hn, hωn⟩ := mem_iUnion₂.mp hω
    exact mem_iUnion₂.mpr ⟨n, hNM.trans hn, hωn⟩
  have hA : A ≤ᵐ[P] ⋃ N, D N := by
    filter_upwards [happrox] with ω hω hωA
    obtain ⟨N, hN⟩ := hω.1 hωA
    exact mem_iUnion.mpr ⟨N, mem_iInter₂.mpr hN⟩
  have hB : (⋂ N, C N) ≤ᵐ[P] B := by
    filter_upwards [happrox] with ω hω hωC
    apply hω.2
    intro N
    obtain ⟨n, hn, hnF⟩ := mem_iUnion₂.mp (mem_iInter.mp hωC N)
    exact ⟨n, hn, hnF⟩
  have hprobA : P.real A ≤ P.real (⋃ N, D N) :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hA)
  have hprobB : P.real (⋂ N, C N) ≤ P.real B :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hB)
  have hDC : ∀ N, (ψ (probabilityInUnitInterval P (D N)) : ℝ) ≤ P.real (C N) := by
    intro N
    have hDE : probabilityInUnitInterval P (D N) ≤ probabilityInUnitInterval P (E N) :=
      measureReal_mono (iInter₂_subset N le_rfl)
    have hFC : P.real (F N) ≤ P.real (C N) :=
      measureReal_mono (fun ω hω => mem_iUnion₂.mpr ⟨N, le_rfl, hω⟩) (measure_ne_top P _)
    have hψ : (ψ (probabilityInUnitInterval P (D N)) : ℝ) ≤
        (ψ (probabilityInUnitInterval P (E N)) : ℝ) := ψ.monotone hDE
    exact (hψ.trans (hcomp N)).trans hFC
  have hDlim : Tendsto (fun N => probabilityInUnitInterval P (D N)) atTop
      (𝓝 (probabilityInUnitInterval P (⋃ N, D N))) :=
    tendsto_subtype_rng.mpr (tendsto_measureReal_iUnion D hDmono)
  have hClim : Tendsto (fun N => P.real (C N)) atTop (𝓝 (P.real (⋂ N, C N))) :=
    tendsto_measureReal_iInter C hCm hCanti
  have hlim : (ψ (probabilityInUnitInterval P (⋃ N, D N)) : ℝ) ≤
      P.real (⋂ N, C N) :=
    le_of_tendsto_of_tendsto'
      (continuous_subtype_val.continuousAt.tendsto.comp (ψ.continuous.continuousAt.tendsto.comp hDlim))
      hClim hDC
  have hleft : probabilityInUnitInterval P A ≤ probabilityInUnitInterval P (⋃ N, D N) := hprobA
  have hleft' : (ψ (probabilityInUnitInterval P A) : ℝ) ≤
      (ψ (probabilityInUnitInterval P (⋃ N, D N)) : ℝ) := ψ.monotone hleft
  exact (hleft'.trans hlim).trans hprobB

end Sandpile.External.ContinuumRSW
