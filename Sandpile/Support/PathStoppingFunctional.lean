import Sandpile.Support.StoppingTimeRepresentative
import Sandpile.Continuum.Stopping
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Stopping times as path functionals

A bounded natural-filtration stopping time has an almost-everywhere equal
right-continuation stopping functional on path space.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A bounded natural-filtration stop admits an almost-everywhere equal bounded
right-continuation stopping functional on path space. -/
theorem Sandpile.Support.exists_path_stoppingTime_of_brownianStopping
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    ∃ θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0,
      IsStoppingTime (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable)).rightCont
        (fun p => (θ p : ℝ≥0∞)) ∧
      (∀ p, θ p ≤ T) ∧ (fun ω => θ (fun t => B t ω)) =ᵐ[P] τ := by
  classical
  let Path := ℝ≥0 → Sandpile.Continuum.Space d
  let path : Ω → Path := fun ω t => B t ω
  let C : ℝ≥0 → Path → Sandpile.Continuum.Space d := fun t p => p t
  have hpath : Measurable path := Measurable.of_eval fun t => (hBm t).measurable
  have hCm : ∀ t, StronglyMeasurable (C t) := fun t => (measurable_pi_apply t).stronglyMeasurable
  let F := LatticeProb.natFiltration C hCm
  have hτm : @Measurable Ω ℝ≥0 (MeasurableSpace.comap path inferInstance) inferInstance τ :=
    measurable_coe_nnreal_ennreal_iff.1
      (MeasureTheory.IsStoppingTime.measurable hτ |>.mono
        (MeasureTheory.IsStoppingTime.measurableSpace_le hτ) le_rfl)
  obtain ⟨f, hfm, hf⟩ := hτm.exists_eq_measurable_comp
  let τpath : Path → ℝ≥0 := fun p => min (f p) T
  have hτpathm : Measurable τpath := hfm.min measurable_const
  have heq : ∀ ω, τpath (path ω) = τ ω := by
    intro ω
    have hh : τ ω = f (path ω) := congrFun hf ω
    simp only [τpath, ← hh, min_eq_left (hτT ω)]
  have hrep : ∀ q, ∃ A : Set Path, MeasurableSet[F q] A ∧
      ∀ᵐ p ∂P.map path, p ∈ A ↔ τpath p < q := by
    intro q
    have hτq := hτ.measurableSet_lt q
    rw [Sandpile.Continuum.brownianFiltration, Filtration.natural_eq_comap] at hτq
    obtain ⟨S, hS, hSeq⟩ := hτq
    let A : Set Path := (fun p (s : Set.Iic q) => p s) ⁻¹' S
    have hA : MeasurableSet[F q] A := by
      change MeasurableSet[LatticeProb.natFiltration C hCm q] A
      rw [LatticeProb.natFiltration_eq_comap]
      exact ⟨S, hS, rfl⟩
    have hAambient : MeasurableSet A := (F.le q) _ hA
    have hτevent : MeasurableSet {p : Path | τpath p < q} :=
      measurableSet_lt hτpathm measurable_const
    have hiff : MeasurableSet {p : Path | p ∈ A ↔ τpath p < q} := by
      convert (hAambient.inter hτevent).union (hAambient.compl.inter hτevent.compl) using 1
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    refine ⟨A, hA, (ae_map_iff hpath.aemeasurable hiff).2 ?_⟩
    filter_upwards [] with ω
    rw [heq]
    change ((fun s : Set.Iic q => B s ω) ∈ S) ↔ τ ω < q
    have hh := Set.ext_iff.mp hSeq ω
    change ((fun s : Set.Iic q => B s ω) ∈ S) ↔
      ((τ ω : ℝ≥0∞) < (q : ℝ≥0∞)) at hh
    exact hh.trans ENNReal.coe_lt_coe
  obtain ⟨θ, hθstop, hθT, hθeq⟩ :=
    Sandpile.Support.exists_stoppingTime_rightCont_of_thresholds (P.map path) F τpath T
      (fun p => min_le_right _ _) hrep
  refine ⟨θ, hθstop, hθT, ?_⟩
  filter_upwards [ae_of_ae_map hpath.aemeasurable hθeq] with ω hω
  exact hω.trans (heq ω)

/-- A right-continuation stopping functional remains a stopping time when
evaluated on a measurable process. -/
theorem Sandpile.Support.isStoppingTime_path_comp_rightCont
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθ : IsStoppingTime (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable)).rightCont
      (fun p => (θ p : ℝ≥0∞))) :
    IsStoppingTime (LatticeProb.natFiltration B hBm).rightCont
      (fun ω => (θ (fun t => B t ω) : ℝ≥0∞)) := by
  intro s
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro t
  rw [MeasurableSpace.measurableSet_iInf]
  intro hst
  have hθs := (hθ.measurableSet_le s)
  have hle : (LatticeProb.natFiltration
      (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
      (fun t => (measurable_pi_apply t).stronglyMeasurable)).rightCont s ≤
      (LatticeProb.natFiltration
        (fun t (p : ℝ≥0 → Sandpile.Continuum.Space d) => p t)
        (fun t => (measurable_pi_apply t).stronglyMeasurable)) t := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t hst
  have he := hle _ hθs
  rw [LatticeProb.natFiltration_eq_comap] at he
  obtain ⟨S, hS, hEq⟩ := he
  rw [LatticeProb.natFiltration_eq_comap]
  refine ⟨S, hS, ?_⟩
  ext ω
  have hh := Set.ext_iff.mp hEq (fun t => B t ω)
  exact hh
