/-
Finite couplings with prescribed marginals. Equal submasses are matched by
normalized product measures, and the remaining marginals are coupled separately.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.Continuum.exists_coupling_of_equal_finite_mass
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : μ univ = ν univ) :
    ∃ π : Measure (Ω × Ω'), π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧ π univ = μ univ := by
  by_cases hμ : μ univ = 0
  · have hν : ν univ = 0 := hm ▸ hμ
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 hμ
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.1 hν
    subst μ ν
    exact ⟨0, by simp, by simp, by simp⟩
  let π : Measure (Ω × Ω') := (μ univ)⁻¹ • μ.prod ν
  have hfst : π.map Prod.fst = μ := by
    simp only [π, Measure.map_smul, Measure.map_fst_prod, smul_smul, ← hm,
      ENNReal.inv_mul_cancel hμ (measure_ne_top μ univ), one_smul]
  have hsnd : π.map Prod.snd = ν := by
    simp only [π, Measure.map_smul, Measure.map_snd_prod, smul_smul,
      ENNReal.inv_mul_cancel hμ (measure_ne_top μ univ), one_smul]
  refine ⟨π, hfst, hsnd, ?_⟩
  rw [← hfst, Measure.map_apply measurable_fst MeasurableSet.univ]
  rfl

theorem Sandpile.Continuum.exists_coupling_extending_subcoupling
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (Ω × Ω')) [IsFiniteMeasure π]
    (hfst : π.map Prod.fst ≤ μ) (hsnd : π.map Prod.snd ≤ ν) :
    ∃ P R : Measure (Ω × Ω'), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ ∧ P.map Prod.snd = ν ∧ P = π + R ∧ R univ = 1 - π univ := by
  have hf : (π.map Prod.fst) univ = π univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
  have hs : (π.map Prod.snd) univ = π univ := by
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]; rfl
  have hm : (μ - π.map Prod.fst) univ = (ν - π.map Prod.snd) univ := by
    rw [Measure.sub_apply MeasurableSet.univ hfst, Measure.sub_apply MeasurableSet.univ hsnd,
      hf, hs, (measure_univ : μ univ = 1), (measure_univ : ν univ = 1)]
  obtain ⟨R, hRf, hRs, hRm⟩ := Sandpile.Continuum.exists_coupling_of_equal_finite_mass
    (μ - π.map Prod.fst) (ν - π.map Prod.snd) hm
  have hPf : (π + R).map Prod.fst = μ := by
    rw [Measure.map_add _ _ measurable_fst, hRf, add_comm, Measure.sub_add_cancel_of_le hfst]
  have hPs : (π + R).map Prod.snd = ν := by
    rw [Measure.map_add _ _ measurable_snd, hRs, add_comm, Measure.sub_add_cancel_of_le hsnd]
  have hP : IsProbabilityMeasure (π + R) := ⟨by
    have he := congrArg (fun m : Measure Ω => m univ) hPf
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at he
    exact he.trans (measure_univ : μ univ = 1)⟩
  refine ⟨π + R, R, hP, hPf, hPs, rfl, ?_⟩
  rw [hRm, Measure.sub_apply MeasurableSet.univ hfst, hf, (measure_univ : μ univ = 1)]

theorem Sandpile.Continuum.exists_coupling_matching_finite_measures
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (μs : Fin N → Measure Ω) (νs : Fin N → Measure Ω')
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, IsFiniteMeasure (νs i)]
    (hm : ∀ i, μs i univ = νs i univ)
    (hμs : ∑ i, μs i ≤ μ) (hνs : ∑ i, νs i ≤ ν) :
    ∃ (P R : Measure (Ω × Ω')) (π : Fin N → Measure (Ω × Ω')),
      IsProbabilityMeasure P ∧ P.map Prod.fst = μ ∧ P.map Prod.snd = ν ∧
      (∀ i, (π i).map Prod.fst = μs i ∧ (π i).map Prod.snd = νs i) ∧
      P = (∑ i, π i) + R ∧ R univ = 1 - ∑ i, μs i univ  := by
  classical
  choose π hπf hπs hπm using fun i =>
    Sandpile.Continuum.exists_coupling_of_equal_finite_mass (μs i) (νs i) (hm i)
  haveI : ∀ i, IsFiniteMeasure (π i) := fun i => ⟨by rw [hπm i]; exact measure_lt_top _ _⟩
  have hf : (∑ i, π i).map Prod.fst = ∑ i, μs i := by
    simp only [← Measure.mapₗ_apply_of_measurable measurable_fst, map_sum]
    congr 1
    ext i
    rw [Measure.mapₗ_apply_of_measurable measurable_fst, hπf]
  have hs : (∑ i, π i).map Prod.snd = ∑ i, νs i := by
    simp only [← Measure.mapₗ_apply_of_measurable measurable_snd, map_sum]
    congr 1
    ext i
    rw [Measure.mapₗ_apply_of_measurable measurable_snd, hπs]
  obtain ⟨P, R, hP, hPf, hPs, hPR, hRm⟩ :=
    Sandpile.Continuum.exists_coupling_extending_subcoupling μ ν (∑ i, π i)
      (hf.trans_le hμs) (hs.trans_le hνs)
  refine ⟨P, R, π, hP, hPf, hPs, fun i => ⟨hπf i, hπs i⟩, hPR, ?_⟩
  simpa only [Measure.finsetSum_apply, hπm] using hRm

theorem Sandpile.Continuum.exists_submeasure_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (a : ℝ≥0∞) (ha : a ≤ μ univ) :
    ∃ ν : Measure Ω, ν ≤ μ ∧ ν univ = a  := by
  by_cases h0 : μ univ = 0
  · have ha0 : a = 0 := le_antisymm (ha.trans_eq h0) zero_le
    exact ⟨0, bot_le, by simp [ha0]⟩
  have hc : a / μ univ ≤ 1 := by
    rw [ENNReal.div_le_iff h0 (measure_ne_top μ univ), one_mul]
    exact ha
  refine ⟨(a / μ univ) • μ, ?_, ?_⟩
  · intro s
    rw [Measure.smul_apply, smul_eq_mul]
    simpa only [one_mul] using mul_le_mul_left hc (μ s)
  · rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.div_mul_cancel h0 (measure_ne_top μ univ)]

theorem Sandpile.Continuum.sum_restrict_le_of_disjoint
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (A : Fin N → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∑ i, μ.restrict (A i) ≤ μ  := by
  have he := μ.restrict_iUnion hd hA
  rw [Measure.sum_fintype] at he
  rw [← he]
  exact Measure.restrict_le_self

theorem Sandpile.Continuum.coupling_compl_rectangle_null
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (π : Measure (Ω × Ω'))
    (A : Set Ω) (B : Set Ω') (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hf : π.map Prod.fst ≤ μ.restrict A) (hs : π.map Prod.snd ≤ ν.restrict B) :
    π (A ×ˢ B)ᶜ = 0  := by
  have hf0 : π (Prod.fst ⁻¹' Aᶜ) = 0 := by
    rw [← Measure.map_apply measurable_fst hA.compl]
    apply le_antisymm ((hf Aᶜ).trans_eq ?_) zero_le
    rw [Measure.restrict_apply hA.compl]
    simp
  have hs0 : π (Prod.snd ⁻¹' Bᶜ) = 0 := by
    rw [← Measure.map_apply measurable_snd hB.compl]
    apply le_antisymm ((hs Bᶜ).trans_eq ?_) zero_le
    rw [Measure.restrict_apply hB.compl]
    simp
  have he : (A ×ˢ B)ᶜ = (Prod.fst ⁻¹' Aᶜ) ∪ (Prod.snd ⁻¹' Bᶜ) := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_union, Set.mem_preimage]
    tauto
  rw [he]
  exact measure_union_null hf0 hs0

theorem Sandpile.Continuum.exists_coupling_matching_cells
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N : ℕ) (A : Fin N → Set Ω) (B : Fin N → Set Ω')
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hdA : Pairwise fun i j => Disjoint (A i) (A j))
    (hdB : Pairwise fun i j => Disjoint (B i) (B j)) :
    ∃ P : Measure (Ω × Ω'), IsProbabilityMeasure P ∧
      P.map Prod.fst = μ ∧ P.map Prod.snd = ν ∧
      P (⋃ i, A i ×ˢ B i)ᶜ ≤ 1 - ∑ i, min (μ (A i)) (ν (B i)) := by
  classical
  let a : Fin N → ℝ≥0∞ := fun i => min (μ (A i)) (ν (B i))
  have hma : ∀ i, ∃ m : Measure Ω, m ≤ μ.restrict (A i) ∧ m univ = a i := by
    intro i
    apply Sandpile.Continuum.exists_submeasure_mass
    simpa only [Measure.restrict_apply_univ] using min_le_left (μ (A i)) (ν (B i))
  have hmb : ∀ i, ∃ m : Measure Ω', m ≤ ν.restrict (B i) ∧ m univ = a i := by
    intro i
    apply Sandpile.Continuum.exists_submeasure_mass
    simpa only [Measure.restrict_apply_univ] using min_le_right (μ (A i)) (ν (B i))
  choose μs hμs hμm using hma
  choose νs hνs hνm using hmb
  haveI : ∀ i, IsFiniteMeasure (μs i) := fun i => isFiniteMeasure_of_le (μ.restrict (A i)) (hμs i)
  haveI : ∀ i, IsFiniteMeasure (νs i) := fun i => isFiniteMeasure_of_le (ν.restrict (B i)) (hνs i)
  have hμle : ∑ i, μs i ≤ μ :=
    (Finset.sum_le_sum fun i _ => hμs i).trans
      (Sandpile.Continuum.sum_restrict_le_of_disjoint μ N A hA hdA)
  have hνle : ∑ i, νs i ≤ ν :=
    (Finset.sum_le_sum fun i _ => hνs i).trans
      (Sandpile.Continuum.sum_restrict_le_of_disjoint ν N B hB hdB)
  obtain ⟨P, R, π, hP, hPf, hPs, hπ, hPR, hRm⟩ :=
    Sandpile.Continuum.exists_coupling_matching_finite_measures μ ν N μs νs
      (fun i => (hμm i).trans (hνm i).symm) hμle hνle
  have hz : ∀ i, π i (⋃ j, A j ×ˢ B j)ᶜ = 0 := by
    intro i
    apply measure_mono_null (compl_subset_compl.mpr (subset_iUnion (fun j => A j ×ˢ B j) i))
    exact Sandpile.Continuum.coupling_compl_rectangle_null μ ν (π i) (A i) (B i) (hA i) (hB i)
      ((hπ i).1.trans_le (hμs i)) ((hπ i).2.trans_le (hνs i))
  refine ⟨P, hP, hPf, hPs, ?_⟩
  rw [hPR, Measure.add_apply, Measure.finsetSum_apply, Finset.sum_eq_zero (fun i _ => hz i), zero_add]
  calc
    R (⋃ i, A i ×ˢ B i)ᶜ ≤ R univ := measure_mono (subset_univ _)
    _ = 1 - ∑ i, min (μ (A i)) (ν (B i)) := by simpa only [hμm, a] using hRm
