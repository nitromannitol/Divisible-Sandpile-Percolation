import Mathlib

/-!
# Finite couplings with prescribed marginals

Finite couplings with prescribed marginals. Equal submasses are matched by normalized product
measures, and the remaining marginals are coupled separately.

The construction proceeds in stages: `exists_coupling_of_equal_finite_mass` couples two finite
measures of equal total mass by a rescaled product measure; `exists_coupling_extending_subcoupling`
extends a subcoupling of two probability measures to a full coupling by matching the leftover mass
on each side; `exists_coupling_matching_finite_measures` iterates this over finitely many pairs of
submeasures with equal pairwise mass. `exists_submeasure_mass` extracts a submeasure of any
prescribed mass below the total, and `sum_restrict_le_of_disjoint` bounds the sum of restrictions
to disjoint sets. `coupling_compl_rectangle_null` shows a coupling whose marginals are confined to
`A` and `B` puts no mass off the rectangle `A ×ˢ B`. These combine in
`exists_coupling_matching_cells` to build a coupling of `μ` and `ν` that matches disjoint cells
`A i, B i` as closely as possible, leaving mass at most `1 - ∑ min (μ (A i)) (ν (B i))` off the
union of matched rectangles.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- Two finite measures `μ, ν` of equal total mass admit a coupling `π` (with `π.map Prod.fst = μ`
and `π.map Prod.snd = ν`) built by rescaling the product measure `μ.prod ν` by `(μ univ)⁻¹`, which
also preserves the total mass `π univ = μ univ`. -/
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

/-- **Extending a subcoupling to a full coupling.** Given probability measures `μ, ν` and a
finite subcoupling `π` whose marginals are dominated by `μ, ν`, there is a full coupling
`P = π + R` for some remainder `R`, obtained by matching the leftover marginal masses
`μ - π.map Prod.fst` and `ν - π.map Prod.snd` (which are equal, both `1 - π univ`) via
`exists_coupling_of_equal_finite_mass`. -/
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

/-- **Coupling finitely many matched submeasure pairs, extended to a full coupling.** Given
finitely many pairs of submeasures `μs i ≤ μ`, `νs i ≤ ν` with `μs i univ = νs i univ` for each
`i`, there are individual couplings `π i` of `μs i, νs i` (via
`exists_coupling_of_equal_finite_mass`) whose sum extends, via
`exists_coupling_extending_subcoupling`, to a full coupling `P` of `μ, ν`. -/
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

/-- Any target mass `a ≤ μ univ` is realized as the total mass of a submeasure `ν ≤ μ`, by
rescaling `μ` by the ratio `a / μ univ`. -/
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

/-- The sum of the restrictions of `μ` to finitely many pairwise disjoint measurable sets `A i`
is bounded above by `μ` itself, since the restrictions sum to the restriction of `μ` to the
disjoint union `⋃ i, A i`. -/
theorem Sandpile.Continuum.sum_restrict_le_of_disjoint
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : ℕ) (A : Fin N → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∑ i, μ.restrict (A i) ≤ μ  := by
  have he := μ.restrict_iUnion hd hA
  rw [Measure.sum_fintype] at he
  rw [← he]
  exact Measure.restrict_le_self

/-- If a coupling `π`'s marginals are confined to `μ.restrict A` and `ν.restrict B`, then `π`
gives zero mass to the complement of the rectangle `A ×ˢ B`, since the complement splits as the
union of the preimages of `Aᶜ` and `Bᶜ` under the two projections, each of which is `π`-null. -/
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

/-- **The cell-matching coupling.** Given disjoint measurable cells `A i` partitioning part of
`Ω` and `B i` partitioning part of `Ω'`, there is a coupling `P` of `μ, ν` that puts mass
`min (μ (A i)) (ν (B i))` on each rectangle `A i ×ˢ B i` (via `exists_submeasure_mass` on each
side and `exists_coupling_matching_finite_measures` to assemble and extend them), leaving mass
at most `1 - ∑ i, min (μ (A i)) (ν (B i))` off the union of the matched rectangles, by
`coupling_compl_rectangle_null` applied cell by cell. -/
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
  rw [hPR, Measure.add_apply, Measure.finsetSum_apply,
    Finset.sum_eq_zero (fun i _ => hz i), zero_add]
  calc
    R (⋃ i, A i ×ˢ B i)ᶜ ≤ R univ := measure_mono (subset_univ _)
    _ = 1 - ∑ i, min (μ (A i)) (ν (B i)) := by simpa only [hμm, a] using hRm
