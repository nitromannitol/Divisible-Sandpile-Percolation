import Sandpile.Support.LimTailEvents

/-!
# Crossing chains under almost-sure equality and Kolmogorov's zero-one law

Countable crossing chains respect coordinatewise almost-everywhere equality and
uniformly bounded perturbations at the crossing scale. Measurable representatives
in every coordinate tail have one representative in the tail intersection,
where Kolmogorov's zero-one law applies.
-/

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal RealInnerProductSpace

/-- The path event `pathEvent X l n v` depends on the field `X` only through its
almost-sure equivalence class: if `X u =ᵐ[P] Y u` for every `u`, then `pathEvent X`
and `pathEvent Y` agree almost everywhere, since the event only reads finitely
many rational-point values `X (segPt (v j) (v (j+1)) q)`. -/
theorem Sandpile.Support.pathEvent_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Space 2 → Ω → ℝ}
    (heq : ∀ u, X u =ᵐ[P] Y u) (l : ℝ) (n : ℕ) (v : ℕ → Space 2) :
    pathEvent X l n v =ᵐ[P] pathEvent Y l n v := by
  have h : ∀ᵐ ω ∂P, ∀ (j : ℕ) (q : ℚ),
      X (segPt (v j) (v (j+1)) q) ω = Y (segPt (v j) (v (j+1)) q) ω :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun q => heq _
  filter_upwards [h] with ω hω
  apply propext
  simp only [pathEvent]
  exact forall_congr' fun j => forall_congr' fun q => by rw [hω j q]

/-- `crossApprox X a b i l` inherits the almost-sure equality of `pathEvent_ae_eq`:
a countable union, over the countably many good chains, of path events that are
each almost surely unchanged by replacing `X` with an almost-everywhere-equal
`Y`. -/
theorem Sandpile.Support.crossApprox_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Space 2 → Ω → ℝ}
    (heq : ∀ u, X u =ᵐ[P] Y u) (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    crossApprox X a b i l =ᵐ[P] crossApprox Y a b i l := by
  have h : ∀ᵐ ω ∂P, ∀ ch : {ch : VertexChain a b // GoodChain a b i ch},
      pathEvent X l (ch.1.1 + 1) (chainFun ch.1) ω =
        pathEvent Y l (ch.1.1 + 1) (chainFun ch.1) ω :=
    ae_all_iff.mpr fun ch => Sandpile.Support.pathEvent_ae_eq heq l _ _
  filter_upwards [h] with ω hω
  apply propext
  change (ω ∈ crossApprox X a b i l) ↔ (ω ∈ crossApprox Y a b i l)
  simp only [crossApprox, Set.mem_iUnion]
  exact exists_congr fun ch => iff_of_eq (hω ch)

/-- `crossApprox` is monotone under a pointwise field comparison on the rectangle:
if every field value `X u ω ≥ l` on `rectSet a b` forces `Y u ω ≥ l'`, then a
crossing witnessed by `X` at level `l` is also a crossing witnessed by `Y` at
level `l'`, using the same chain. -/
theorem Sandpile.Support.crossApprox_mono_on_rectangle {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Space 2 → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {l l' : ℝ} {ω : Ω}
    (hXY : ∀ u ∈ rectSet a b, l ≤ X u ω → l' ≤ Y u ω)
    (hX : ω ∈ crossApprox X a b i l) : ω ∈ crossApprox Y a b i l' := by
  obtain ⟨ch, hch⟩ := Set.mem_iUnion.mp hX
  apply Set.mem_iUnion.mpr
  refine ⟨ch, ?_⟩
  intro j q hj hq0 hq1
  apply hXY _ ?_ (hch j q hj hq0 hq1)
  apply ch.2.1
  apply Set.mem_biUnion (Finset.mem_range.mpr hj)
  exact ⟨(q : ℝ), ⟨by exact_mod_cast hq0, by exact_mod_cast hq1⟩, rfl⟩

/-- Membership in the scale-chain intersection `⋂ n, scaleChainEvent d W a b i n`
transfers along a uniformly bounded perturbation: if `W` and `W'` differ by at
most `C · crossScale d s` at every rational scale `s ∈ (0,1)` on the rectangle,
then it survives at every level `n`, via `crossApprox_mono_on_rectangle` applied
after enlarging the level to absorb the perturbation. -/
theorem Sandpile.Support.scaleChainIntersection_of_bounded_perturbation {Ω : Type*}
    [MeasurableSpace Ω] {d : ℕ} {W W' : (Space d → ℝ) → Ω → ℝ}
    {a b : Fin 2 → ℝ} {i : Fin 2} {ω : Ω} {C : ℝ} (hC : 0 ≤ C)
    (hshift : ∀ s : ℚ, 0 < s → (s : ℝ) < 1 → ∀ u ∈ rectSet a b,
      |ballField d W (s : ℝ) u ω - ballField d W' (s : ℝ) u ω| ≤ C * crossScale d (s : ℝ))
    (h : ω ∈ ⋂ n, scaleChainEvent d W a b i n) :
    ω ∈ ⋂ n, scaleChainEvent d W' a b i n := by
  refine Set.mem_iInter.mpr fun n => ?_
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) + C)
  have hnm : n ≤ m := by
    have : (n : ℝ) ≤ m := by linarith
    exact_mod_cast this
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp h m)
  obtain ⟨hs, hcr⟩ := Set.mem_iUnion.mp hs
  have hcut : ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
    inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcut1 : ((m : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
  refine Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨hs.1, hs.2.trans_le hcut⟩, ?_⟩⟩
  apply Sandpile.Support.crossApprox_mono_on_rectangle (ω := ω) (X := ballField d W (s:ℝ)) ?_ hcr
  intro u hu hmem
  have he := (abs_le.mp (hshift s hs.1 (hs.2.trans_le hcut1) u hu)).2
  have hp : 0 < crossScale d (s : ℝ) := crossScale_pos (by exact_mod_cast hs.1)
  nlinarith

/-- `crossApprox X a b i l` has a representative measurable in a coarser
`σ`-algebra `m`, whenever `X` itself is `m`-almost-strongly-measurable at every
point: take the `m`-measurable modification `Y u = (hX u).mk (X u)` of `X`, whose
`crossApprox` is `m`-measurable and equals the original almost everywhere by
`crossApprox_ae_eq`. -/
theorem Sandpile.Support.exists_crossApprox_representative {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (m : MeasurableSpace Ω) {X : Space 2 → Ω → ℝ}
    (hX : ∀ u, AEStronglyMeasurable[m] (X u) P)
    (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧ E =ᵐ[P] crossApprox X a b i l := by
  let Y : Space 2 → Ω → ℝ := fun u => (hX u).mk (X u)
  let E : Set Ω := @crossApprox Ω mΩ Y a b i l
  refine ⟨E, ?_, ?_⟩
  · change MeasurableSet[m] (@crossApprox Ω m Y a b i l)
    exact @measurableSet_crossApprox Ω m Y (fun u => (hX u).measurable_mk) a b i l
  · exact @Sandpile.Support.crossApprox_ae_eq Ω mΩ P Y X
      (fun u => (hX u).ae_eq_mk.symm) a b i l

/-- The scale-chain intersection `⋂ n, scaleChainEvent d W a b i n` has an
`m`-measurable representative whenever every ball field `ballField d W s` is
`m`-almost-strongly-measurable: apply `exists_crossApprox_representative` at
each rational scale and level to get a family of representatives, then take
their diagonal intersection-union, which is `m`-measurable and agrees with the
scale-chain intersection almost everywhere. -/
theorem Sandpile.Support.exists_scaleChainIntersection_representative {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    (m : MeasurableSpace Ω) {W : (Space d → ℝ) → Ω → ℝ}
    (hm : ∀ s : ℚ, 0 < s → ∀ u, AEStronglyMeasurable[m] (ballField d W (s : ℝ) u) P)
    (a b : Fin 2 → ℝ) (i : Fin 2) :
    ∃ E : Set Ω, MeasurableSet[m] E ∧ E =ᵐ[P] (⋂ n, scaleChainEvent d W a b i n) := by
  classical
  have hrep : ∀ n : ℕ, ∀ s : {s : ℚ // 0 < s},
      ∃ F : Set Ω, MeasurableSet[m] F ∧ F =ᵐ[P]
        crossApprox (ballField d W (s : ℝ)) a b i
          (((n : ℝ)+1)*crossScale d (s : ℝ)) := fun n s =>
    @Sandpile.Support.exists_crossApprox_representative Ω mΩ P m
      (ballField d W (s : ℝ)) (hm s s.2) a b i _
  choose F hFm hFe using hrep
  let E : Set Ω := ⋂ n : ℕ, ⋃ s : {s : ℚ // 0 < s},
    ⋃ _ : (s : ℝ) < ((n : ℝ)+1)⁻¹, F n s
  refine ⟨E, ?_, ?_⟩
  · letI : MeasurableSpace Ω := m
    exact MeasurableSet.iInter fun n =>
      MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ => hFm n s
  · have hall : ∀ᵐ ω ∂P, ∀ (n : ℕ) (s : {s : ℚ // 0 < s}),
        F n s ω = crossApprox (ballField d W (s : ℝ)) a b i
          (((n : ℝ)+1)*crossScale d (s : ℝ)) ω :=
      ae_all_iff.mpr fun n => ae_all_iff.mpr fun s => hFe n s
    filter_upwards [hall] with ω hω
    apply propext
    change (ω ∈ E) ↔ (ω ∈ ⋂ n, scaleChainEvent d W a b i n)
    simp only [E, Set.mem_iInter, Set.mem_iUnion, scaleChainEvent]
    apply forall_congr'
    intro n
    constructor
    · rintro ⟨s, hs, hF⟩
      exact ⟨(s : ℚ), ⟨s.2, hs⟩, (iff_of_eq (hω n s)).mp hF⟩
    · rintro ⟨s, hs, hF⟩
      exact ⟨⟨s, hs.1⟩, hs.2, (iff_of_eq (hω n ⟨s, hs.1⟩)).mpr hF⟩

/-- An event `E` with an `m n`-measurable representative for every `n`, along an
antitone family `m` of `σ`-algebras, has a representative measurable in the tail
`⨅ n, m n`: take `limsup` of the individual representatives `F n`, which lands
in every tail `σ`-algebra `m n` since dropping finitely many terms of an
antitone sequence does not change a `limsup`, and equals `E` almost everywhere
since each `F n` does. -/
theorem Sandpile.Support.exists_common_tail_representative {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m : ℕ → MeasurableSpace Ω)
    (hm : Antitone m) {E : Set Ω}
    (hE : ∀ n, ∃ F : Set Ω, MeasurableSet[m n] F ∧ F =ᵐ[P] E) :
    ∃ F : Set Ω, MeasurableSet[⨅ n, m n] F ∧ F =ᵐ[P] E := by
  classical
  choose F hFm hFe using hE
  refine ⟨Filter.limsup F Filter.atTop, ?_,
    MeasureTheory.limsup_ae_eq_of_forall_ae_eq F hFe⟩
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  rw [← Filter.limsup_nat_add F n]
  letI : MeasurableSpace Ω := m n
  exact MeasurableSet.measurableSet_limsup fun k =>
    (hm (Nat.le_add_left n k)) _ (hFm (k + n))

/-- Independence of `σ`-algebras `m₁` and `m₂` transfers to events `E` and `F`
that merely agree almost everywhere with `m₁`- and `m₂`-measurable sets `A` and
`B`: `P (E ∩ F) = P E * P F`, by rewriting each measure through the a.e.
equalities and applying independence to `A` and `B`. -/
theorem Sandpile.Support.measure_inter_eq_mul_of_ae_representatives {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m₁ m₂ : MeasurableSpace Ω)
    (hI : Indep m₁ m₂ P) {E F A B : Set Ω}
    (hA : MeasurableSet[m₁] A) (hB : MeasurableSet[m₂] B)
    (hEA : E =ᵐ[P] A) (hFB : F =ᵐ[P] B) :
    P (E ∩ F) = P E * P F := by
  rw [measure_congr (hEA.inter hFB), measure_congr hEA, measure_congr hFB]
  exact ((ProbabilityTheory.Indep_iff m₁ m₂ P).mp hI) A B hA hB

/-- **Kolmogorov's zero-one law for a cutoff-indexed tail.** For an independent
family `m` of `σ`-algebras and a cutoff function `cut : ι → ℕ`, any event
measurable in the tail `limsup m (comap cut atTop)` (equivalently, in every
`σ`-algebra generated by the indices with `cut i` large) has probability `0` or
`1`. Proved by specializing the general `measure_zero_or_one_of_measurableSet_limsup`
to the filter base of finite subsets of `ι` ordered by their image under `cut`. -/
theorem Sandpile.Support.measure_zero_or_one_of_cut_tail {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (m : ι → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (hi : iIndep m P) (cut : ι → ℕ) {E : Set Ω}
    (hE : MeasurableSet[Filter.limsup m (Filter.comap cut Filter.atTop)] E) :
    P E = 0 ∨ P E = 1 := by
  classical
  exact measure_zero_or_one_of_measurableSet_limsup hm hi
    (p := Set.Finite) (ns := fun s : Finset ι => (s : Set ι))
    (fun t ht => by
      obtain ⟨n, hn⟩ := (ht.image cut).bddAbove
      apply Filter.mem_comap.mpr
      refine ⟨Set.Ici (n + 1), Filter.Ici_mem_atTop _, ?_⟩
      intro i hi hit
      have hle := hn (Set.mem_image_of_mem cut hit)
      have hgt : n + 1 ≤ cut i := hi
      omega)
    (fun s t => ⟨s ∪ t, Finset.coe_subset.mpr (Finset.subset_union_left),
      Finset.coe_subset.mpr (Finset.subset_union_right)⟩)
    (fun s => s.finite_toSet) (fun i => ⟨{i}, by simp⟩) hE

/-- The cutoff-indexed tail `limsup m (comap cut atTop)` equals the explicit
`σ`-algebra intersection `⨅ n, ⨆ (i with n ≤ cut i), m i`: both compute the same
`limsup` along the `atTop` filter basis pulled back through `cut`. -/
theorem Sandpile.Support.cut_tail_eq_iInf {Ω ι : Type*}
    (m : ι → MeasurableSpace Ω) (cut : ι → ℕ) :
    Filter.limsup m (Filter.comap cut Filter.atTop) =
      ⨅ n : ℕ, ⨆ i : ι, ⨆ (_ : n ≤ cut i), m i := by
  simpa only [Set.mem_preimage, Set.mem_Ici, iInf_true] using
    (Filter.atTop_basis.comap cut).limsup_eq_iInf_iSup (u := m)

/-- **The zero-one law upgraded to almost-sure membership.** If an event `E` of
positive probability has, at every cutoff level `n`, a representative measurable
in the `σ`-algebra generated by the indices with `cut i ≥ n`, then `P E = 1` and
in fact `E` holds almost surely: package the representatives into one tail
representative via `exists_common_tail_representative`, identify the tail with
the `cut`-indexed one via `cut_tail_eq_iInf`, and apply
`measure_zero_or_one_of_cut_tail` to rule out `P E = 0`. -/
theorem Sandpile.Support.ae_mem_of_cut_tail_representatives {Ω ι : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ι → MeasurableSpace Ω) (hm : ∀ i, m i ≤ mΩ) (hi : iIndep m P)
    (cut : ι → ℕ) {E : Set Ω} (hE : MeasurableSet E)
    (hrep : ∀ n : ℕ, ∃ F : Set Ω,
      MeasurableSet[⨆ i, ⨆ (_ : n ≤ cut i), m i] F ∧ F =ᵐ[P] E)
    (hpos : 0 < P E) : ∀ᵐ ω ∂P, ω ∈ E := by
  let t : ℕ → MeasurableSpace Ω := fun n => ⨆ i, ⨆ (_ : n ≤ cut i), m i
  have ht : Antitone t := by
    intro n k hnk
    refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le i (le_iSup_of_le (hnk.trans hi) le_rfl)
  obtain ⟨F, hFm, hFe⟩ := Sandpile.Support.exists_common_tail_representative P t ht hrep
  have hFt : MeasurableSet[Filter.limsup m (Filter.comap cut Filter.atTop)] F := by
    rw [Sandpile.Support.cut_tail_eq_iInf m cut]
    exact hFm
  have h1 : P E = 1 := by
    rcases Sandpile.Support.measure_zero_or_one_of_cut_tail P m hm hi cut hFt with hz | ho
    · have h0 : P E = 0 := (measure_congr hFe).symm.trans hz
      exact False.elim (hpos.ne' h0)
    · exact (measure_congr hFe).symm.trans ho
  exact ae_iff.mpr ((prob_compl_eq_zero_iff hE).mpr h1)
