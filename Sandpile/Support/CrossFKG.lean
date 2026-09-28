import Sandpile.Support.CrossField

/-!
# Positive association (FKG) for crossing events

Positive association for the events the crossing argument uses
(`sandpile.tex:2104`, `sandpile.tex:2229`).

  "Finite collections are positively associated by Pitt's Gaussian FKG theorem."
  "... and the FKG inequality give a uniformly positive probability of a
   `{𝒳_1 ≥ 0}` circuit in every annulus ..."

`Sandpile.Continuum.IsAssociatedField` is the form Pitt's theorem supplies:
finitely many points of the plane, and two bounded measurable functions of those
field values, each nondecreasing in every coordinate.  The events the crossing
argument intersects are not of that form: a chain event
`Sandpile.Support.crossApprox` is a countable union of countable intersections
of the events `{ℓ ≤ 𝒳(u)}`.  This module carries the extension the docstring of
`Sandpile/Support/CrossField.lean` announces, in three layers, each closed under
the operation the next one needs:

* `UpperCylinder`: the field values at finitely many points lie in a measurable
  upper set.  Positive association for two of these is Pitt's theorem applied to
  the indicators, after putting the two point lists side by side.
* `UpperLimit`: a countable decreasing limit of upper cylinders, which is what a
  countable intersection of upper cylinders is.  Positive association passes to
  the limit by continuity from above.
* `UpperEvent`: a countable increasing limit of those, which is what a countable
  union is.  Positive association passes by continuity from below.

Nothing here approximates a general measurable increasing event: that would need
a martingale argument, and the field is not a product measure.  The three layers
are exactly the ones the chain events are built in.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

variable {Ω : Type}

/-- The field values at finitely many points lie in a measurable upper set. -/
def UpperCylinder (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (A : Set Ω) : Prop :=
  ∃ (k : ℕ) (q : Fin k → Sandpile.Continuum.Space 2) (U : Set (Fin k → ℝ)),
    MeasurableSet U ∧ IsUpperSet U ∧ A = {ω | (fun i => X (q i) ω) ∈ U}

/-- An upper cylinder is measurable: it is the preimage of the measurable upper set `U`
under the measurable map into the finitely many coordinates `X (q i)`. -/
theorem measurableSet_of_upperCylinder [MeasurableSpace Ω] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (hmeas : ∀ u, Measurable (X u)) {A : Set Ω} (hA : UpperCylinder X A) :
    MeasurableSet A := by
  obtain ⟨k, q, U, hU, _, rfl⟩ := hA
  exact (measurable_pi_lambda _ fun i => hmeas (q i)) hU

/-- A single level constraint is an upper cylinder. -/
theorem upperCylinder_le {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (l : ℝ) (u : Sandpile.Continuum.Space 2) :
    UpperCylinder X {ω | l ≤ X u ω} := by
  refine ⟨1, fun _ => u, {x : Fin 1 → ℝ | l ≤ x 0}, ?_, ?_, ?_⟩
  · exact measurableSet_le measurable_const (measurable_pi_apply 0)
  · intro x y hxy hx
    exact le_trans hx (hxy 0)
  · rfl

/-- Two upper cylinders can be written over one common list of points. -/
theorem upperCylinder_pair {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperCylinder X A) (hB : UpperCylinder X B) :
    ∃ (k : ℕ) (q : Fin k → Sandpile.Continuum.Space 2) (U V : Set (Fin k → ℝ)),
      MeasurableSet U ∧ IsUpperSet U ∧ MeasurableSet V ∧ IsUpperSet V ∧
        A = {ω | (fun i => X (q i) ω) ∈ U} ∧ B = {ω | (fun i => X (q i) ω) ∈ V} := by
  obtain ⟨k₁, q₁, U, hU, hUup, rfl⟩ := hA
  obtain ⟨k₂, q₂, V, hV, hVup, rfl⟩ := hB
  refine ⟨k₁ + k₂, Fin.append q₁ q₂,
    (fun x : Fin (k₁ + k₂) → ℝ => fun i => x (Fin.castAdd k₂ i)) ⁻¹' U,
    (fun x : Fin (k₁ + k₂) → ℝ => fun i => x (Fin.natAdd k₁ i)) ⁻¹' V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (measurable_pi_lambda _ fun i => measurable_pi_apply _) hU
  · intro x y hxy hx
    exact hUup (fun i => hxy _) hx
  · exact (measurable_pi_lambda _ fun i => measurable_pi_apply _) hV
  · intro x y hxy hx
    exact hVup (fun i => hxy _) hx
  · ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h; convert h using 1; funext i; simp [Fin.append_left]
    · intro h; convert h using 1; funext i; simp [Fin.append_left]
  · ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h; convert h using 1; funext i; simp [Fin.append_right]
    · intro h; convert h using 1; funext i; simp [Fin.append_right]

/-- Positive association for two upper cylinders over the same list of points:
Pitt's theorem applied to the two indicators, which are bounded, measurable and
nondecreasing because the sets are upper. -/
theorem fkg_cylinder_same [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X)
    (k : ℕ) (q : Fin k → Sandpile.Continuum.Space 2) (U V : Set (Fin k → ℝ))
    (hU : MeasurableSet U) (hUup : IsUpperSet U)
    (hV : MeasurableSet V) (hVup : IsUpperSet V) :
    P.real {ω | (fun i => X (q i) ω) ∈ U} * P.real {ω | (fun i => X (q i) ω) ∈ V}
      ≤ P.real {ω | (fun i => X (q i) ω) ∈ U ∩ V} := by
  classical
  have hY : Measurable (fun ω => (fun i => X (q i) ω)) :=
    measurable_pi_lambda _ fun i => hmeas (q i)
  have hmU : MeasurableSet {ω | (fun i => X (q i) ω) ∈ U} := hY hU
  have hmV : MeasurableSet {ω | (fun i => X (q i) ω) ∈ V} := hY hV
  have hmUV : MeasurableSet {ω | (fun i => X (q i) ω) ∈ U ∩ V} := hY (hU.inter hV)
  have hfmono : Monotone (U.indicator (fun _ => (1:ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hUup hxy hx)]
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have hgmono : Monotone (V.indicator (fun _ => (1:ℝ))) := by
    intro x y hxy
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hVup hxy hx)]
    · rw [Set.indicator_of_notMem hx]
      exact Set.indicator_apply_nonneg fun _ => zero_le_one
  have hfb : ∃ M : ℝ, ∀ x, |U.indicator (fun _ => (1:ℝ)) x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hgb : ∃ M : ℝ, ∀ x, |V.indicator (fun _ => (1:ℝ)) x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have key := hass k q (U.indicator (fun _ => (1:ℝ))) (V.indicator (fun _ => (1:ℝ)))
    hfmono hgmono (measurable_const.indicator hU) (measurable_const.indicator hV) hfb hgb
  have e1 : (fun ω => U.indicator (fun _ => (1:ℝ)) (fun i => X (q i) ω))
      = ({ω | (fun i => X (q i) ω) ∈ U}).indicator (1 : Ω → ℝ) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e2 : (fun ω => V.indicator (fun _ => (1:ℝ)) (fun i => X (q i) ω))
      = ({ω | (fun i => X (q i) ω) ∈ V}).indicator (1 : Ω → ℝ) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  have e3 : (fun ω => U.indicator (fun _ => (1:ℝ)) (fun i => X (q i) ω)
        * V.indicator (fun _ => (1:ℝ)) (fun i => X (q i) ω))
      = ({ω | (fun i => X (q i) ω) ∈ U ∩ V}).indicator (1 : Ω → ℝ) := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_inter_iff, Pi.one_apply]
    by_cases hx : (fun i => X (q i) ω) ∈ U <;> by_cases hy : (fun i => X (q i) ω) ∈ V <;>
      simp [hx, hy]
  rw [e1, e2, e3] at key
  rw [MeasureTheory.integral_indicator_one hmU, MeasureTheory.integral_indicator_one hmV,
    MeasureTheory.integral_indicator_one hmUV] at key
  exact key

/-- Positive association for two upper cylinders. -/
theorem fkg_upperCylinder [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {A B : Set Ω}
    (hA : UpperCylinder X A) (hB : UpperCylinder X B) :
    P.real A * P.real B ≤ P.real (A ∩ B) := by
  obtain ⟨k, q, U, V, hU, hUup, hV, hVup, rfl, rfl⟩ := upperCylinder_pair hA hB
  have hinter : {ω | (fun i => X (q i) ω) ∈ U} ∩ {ω | (fun i => X (q i) ω) ∈ V}
      = {ω | (fun i => X (q i) ω) ∈ U ∩ V} := rfl
  rw [hinter]
  exact fkg_cylinder_same hmeas hass k q U V hU hUup hV hVup

/-- Upper cylinders are closed under intersection. -/
theorem upperCylinder_inter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperCylinder X A) (hB : UpperCylinder X B) : UpperCylinder X (A ∩ B) := by
  obtain ⟨k, q, U, V, hU, hUup, hV, hVup, rfl, rfl⟩ := upperCylinder_pair hA hB
  exact ⟨k, q, U ∩ V, hU.inter hV, fun x y hxy hx => ⟨hUup hxy hx.1, hVup hxy hx.2⟩, rfl⟩

/-- Upper cylinders are closed under union. -/
theorem upperCylinder_union {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperCylinder X A) (hB : UpperCylinder X B) : UpperCylinder X (A ∪ B) := by
  obtain ⟨k, q, U, V, hU, hUup, hV, hVup, rfl, rfl⟩ := upperCylinder_pair hA hB
  refine ⟨k, q, U ∪ V, hU.union hV, ?_, rfl⟩
  rintro x y hxy (hx | hx)
  · exact Or.inl (hUup hxy hx)
  · exact Or.inr (hVup hxy hx)

/-- The whole space is an upper cylinder. -/
theorem upperCylinder_univ {X : Sandpile.Continuum.Space 2 → Ω → ℝ} :
    UpperCylinder X (Set.univ : Set Ω) :=
  ⟨0, fun i => i.elim0, Set.univ, MeasurableSet.univ, fun _ _ _ _ => trivial, rfl⟩

/-- Upper cylinders are closed under finite intersections. -/
theorem upperCylinder_biInter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (c : ℕ → Set Ω)
    (hc : ∀ n, UpperCylinder X (c n)) (n : ℕ) :
    UpperCylinder X (⋂ m ∈ Finset.range n, c m) := by
  induction n with
  | zero => simpa using upperCylinder_univ
  | succ n ih =>
    have hrw : (⋂ m ∈ Finset.range (n + 1), c m) = (⋂ m ∈ Finset.range n, c m) ∩ c n := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_range, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun m hm => h m (by omega), h n (by omega)⟩
      · rintro ⟨h1, h2⟩ m hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
        · exact h1 m h
        · exact h ▸ h2
    rw [hrw]
    exact upperCylinder_inter ih (hc n)

/-- Upper cylinders are closed under finite unions. -/
theorem upperCylinder_biUnion {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (c : ℕ → Set Ω)
    (hc : ∀ n, UpperCylinder X (c n)) (n : ℕ) :
    UpperCylinder X (⋃ m ∈ Finset.range n, c m) := by
  induction n with
  | zero =>
    have : (⋃ m ∈ Finset.range 0, c m) = (∅ : Set Ω) := by simp
    rw [this]
    exact ⟨0, fun i => i.elim0, ∅, MeasurableSet.empty, fun _ _ _ h => h.elim, rfl⟩
  | succ n ih =>
    have hrw : (⋃ m ∈ Finset.range (n + 1), c m) = (⋃ m ∈ Finset.range n, c m) ∪ c n := by
      ext ω
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨m, hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | h'
        · exact Or.inl ⟨m, h', h⟩
        · exact Or.inr (h' ▸ h)
      · rintro (⟨m, hm, h⟩ | h)
        · exact ⟨m, by omega, h⟩
        · exact ⟨n, by omega, h⟩
    rw [hrw]
    exact upperCylinder_union ih (hc n)

/-- Continuity from above, for the real-valued measure of a decreasing sequence
of measurable sets. -/
theorem tendsto_measureReal_iInter [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (C : ℕ → Set Ω) (hmC : ∀ n, MeasurableSet (C n)) (hC : Antitone C) :
    Tendsto (fun n => P.real (C n)) atTop (𝓝 (P.real (⋂ n, C n))) :=
  (ENNReal.tendsto_toReal (measure_ne_top P _)).comp
    (tendsto_measure_iInter_atTop (fun n => (hmC n).nullMeasurableSet) hC
      ⟨0, measure_ne_top P _⟩)

/-- Continuity from below, for the real-valued measure of an increasing
sequence of sets. -/
theorem tendsto_measureReal_iUnion [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (D : ℕ → Set Ω) (hD : Monotone D) :
    Tendsto (fun n => P.real (D n)) atTop (𝓝 (P.real (⋃ n, D n))) :=
  (ENNReal.tendsto_toReal (measure_ne_top P _)).comp (tendsto_measure_iUnion_atTop hD)

/-- Positive association passes to a decreasing limit in the first argument. -/
theorem fkg_pass_iInter [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : ℕ → Set Ω) (hmC : ∀ n, MeasurableSet (C n)) (hC : Antitone C)
    (B : Set Ω) (hB : MeasurableSet B)
    (h : ∀ n, P.real (C n) * P.real B ≤ P.real (C n ∩ B)) :
    P.real (⋂ n, C n) * P.real B ≤ P.real ((⋂ n, C n) ∩ B) := by
  have h1 : Tendsto (fun n => P.real (C n) * P.real B) atTop
      (𝓝 (P.real (⋂ n, C n) * P.real B)) :=
    (tendsto_measureReal_iInter C hmC hC).mul tendsto_const_nhds
  have hmono : Antitone (fun n => C n ∩ B) := fun m n hmn => Set.inter_subset_inter_left B (hC hmn)
  have heq : (⋂ n, C n ∩ B) = (⋂ n, C n) ∩ B := (Set.iInter_inter B C).symm
  have h2 : Tendsto (fun n => P.real (C n ∩ B)) atTop (𝓝 (P.real ((⋂ n, C n) ∩ B))) := by
    have := tendsto_measureReal_iInter (P := P) (fun n => C n ∩ B)
      (fun n => (hmC n).inter hB) hmono
    rwa [heq] at this
  exact le_of_tendsto_of_tendsto' h1 h2 h

/-- Positive association passes to an increasing limit in the first argument. -/
theorem fkg_pass_iUnion [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : ℕ → Set Ω) (hD : Monotone D) (B : Set Ω)
    (h : ∀ n, P.real (D n) * P.real B ≤ P.real (D n ∩ B)) :
    P.real (⋃ n, D n) * P.real B ≤ P.real ((⋃ n, D n) ∩ B) := by
  have h1 : Tendsto (fun n => P.real (D n) * P.real B) atTop
      (𝓝 (P.real (⋃ n, D n) * P.real B)) :=
    (tendsto_measureReal_iUnion D hD).mul tendsto_const_nhds
  have hmono : Monotone (fun n => D n ∩ B) := fun m n hmn => Set.inter_subset_inter_left B (hD hmn)
  have heq : (⋃ n, D n ∩ B) = (⋃ n, D n) ∩ B := (Set.iUnion_inter B D).symm
  have h2 : Tendsto (fun n => P.real (D n ∩ B)) atTop (𝓝 (P.real ((⋃ n, D n) ∩ B))) := by
    have := tendsto_measureReal_iUnion (P := P) (fun n => D n ∩ B) hmono
    rwa [heq] at this
  exact le_of_tendsto_of_tendsto' h1 h2 h

/-- A countable decreasing limit of upper cylinders. -/
def UpperLimit (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (A : Set Ω) : Prop :=
  ∃ C : ℕ → Set Ω, Antitone C ∧ (∀ n, UpperCylinder X (C n)) ∧ A = ⋂ n, C n

/-- Every upper cylinder is an upper limit, taken along the constant sequence at `A`. -/
theorem upperLimit_of_upperCylinder {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A : Set Ω}
    (hA : UpperCylinder X A) : UpperLimit X A :=
  ⟨fun _ => A, fun _ _ _ => le_refl _, fun _ => hA, (Set.iInter_const A).symm⟩

/-- An upper limit is measurable, being a countable intersection of the measurable upper
cylinders that witness it (`measurableSet_of_upperCylinder`). -/
theorem measurableSet_of_upperLimit [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u)) {A : Set Ω}
    (hA : UpperLimit X A) : MeasurableSet A := by
  obtain ⟨C, _, hC, rfl⟩ := hA
  exact MeasurableSet.iInter fun n => measurableSet_of_upperCylinder hmeas (hC n)

/-- A countable intersection of upper cylinders is a decreasing limit of upper
cylinders, namely of its partial intersections. -/
theorem upperLimit_iInter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (c : ℕ → Set Ω)
    (hc : ∀ n, UpperCylinder X (c n)) : UpperLimit X (⋂ n, c n) := by
  refine ⟨fun n => ⋂ m ∈ Finset.range n, c m, ?_, upperCylinder_biInter c hc, ?_⟩
  · intro m n hmn
    refine Set.iInter₂_mono' fun j hj => ⟨j, ?_, le_rfl⟩
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hmn)
  · apply Set.Subset.antisymm
    · intro ω h
      exact Set.mem_iInter.2 fun n => Set.mem_iInter₂.2 fun m _ => Set.mem_iInter.1 h m
    · intro ω h
      refine Set.mem_iInter.2 fun n => ?_
      exact Set.mem_iInter₂.1 (Set.mem_iInter.1 h (n + 1)) n (Finset.mem_range.2 (by omega))

/-- Decreasing limits of upper cylinders are closed under union. -/
theorem upperLimit_union {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperLimit X A) (hB : UpperLimit X B) : UpperLimit X (A ∪ B) := by
  obtain ⟨C, hCa, hCc, rfl⟩ := hA
  obtain ⟨D, hDa, hDc, rfl⟩ := hB
  refine ⟨fun n => C n ∪ D n, ?_, fun n => upperCylinder_union (hCc n) (hDc n), ?_⟩
  · intro m n hmn
    exact Set.union_subset_union (hCa hmn) (hDa hmn)
  · apply Set.Subset.antisymm
    · rintro ω (h | h)
      · exact Set.mem_iInter.2 fun n => Or.inl (Set.mem_iInter.1 h n)
      · exact Set.mem_iInter.2 fun n => Or.inr (Set.mem_iInter.1 h n)
    · intro ω h
      by_cases hc : ∀ n, ω ∈ C n
      · exact Or.inl (Set.mem_iInter.2 hc)
      · obtain ⟨n₁, hn₁⟩ := not_forall.1 hc
        refine Or.inr (Set.mem_iInter.2 fun m => ?_)
        rcases Set.mem_iInter.1 h (max n₁ m) with hcc | hdd
        · exact absurd (hCa (le_max_left n₁ m) hcc) hn₁
        · exact hDa (le_max_right n₁ m) hdd

/-- Decreasing limits of upper cylinders are closed under finite unions. -/
theorem upperLimit_biUnion {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (c : ℕ → Set Ω)
    (hc : ∀ n, UpperLimit X (c n)) (n : ℕ) :
    UpperLimit X (⋃ m ∈ Finset.range n, c m) := by
  induction n with
  | zero =>
    have hrw : (⋃ m ∈ Finset.range 0, c m) = (∅ : Set Ω) := by simp
    rw [hrw]
    exact upperLimit_of_upperCylinder
      ⟨0, fun i => i.elim0, ∅, MeasurableSet.empty, fun _ _ _ h => h.elim, rfl⟩
  | succ n ih =>
    have hrw : (⋃ m ∈ Finset.range (n + 1), c m) = (⋃ m ∈ Finset.range n, c m) ∪ c n := by
      ext ω
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨m, hm, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h' | h'
        · exact Or.inl ⟨m, h', h⟩
        · exact Or.inr (h' ▸ h)
      · rintro (⟨m, hm, h⟩ | h)
        · exact ⟨m, by omega, h⟩
        · exact ⟨n, by omega, h⟩
    rw [hrw]
    exact upperLimit_union ih (hc n)

/-- Positive association for a decreasing limit and an upper cylinder. -/
theorem fkg_upperLimit_cylinder [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {A B : Set Ω}
    (hA : UpperLimit X A) (hB : UpperCylinder X B) :
    P.real A * P.real B ≤ P.real (A ∩ B) := by
  obtain ⟨C, hCa, hCc, rfl⟩ := hA
  exact fkg_pass_iInter C (fun n => measurableSet_of_upperCylinder hmeas (hCc n)) hCa B
    (measurableSet_of_upperCylinder hmeas hB)
    (fun n => fkg_upperCylinder hmeas hass (hCc n) hB)

/-- Positive association for two decreasing limits. -/
theorem fkg_upperLimit [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {A B : Set Ω}
    (hA : UpperLimit X A) (hB : UpperLimit X B) :
    P.real A * P.real B ≤ P.real (A ∩ B) := by
  obtain ⟨D, hDa, hDc, rfl⟩ := hB
  have hstep := fkg_pass_iInter D (fun n => measurableSet_of_upperCylinder hmeas (hDc n)) hDa A
    (measurableSet_of_upperLimit hmeas hA)
    (fun n => by
      have := fkg_upperLimit_cylinder hmeas hass hA (hDc n)
      rw [mul_comm, Set.inter_comm] at this
      exact this)
  rw [mul_comm, Set.inter_comm]
  exact hstep

/-- A countable increasing limit of decreasing limits of upper cylinders; this is the
category the chain events of `Sandpile/Support/CrossUnion.lean` belong to. -/
def UpperEvent (X : Sandpile.Continuum.Space 2 → Ω → ℝ) (A : Set Ω) : Prop :=
  ∃ D : ℕ → Set Ω, Monotone D ∧ (∀ n, UpperLimit X (D n)) ∧ A = ⋃ n, D n

/-- Every upper limit is an upper event, taken along the constant sequence at `A`. -/
theorem upperEvent_of_upperLimit {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A : Set Ω}
    (hA : UpperLimit X A) : UpperEvent X A :=
  ⟨fun _ => A, fun _ _ _ => le_refl _, fun _ => hA, (Set.iUnion_const A).symm⟩

/-- An upper event is measurable, being a countable union of the measurable upper limits
that witness it (`measurableSet_of_upperLimit`). -/
theorem measurableSet_of_upperEvent [MeasurableSpace Ω]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u)) {A : Set Ω}
    (hA : UpperEvent X A) : MeasurableSet A := by
  obtain ⟨D, _, hD, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => measurableSet_of_upperLimit hmeas (hD n)

/-- A countable union of decreasing limits of upper cylinders is an increasing
limit of such, namely of its partial unions. -/
theorem upperEvent_iUnion {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (c : ℕ → Set Ω)
    (hc : ∀ n, UpperLimit X (c n)) : UpperEvent X (⋃ n, c n) := by
  refine ⟨fun n => ⋃ m ∈ Finset.range n, c m, ?_, upperLimit_biUnion c hc, ?_⟩
  · intro m n hmn
    refine Set.iUnion₂_mono' fun j hj => ⟨j, ?_, le_rfl⟩
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hmn)
  · apply Set.Subset.antisymm
    · intro ω h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
      exact Set.mem_iUnion.2 ⟨n + 1, Set.mem_biUnion (Finset.mem_range.2 (by omega)) hn⟩
    · intro ω h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
      obtain ⟨m, _, hmem⟩ := Set.mem_iUnion₂.1 hn
      exact Set.mem_iUnion.2 ⟨m, hmem⟩

/-- Positive association for an increasing limit and a decreasing limit. -/
theorem fkg_upperEvent_limit [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {A B : Set Ω}
    (hA : UpperEvent X A) (hB : UpperLimit X B) :
    P.real A * P.real B ≤ P.real (A ∩ B) := by
  obtain ⟨D, hDa, hDc, rfl⟩ := hA
  exact fkg_pass_iUnion D hDa B (fun n => fkg_upperLimit hmeas hass (hDc n) hB)

/-- **Positive association for the events the crossing argument intersects.**
Two events, each a countable union of countable intersections of the events
`{ℓ ≤ 𝒳(u)}`, correlate nonnegatively. -/
theorem fkg_upperEvent [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {A B : Set Ω}
    (hA : UpperEvent X A) (hB : UpperEvent X B) :
    P.real A * P.real B ≤ P.real (A ∩ B) := by
  obtain ⟨D, hDa, hDc, rfl⟩ := hB
  have hstep := fkg_pass_iUnion D hDa A
    (fun n => by
      have := fkg_upperEvent_limit hmeas hass hA (hDc n)
      rw [mul_comm, Set.inter_comm] at this
      exact this)
  rw [mul_comm, Set.inter_comm]
  exact hstep

/-- A countable intersection of upper cylinders, over any countable index. -/
theorem upperLimit_iInter_countable {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {ι : Sort*}
    [Countable ι] (c : ι → Set Ω) (hc : ∀ i, UpperCylinder X (c i)) :
    UpperLimit X (⋂ i, c i) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    have hrw : (⋂ i, c i) = ⋂ n : ℕ, c (e n) := by
      apply Set.Subset.antisymm
      · intro ω h
        exact Set.mem_iInter.2 fun n => Set.mem_iInter.1 h (e n)
      · intro ω h
        refine Set.mem_iInter.2 fun i => ?_
        obtain ⟨n, rfl⟩ := he i
        exact Set.mem_iInter.1 h n
    rw [hrw]
    exact upperLimit_iInter _ fun n => hc (e n)
  · have hrw : (⋂ i, c i) = (Set.univ : Set Ω) := by
      apply Set.Subset.antisymm (Set.subset_univ _)
      intro ω _
      exact Set.mem_iInter.2 fun i => absurd ⟨i⟩ hne
    rw [hrw]
    exact upperLimit_of_upperCylinder upperCylinder_univ

/-- A countable union of decreasing limits of upper cylinders, over any
countable index. -/
theorem upperEvent_iUnion_countable {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {ι : Sort*}
    [Countable ι] (c : ι → Set Ω) (hc : ∀ i, UpperLimit X (c i)) :
    UpperEvent X (⋃ i, c i) := by
  classical
  by_cases hne : Nonempty ι
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    have hrw : (⋃ i, c i) = ⋃ n : ℕ, c (e n) := by
      apply Set.Subset.antisymm
      · intro ω h
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h
        obtain ⟨n, rfl⟩ := he i
        exact Set.mem_iUnion.2 ⟨n, hi⟩
      · intro ω h
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
        exact Set.mem_iUnion.2 ⟨e n, hn⟩
    rw [hrw]
    exact upperEvent_iUnion _ fun n => hc (e n)
  · have hrw : (⋃ i, c i) = (∅ : Set Ω) := by
      apply Set.Subset.antisymm _ (Set.empty_subset _)
      intro ω h
      obtain ⟨i, _⟩ := Set.mem_iUnion.1 h
      exact absurd ⟨i⟩ hne
    rw [hrw]
    exact upperEvent_of_upperLimit (upperLimit_of_upperCylinder
      ⟨0, fun i => i.elim0, ∅, MeasurableSet.empty, fun _ _ _ h => h.elim, rfl⟩)

/-- Decreasing limits of upper cylinders are closed under intersection. -/
theorem upperLimit_inter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperLimit X A) (hB : UpperLimit X B) : UpperLimit X (A ∩ B) := by
  obtain ⟨C, hCa, hCc, rfl⟩ := hA
  obtain ⟨D, hDa, hDc, rfl⟩ := hB
  refine ⟨fun n => C n ∩ D n, fun m n hmn => Set.inter_subset_inter (hCa hmn) (hDa hmn),
    fun n => upperCylinder_inter (hCc n) (hDc n), ?_⟩
  apply Set.Subset.antisymm
  · rintro ω ⟨h1, h2⟩
    exact Set.mem_iInter.2 fun n => ⟨Set.mem_iInter.1 h1 n, Set.mem_iInter.1 h2 n⟩
  · intro ω h
    exact ⟨Set.mem_iInter.2 fun n => (Set.mem_iInter.1 h n).1,
      Set.mem_iInter.2 fun n => (Set.mem_iInter.1 h n).2⟩

/-- The class of the chain events is closed under intersection. -/
theorem upperEvent_inter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {A B : Set Ω}
    (hA : UpperEvent X A) (hB : UpperEvent X B) : UpperEvent X (A ∩ B) := by
  obtain ⟨C, hCa, hCc, rfl⟩ := hA
  obtain ⟨D, hDa, hDc, rfl⟩ := hB
  refine ⟨fun n => C n ∩ D n, fun m n hmn => Set.inter_subset_inter (hCa hmn) (hDa hmn),
    fun n => upperLimit_inter (hCc n) (hDc n), ?_⟩
  apply Set.Subset.antisymm
  · rintro ω ⟨h1, h2⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h1
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 h2
    exact Set.mem_iUnion.2 ⟨max n m, hCa (le_max_left n m) hn, hDa (le_max_right n m) hm⟩
  · intro ω h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact ⟨Set.mem_iUnion.2 ⟨n, hn.1⟩, Set.mem_iUnion.2 ⟨n, hn.2⟩⟩

/-- The class of the chain events is closed under finite intersections. -/
theorem upperEvent_biInter {X : Sandpile.Continuum.Space 2 → Ω → ℝ} {ι : Type*}
    [DecidableEq ι] (A : ι → Set Ω) (hA : ∀ i, UpperEvent X (A i)) (s : Finset ι) :
    UpperEvent X (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hrw : (⋂ i ∈ (∅ : Finset ι), A i) = (Set.univ : Set Ω) := by simp
    rw [hrw]
    exact upperEvent_of_upperLimit (upperLimit_of_upperCylinder upperCylinder_univ)
  | insert a s ha ih =>
    have hrw : (⋂ i ∈ insert a s, A i) = A a ∩ ⋂ i ∈ s, A i := by
      simp
    rw [hrw]
    exact upperEvent_inter (hA a) ih

/-- **The FKG inequality for the events the crossing argument intersects**, in
the form `sandpile.tex:2229` uses it: the probability that all of finitely many
of them occur is at least the product of their probabilities. -/
theorem fkg_prod_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {ι : Type*} [DecidableEq ι]
    (A : ι → Set Ω) (hA : ∀ i, UpperEvent X (A i)) (s : Finset ι) :
    ∏ i ∈ s, P.real (A i) ≤ P.real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hrw : (⋂ i ∈ insert a s, A i) = A a ∩ ⋂ i ∈ s, A i := by
      simp
    rw [Finset.prod_insert ha, hrw]
    calc P.real (A a) * ∏ i ∈ s, P.real (A i)
        ≤ P.real (A a) * P.real (⋂ i ∈ s, A i) := by
          exact mul_le_mul_of_nonneg_left ih measureReal_nonneg
      _ ≤ P.real (A a ∩ ⋂ i ∈ s, A i) :=
          fkg_upperEvent hmeas hass (hA a) (upperEvent_biInter A hA s)

/-- A chain event of `Sandpile/Support/CrossPath.lean` is a countable
intersection of level constraints, hence a decreasing limit of upper
cylinders. -/
theorem upperLimit_pathEvent [MeasurableSpace Ω] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (l : ℝ) (n : ℕ) (v : ℕ → Sandpile.Continuum.Space 2) :
    UpperLimit X (pathEvent X l n v) := by
  classical
  have hrw : pathEvent X l n v = ⋂ p : ℕ × ℚ, {ω | p.1 < n → 0 ≤ p.2 → p.2 ≤ 1 →
      l ≤ X (segPt (v p.1) (v (p.1 + 1)) ((p.2 : ℝ))) ω} := by
    ext ω
    simp only [pathEvent, Set.mem_setOf_eq, Set.mem_iInter, Prod.forall]
  rw [hrw]
  refine upperLimit_iInter_countable _ fun p => ?_
  by_cases h : p.1 < n ∧ 0 ≤ p.2 ∧ p.2 ≤ 1
  · have he : {ω | p.1 < n → 0 ≤ p.2 → p.2 ≤ 1 →
        l ≤ X (segPt (v p.1) (v (p.1 + 1)) ((p.2 : ℝ))) ω}
        = {ω | l ≤ X (segPt (v p.1) (v (p.1 + 1)) ((p.2 : ℝ))) ω} := by
      ext ω
      simp [h.1, h.2.1, h.2.2]
    rw [he]
    exact upperCylinder_le _ _
  · have he : {ω | p.1 < n → 0 ≤ p.2 → p.2 ≤ 1 →
        l ≤ X (segPt (v p.1) (v (p.1 + 1)) ((p.2 : ℝ))) ω} = (Set.univ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro h1 h2 h3
      exact absurd ⟨h1, h2, h3⟩ h
    rw [he]
    exact upperCylinder_univ

/-- The chain event `Sandpile.Support.crossApprox`, a countable union of chain
events, belongs to the class. -/
theorem upperEvent_crossApprox [MeasurableSpace Ω] {X : Sandpile.Continuum.Space 2 → Ω → ℝ}
    (a b : Fin 2 → ℝ) (i : Fin 2) (l : ℝ) :
    UpperEvent X (crossApprox X a b i l) :=
  upperEvent_iUnion_countable _ fun _ => upperLimit_pathEvent l _ _

/-- **The FKG inequality for the chain events of the crossing argument.**  The
probability that finitely many prescribed rectangles are all crossed, in the
chain vocabulary, is at least the product of the crossing probabilities.  This
is the form `sandpile.tex:2229` uses to build a circuit in an annulus out of
four rectangle crossings. -/
theorem fkg_crossApprox [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Sandpile.Continuum.Space 2 → Ω → ℝ} (hmeas : ∀ u, Measurable (X u))
    (hass : Sandpile.Continuum.IsAssociatedField P X) {ι : Type*} [DecidableEq ι]
    (a b : ι → Fin 2 → ℝ) (dir : ι → Fin 2) (lev : ι → ℝ) (s : Finset ι) :
    ∏ i ∈ s, P.real (crossApprox X (a i) (b i) (dir i) (lev i))
      ≤ P.real (⋂ i ∈ s, crossApprox X (a i) (b i) (dir i) (lev i)) :=
  fkg_prod_le hmeas hass _ (fun i => upperEvent_crossApprox (a i) (b i) (dir i) (lev i)) s

end Sandpile.Support
