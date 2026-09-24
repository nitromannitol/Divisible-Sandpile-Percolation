/-
The threshold replacement of Step 2 of `lem:dgt4-path-survival`
(`eq:dgt4-path-contact-replacement`, `sandpile.tex:5533-5548`) and the reindexing of a
product over visited sites as a product over last-visit times.

The paper bounds the probability that at least one of the contact events
`{u_{n_R-r}(X_r)=0}` differs from its threshold event by the union bound over the
symmetric differences, and then replaces the intersection over times `0 ≤ r ≤ j` by the
intersection over the sites `x` the path visits, each with the threshold belonging to its
LAST visit, since `E u_m(0)` increases in `m`.  Two ingredients are separated here:

* `measure_symmDiff_iInter_le`, the union bound for the symmetric difference of two finite
  intersections, which is what turns the per-time bound of
  `eq:dgt4-uniform-contact-thresholds` into a bound for the whole path;
* `lastVisit_injOn`, `lastVisit_image_eq` and `prod_lastVisit_eq`, which say that
  `r ↦ X_r` is a bijection from the last-visit times up to `j` onto the visited sites, so
  that `∏_{x∈Λ} g(x) = ∏_{r ∈ L} g(X_r)`, the identification behind
  `eq:dgt4-path-product-limit`.
-/
import Sandpile.Support.LinProduct

open MeasureTheory

namespace Sandpile

/-- The symmetric difference of two finite intersections is contained in the union of the
symmetric differences. -/
theorem symmDiff_iInter_subset {α ι : Type*} (s : Finset ι) (A B : ι → Set α) :
    symmDiff (⋂ i ∈ s, A i) (⋂ i ∈ s, B i) ⊆ ⋃ i ∈ s, symmDiff (A i) (B i) := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_iInter, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · push Not at hB
    obtain ⟨i, hi, hxB⟩ := hB
    exact ⟨i, hi, Or.inl ⟨hA i hi, hxB⟩⟩
  · push Not at hA
    obtain ⟨i, hi, hxA⟩ := hA
    exact ⟨i, hi, Or.inr ⟨hB i hi, hxA⟩⟩

/-- **The union bound of the threshold replacement**, `eq:dgt4-path-contact-replacement`. -/
theorem measure_symmDiff_iInter_le {α ι : Type*} [MeasurableSpace α] (mu : Measure α)
    (s : Finset ι) (A B : ι → Set α) :
    mu (symmDiff (⋂ i ∈ s, A i) (⋂ i ∈ s, B i))
      ≤ ∑ i ∈ s, mu (symmDiff (A i) (B i)) :=
  le_trans (measure_mono (symmDiff_iInter_subset s A B)) (measure_biUnion_finset_le s _)

/-- The last-visit times of a path up to time `j`. -/
def lastVisitTimes {α : Type*} [DecidableEq α] (j : ℕ) (X : ℕ → α) : Finset ℕ :=
  (Finset.range (j + 1)).filter (fun r => ∀ s ∈ Finset.Ioc r j, X s ≠ X r)

/-- Distinct last-visit times sit at distinct sites. -/
theorem lastVisit_injOn {α : Type*} [DecidableEq α] (j : ℕ) (X : ℕ → α) :
    ∀ r ∈ lastVisitTimes j X, ∀ r' ∈ lastVisitTimes j X, X r = X r' → r = r' := by
  intro r hr r' hr' hXX
  rw [lastVisitTimes, Finset.mem_filter, Finset.mem_range] at hr hr'
  obtain ⟨hrlt, hrP⟩ := hr
  obtain ⟨hr'lt, hr'P⟩ := hr'
  rcases lt_trichotomy r r' with h | h | h
  · exact absurd hXX.symm (hrP r' (Finset.mem_Ioc.mpr ⟨h, by omega⟩))
  · exact h
  · exact absurd hXX (hr'P r (Finset.mem_Ioc.mpr ⟨h, by omega⟩))

/-- Every site visited up to time `j` is visited at exactly one last-visit time. -/
theorem lastVisit_image_eq {α : Type*} [DecidableEq α] (j : ℕ) (X : ℕ → α) :
    (lastVisitTimes j X).image X = (Finset.range (j + 1)).image X := by
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (Finset.filter_subset _ _)
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, hr, hxr⟩ := hx
    have hne : ((Finset.range (j + 1)).filter (fun s => X s = x)).Nonempty :=
      ⟨r, Finset.mem_filter.mpr ⟨hr, hxr⟩⟩
    have hmS := Finset.max'_mem _ hne
    rw [Finset.mem_filter, Finset.mem_range] at hmS
    refine Finset.mem_image.mpr ⟨_, ?_, hmS.2⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmS.1, ?_⟩
    intro s hs hXs
    rw [Finset.mem_Ioc] at hs
    have hsS : s ∈ (Finset.range (j + 1)).filter (fun s => X s = x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rw [hXs, hmS.2]⟩
    have hle := Finset.le_max' _ s hsS
    omega

/-- **The product over visited sites is the product over last-visit times.**  This is the
identification that turns the factorized approximation
`∏_{x∈Λ} P(J(0) ≤ b_x)` of Step 1 into the form `∏_{r≤j}(1-π_{R,r})^{I_{r,j}(X)}` of
`eq:dgt4-path-product-limit`. -/
theorem prod_lastVisit_eq {α M : Type*} [DecidableEq α] [CommMonoid M] (j : ℕ) (X : ℕ → α)
    (g : α → M) :
    ∏ x ∈ (Finset.range (j + 1)).image X, g x = ∏ r ∈ lastVisitTimes j X, g (X r) := by
  rw [← lastVisit_image_eq j X, Finset.prod_image (lastVisit_injOn j X)]

/-- **Two events differ in probability by at most the measure of their symmetric
difference.**  With `measure_symmDiff_iInter_le` this is the whole of
`eq:dgt4-path-contact-replacement`: the survival probability along a path differs from the
probability that all the threshold events hold by at most the sum over the times of the
one-site symmetric-difference probabilities. -/
theorem abs_measureReal_sub_le_symmDiff {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (A B : Set alpha)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    |mu.real A - mu.real B| ≤ mu.real (symmDiff A B) := by
  have hA' : mu.real (A ∩ B) + mu.real (A \ B) = mu.real A :=
    MeasureTheory.measureReal_inter_add_sdiff hB
  have hB' : mu.real (B ∩ A) + mu.real (B \ A) = mu.real B :=
    MeasureTheory.measureReal_inter_add_sdiff hA
  have hsym : mu.real (symmDiff A B) = mu.real (A \ B) + mu.real (B \ A) := by
    rw [Set.symmDiff_def]
    exact MeasureTheory.measureReal_union disjoint_sdiff_sdiff (hB.diff hA)
  have h1 : (0:ℝ) ≤ mu.real (A \ B) := MeasureTheory.measureReal_nonneg
  have h2 : (0:ℝ) ≤ mu.real (B \ A) := MeasureTheory.measureReal_nonneg
  rw [Set.inter_comm B A] at hB'
  rw [hsym, abs_le]
  constructor <;> linarith

/-- Every time `r ≤ j` is dominated by the last visit to its own site, which is at least
`r`. -/
theorem exists_lastVisit_ge {α : Type*} [DecidableEq α] {j r : ℕ} (hr : r ≤ j)
    (X : ℕ → α) : ∃ m ∈ lastVisitTimes j X, r ≤ m ∧ X m = X r := by
  have hmem : X r ∈ (lastVisitTimes j X).image X := by
    rw [lastVisit_image_eq j X]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩
  obtain ⟨m, hm, hXm⟩ := Finset.mem_image.mp hmem
  refine ⟨m, hm, ?_, hXm⟩
  by_contra hlt
  push Not at hlt
  have hmP := (Finset.mem_filter.mp hm).2
  exact hmP r (Finset.mem_Ioc.mpr ⟨hlt, hr⟩) hXm.symm

/-- **The threshold intersection is carried by the last visits.**  When the levels are
antitone in time, the constraint at a site imposed by all of its visits is the constraint
imposed by its LAST visit.  This is the paper's "monotonicity of `E u_m(0)`" step at
`sandpile.tex:5545-5547`, since `b_r = E u_{n-r-1}(0)` decreases in `r`. -/
theorem iInter_lastVisit_eq {α β : Type*} [DecidableEq α] (j : ℕ) (X : ℕ → α)
    (b : ℕ → ℝ) (hb : Antitone b) (J : β → α → ℝ) :
    (⋂ r ∈ Finset.range (j + 1), {w : β | J w (X r) ≤ b r})
      = ⋂ r ∈ lastVisitTimes j X, {w : β | J w (X r) ≤ b r} := by
  apply Set.Subset.antisymm
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hw ⊢
    intro r hr
    exact hw r (Finset.mem_filter.mp hr).1
  · intro w hw
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hw ⊢
    intro r hr
    have hrj : r ≤ j := by
      have := Finset.mem_range.mp hr
      omega
    obtain ⟨m, hm, hrm, hXm⟩ := exists_lastVisit_ge hrj X
    have hle := hw m hm
    rw [hXm] at hle
    exact le_trans hle (hb hrm)

/-- **The threshold replacement, `eq:dgt4-path-contact-replacement`.**  The probability
that the contact events hold at every time `r ∈ s` differs from the probability that the
threshold events hold at every such time by at most the sum over `r ∈ s` of the
probabilities of the one-time symmetric differences. -/
theorem abs_measureReal_iInter_sub_le {alpha iota : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (s : Finset iota) (A B : iota → Set alpha)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i)) :
    |mu.real (⋂ i ∈ s, A i) - mu.real (⋂ i ∈ s, B i)|
      ≤ ∑ i ∈ s, mu.real (symmDiff (A i) (B i)) := by
  have hAm : MeasurableSet (⋂ i ∈ s, A i) :=
    MeasurableSet.biInter s.countable_toSet fun i _ => hA i
  have hBm : MeasurableSet (⋂ i ∈ s, B i) :=
    MeasurableSet.biInter s.countable_toSet fun i _ => hB i
  refine le_trans (abs_measureReal_sub_le_symmDiff mu _ _ hAm hBm) ?_
  have hle := measure_symmDiff_iInter_le mu s A B
  have hfin : (∑ i ∈ s, mu (symmDiff (A i) (B i))) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top mu _).ne
  have hmono := ENNReal.toReal_mono hfin hle
  rw [MeasureTheory.measureReal_def]
  refine le_trans hmono ?_
  rw [ENNReal.toReal_sum fun i _ => (measure_lt_top mu _).ne]
  rfl

/-- The event "the property holds at every time up to `j`" is the finite intersection over
`Finset.range (j+1)`, which is the form the two lemmas above consume. -/
theorem setOf_forall_le_eq_iInter {alpha : Type*} (j : ℕ) (P : ℕ → alpha → Prop) :
    {w : alpha | ∀ r ≤ j, P r w} = ⋂ r ∈ Finset.range (j + 1), {w : alpha | P r w} := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
  constructor
  · intro h r hr
    exact h r (by omega)
  · intro h r hr
    exact h r (by omega)

end Sandpile
