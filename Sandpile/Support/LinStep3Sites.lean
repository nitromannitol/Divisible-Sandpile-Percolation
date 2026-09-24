/-
The site bookkeeping of Step 3 of `lem:dgt4-path-survival` (`sandpile.tex:5584-5610`).

Step 2 reads the threshold event of ONE path through its last visits, indexed by TIME
(`Support/LinThreshold.lean`).  Step 3 compares the joint event of two paths with the product
of the two marginal events, and there the natural index is the SITE: the two products run over
the visited sites and agree off the shared ones.  `lastTimeOf i X x` is the last time at most
`i` at which `X` is at `x`, with the value `i` when `x` is not visited, so that every site of
the lattice carries a time at most `i`; `iInter_single_eq_image` and `iInter_joint_eq_image`
rewrite the two events as intersections over sites, the joint one carrying at a shared site the
SMALLER of the two last-visit levels, which is the paper's `1-\max\{\pi_{R,r},\pi_{R,h}\}` once
`thresholdProb_antitone` and `antitone_min_eq_max` are applied.

`abs_measureReal_inter_sub_le` is the joint threshold replacement.  Replacing the two factors
of the intersection one at a time costs the two union bounds of
`eq:dgt4-path-contact-replacement` separately, and, as in `Support/LinThresholdNull.lean`, no
measurability is needed: every step is monotonicity or subadditivity of an outer measure.
-/
import Sandpile.Support.LinStep3Product
import Sandpile.Support.LinThresholdNull

open MeasureTheory Filter Topology

namespace Sandpile

variable {α : Type*}

/-- `|\mu(S)-\mu(T)|\leq\mu(S\triangle T)` for ARBITRARY sets: both sides are outer measures
and every step is monotonicity or subadditivity. -/
theorem abs_measureReal_sub_le_symmDiff_all {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (S T : Set alpha) :
    |mu.real S - mu.real T| ≤ mu.real (symmDiff S T) := by
  have h1 : S ⊆ T ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ T
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx, h⟩))
  have h2 : T ⊆ S ∪ symmDiff S T := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl h
    · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hx, h⟩))
  have h3 : mu.real S ≤ mu.real T + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h1) (measureReal_union_le T (symmDiff S T))
  have h4 : mu.real T ≤ mu.real S + mu.real (symmDiff S T) :=
    le_trans (measureReal_mono h2) (measureReal_union_le S (symmDiff S T))
  rw [abs_le]
  constructor <;> linarith

/-- The union bound for the symmetric difference of two finite intersections, in the real
normalization. -/
theorem measureReal_symmDiff_iInter_le {alpha iota : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (s : Finset iota) (A B : iota → Set alpha) :
    mu.real (symmDiff (⋂ i ∈ s, A i) (⋂ i ∈ s, B i))
      ≤ ∑ i ∈ s, mu.real (symmDiff (A i) (B i)) :=
  le_trans (measureReal_mono (symmDiff_iInter_subset s A B) (measure_ne_top mu _))
    (measureReal_biUnion_finset_le s (fun i => symmDiff (A i) (B i)))

/-- Changing one factor of an intersection changes it inside the symmetric difference of that
factor. -/
theorem symmDiff_inter_subset_left {alpha : Type*} (A A' B : Set alpha) :
    symmDiff (A ∩ B) (A' ∩ B) ⊆ symmDiff A A' := by
  intro x hx
  rcases Set.mem_symmDiff.mp hx with ⟨⟨hA, hB⟩, hn⟩ | ⟨⟨hA', hB⟩, hn⟩
  · exact Set.mem_symmDiff.mpr (Or.inl ⟨hA, fun hA' => hn ⟨hA', hB⟩⟩)
  · exact Set.mem_symmDiff.mpr (Or.inr ⟨hA', fun hA => hn ⟨hA, hB⟩⟩)

/-- Changing the second factor of an intersection changes it inside the symmetric difference
of that factor. -/
theorem symmDiff_inter_subset_right {alpha : Type*} (A B B' : Set alpha) :
    symmDiff (A ∩ B) (A ∩ B') ⊆ symmDiff B B' := by
  intro x hx
  rcases Set.mem_symmDiff.mp hx with ⟨⟨hA, hB⟩, hn⟩ | ⟨⟨hA, hB'⟩, hn⟩
  · exact Set.mem_symmDiff.mpr (Or.inl ⟨hB, fun hB' => hn ⟨hA, hB'⟩⟩)
  · exact Set.mem_symmDiff.mpr (Or.inr ⟨hB', fun hB => hn ⟨hA, hB⟩⟩)

/-- **The joint threshold replacement.**  Replacing each factor of a product of two finite
intersections costs the two union bounds separately, and no measurability is needed. -/
theorem abs_measureReal_inter_sub_le {alpha iota : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsFiniteMeasure mu] (s t : Finset iota)
    (A A' B B' : iota → Set alpha) :
    |mu.real ((⋂ i ∈ s, A i) ∩ ⋂ i ∈ t, B i)
        - mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B' i)|
      ≤ (∑ i ∈ s, mu.real (symmDiff (A i) (A' i)))
        + ∑ i ∈ t, mu.real (symmDiff (B i) (B' i)) := by
  have h1 : |mu.real ((⋂ i ∈ s, A i) ∩ ⋂ i ∈ t, B i)
      - mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B i)|
      ≤ ∑ i ∈ s, mu.real (symmDiff (A i) (A' i)) := by
    refine le_trans (abs_measureReal_sub_le_symmDiff_all mu _ _) ?_
    refine le_trans (measureReal_mono (symmDiff_inter_subset_left _ _ _)
      (measure_ne_top mu _)) ?_
    exact measureReal_symmDiff_iInter_le mu s A A'
  have h2 : |mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B i)
      - mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B' i)|
      ≤ ∑ i ∈ t, mu.real (symmDiff (B i) (B' i)) := by
    refine le_trans (abs_measureReal_sub_le_symmDiff_all mu _ _) ?_
    refine le_trans (measureReal_mono (symmDiff_inter_subset_right _ _ _)
      (measure_ne_top mu _)) ?_
    exact measureReal_symmDiff_iInter_le mu t B B'
  have htri := abs_sub_le (mu.real ((⋂ i ∈ s, A i) ∩ ⋂ i ∈ t, B i))
    (mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B i))
    (mu.real ((⋂ i ∈ s, A' i) ∩ ⋂ i ∈ t, B' i))
  linarith

noncomputable def lastTimeOf [DecidableEq α] (i : ℕ) (X : ℕ → α) (x : α) : ℕ :=
  if h : ((Finset.range (i + 1)).filter (fun r => X r = x)).Nonempty
  then ((Finset.range (i + 1)).filter (fun r => X r = x)).max' h else i

theorem lastTimeOf_le [DecidableEq α] (i : ℕ) (X : ℕ → α) (x : α) : lastTimeOf i X x ≤ i := by
  classical
  rw [lastTimeOf]
  split_ifs with h
  · have hm := Finset.max'_mem _ h
    rw [Finset.mem_filter, Finset.mem_range] at hm
    omega
  · exact le_rfl

theorem lastTimeOf_spec [DecidableEq α] (i : ℕ) (X : ℕ → α) (r : ℕ) (hr : r ≤ i) :
    r ≤ lastTimeOf i X (X r) ∧ X (lastTimeOf i X (X r)) = X r := by
  classical
  have hmem : r ∈ (Finset.range (i + 1)).filter (fun s => X s = X r) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega : r < i + 1), rfl⟩
  have hne : ((Finset.range (i + 1)).filter (fun s => X s = X r)).Nonempty := ⟨r, hmem⟩
  rw [lastTimeOf, dif_pos hne]
  refine ⟨Finset.le_max' _ r hmem, ?_⟩
  have hm := Finset.max'_mem _ hne
  rw [Finset.mem_filter] at hm
  exact hm.2

theorem eq_lastTimeOf_image [DecidableEq α] (i : ℕ) (X : ℕ → α) (x : α)
    (hx : x ∈ (Finset.range (i + 1)).image X) : X (lastTimeOf i X x) = x := by
  classical
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  have hri : r ≤ i := by
    have := Finset.mem_range.mp hr
    omega
  exact (lastTimeOf_spec i X r hri).2

/-- The level a site carries in the joint threshold event of two paths: the smaller of the
two last-visit levels at a shared site, and the single last-visit level elsewhere. -/
noncomputable def jointLevel [DecidableEq α] (i j : ℕ) (X Y : ℕ → α) (b : ℕ → ℝ) (x : α) : ℝ :=
  if x ∈ (Finset.range (i + 1)).image X then
    (if x ∈ (Finset.range (j + 1)).image Y then
        min (b (lastTimeOf i X x)) (b (lastTimeOf j Y x))
      else b (lastTimeOf i X x))
  else b (lastTimeOf j Y x)

/-- The threshold event of one path is carried by its last visits, indexed by SITES. -/
theorem iInter_single_eq_image {β : Type*} [DecidableEq α] (i : ℕ) (X : ℕ → α)
    (b : ℕ → ℝ) (hb : Antitone b) (J : β → α → ℝ) :
    (⋂ r ∈ Finset.range (i + 1), {w : β | J w (X r) ≤ b r})
      = ⋂ x ∈ (Finset.range (i + 1)).image X,
          {w : β | J w x ≤ b (lastTimeOf i X x)} := by
  classical
  ext w
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro h x ⟨r, hr, rfl⟩
    have hri : r ≤ i := by omega
    have hspec := lastTimeOf_spec i X r hri
    have hle := h (lastTimeOf i X (X r)) (by have := lastTimeOf_le i X (X r); omega)
    rwa [hspec.2] at hle
  · intro h r hr
    have hri : r ≤ i := by omega
    have hspec := lastTimeOf_spec i X r hri
    exact le_trans (h (X r) ⟨r, hr, rfl⟩) (hb hspec.1)

/-- The joint threshold event of two paths is carried by their last visits, indexed by
SITES, with the smaller level at a shared site. -/
theorem iInter_joint_eq_image {β : Type*} [DecidableEq α] (i j : ℕ) (X Y : ℕ → α)
    (b : ℕ → ℝ) (hb : Antitone b) (J : β → α → ℝ) :
    ((⋂ r ∈ Finset.range (i + 1), {w : β | J w (X r) ≤ b r}) ∩
        ⋂ h ∈ Finset.range (j + 1), {w : β | J w (Y h) ≤ b h})
      = ⋂ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
          {w : β | J w x ≤ jointLevel i j X Y b x} := by
  classical
  ext w
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hX, hY⟩ x hx
    have hXle : x ∈ (Finset.range (i + 1)).image X → J w x ≤ b (lastTimeOf i X x) := by
      intro hxX
      have hle := hX (lastTimeOf i X x)
        (Finset.mem_range.mpr (by have := lastTimeOf_le i X x; omega))
      rwa [eq_lastTimeOf_image i X x hxX] at hle
    have hYle : x ∈ (Finset.range (j + 1)).image Y → J w x ≤ b (lastTimeOf j Y x) := by
      intro hxY
      have hle := hY (lastTimeOf j Y x)
        (Finset.mem_range.mpr (by have := lastTimeOf_le j Y x; omega))
      rwa [eq_lastTimeOf_image j Y x hxY] at hle
    rw [jointLevel]
    split_ifs with h1 h2
    · exact le_min (hXle h1) (hYle h2)
    · exact hXle h1
    · rcases Finset.mem_union.mp hx with h | h
      · exact absurd h h1
      · exact hYle h
  · intro h
    constructor
    · intro r hr
      have hri : r ≤ i := by
        have := Finset.mem_range.mp hr
        omega
      have hxX : X r ∈ (Finset.range (i + 1)).image X := Finset.mem_image_of_mem X hr
      have hspec := lastTimeOf_spec i X r hri
      have hle := h (X r) (Finset.mem_union_left _ hxX)
      have hjl : jointLevel i j X Y b (X r) ≤ b (lastTimeOf i X (X r)) := by
        rw [jointLevel, if_pos hxX]
        split_ifs with h2
        · exact min_le_left _ _
        · exact le_rfl
      exact le_trans (le_trans hle hjl) (hb hspec.1)
    · intro s hs
      have hsj : s ≤ j := by
        have := Finset.mem_range.mp hs
        omega
      have hxY : Y s ∈ (Finset.range (j + 1)).image Y := Finset.mem_image_of_mem Y hs
      have hspec := lastTimeOf_spec j Y s hsj
      have hle := h (Y s) (Finset.mem_union_right _ hxY)
      have hjl : jointLevel i j X Y b (Y s) ≤ b (lastTimeOf j Y (Y s)) := by
        rw [jointLevel]
        by_cases h1 : Y s ∈ (Finset.range (i + 1)).image X
        · rw [if_pos h1, if_pos hxY]
          exact min_le_right _ _
        · rw [if_neg h1]
      exact le_trans (le_trans hle hjl) (hb hspec.1)

/-- The threshold probability is antitone in the level. -/
theorem thresholdProb_antitone {alpha : Type*} [MeasurableSpace alpha] (mu : Measure alpha)
    [IsFiniteMeasure mu] (f : alpha → ℝ) :
    Antitone (fun t : ℝ => mu.real {z : alpha | t < f z}) := by
  intro u v huv
  exact measureReal_mono (fun z hz => lt_of_le_of_lt huv hz) (measure_ne_top _ _)

/-- An antitone function sends a minimum to a maximum, which is the paper's
`1-\max\{\pi_{R,r},\pi_{R,h}\}` at a shared site. -/
theorem antitone_min_eq_max (g : ℝ → ℝ) (hg : Antitone g) (u v : ℝ) :
    g (min u v) = max (g u) (g v) := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_left (hg h)]
  · rw [min_eq_right h, max_eq_right (hg h)]

/-- An enumeration of a finset by `Fin` of its cardinality. -/
theorem exists_finset_enum [DecidableEq α] (s : Finset α) :
    ∃ (m : ℕ) (e : Fin m → α), Function.Injective e ∧ (∀ k, e k ∈ s) ∧
      (∀ x ∈ s, ∃ k, e k = x) ∧ (m : ℝ) = (s.card : ℝ) ∧
      (∀ g : α → ℝ, ∏ k : Fin m, g (e k) = ∏ x ∈ s, g x) := by
  classical
  refine ⟨s.card, fun k => ((s.equivFin.symm k : {x // x ∈ s}) : α), ?_, ?_, ?_, rfl, ?_⟩
  · intro k k' hkk
    exact s.equivFin.symm.injective (Subtype.ext hkk)
  · intro k
    exact (s.equivFin.symm k).2
  · intro x hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩
  · intro g
    rw [Equiv.prod_comp s.equivFin.symm (fun y : {x // x ∈ s} => g (y : α)),
      Finset.prod_coe_sort s g]

end Sandpile
