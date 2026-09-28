import Sandpile.Support.CrossBasic

/-!
# Extracting finitely many deterministic scales

Step 2 of `lem:finite-scale-extraction` (`sandpile.tex:2470-2490`): from the almost-sure
crossings at random rational scales to finitely many deterministic scales and a deterministic
level. Applying Step 1 to `𝓡_1,…,𝓡_N` gives, almost surely, random rational scales
`s_1,…,s_N ∈ (0,1)` for which `H_{𝓡_j}(b(s_j); 𝒳_{s_j})` occurs for every `j`; if
`S = {s_1,…,s_N}` then `max_{s ∈ S} 𝒳_s ≥ 𝒳_{s_j}` on `𝓡_j`, and choosing `n` so large that
`4/n ≤ min_j b(s_j)` makes the union over `n` and finite `S` almost sure. Continuity from below
then produces finitely many pairs whose union has probability at least `1 - ε`, and taking
`n = max_i n_i`, `S = ⋃_i S_i`, and `c = 1/n` gives the claim. Here the finite sets `S` are
replaced by the prefixes of one enumeration of the rationals in `(0,1)`, which is legitimate
because any finite set of such rationals sits in a prefix and the level only has to be
lowered. The family of events is then a single increasing sequence, and continuity from below
is `Monotone.measure_iUnion`, which needs no measurability: the crossing events are compared
as outer measures throughout, as the frozen statement does.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Frozen.FixedScaleCrossings

/-- An enumeration of the rationals in `(0,1)`. -/
theorem exists_scale_enum :
    ∃ q : ℕ → ℚ, (∀ i, 0 < q i ∧ q i < 1) ∧ ∀ s : ℚ, 0 < s → s < 1 → ∃ i, q i = s := by
  have hne : (Set.Ioo (0 : ℚ) 1).Nonempty := ⟨1 / 2, by norm_num⟩
  obtain ⟨f, hf⟩ := (Set.to_countable (Set.Ioo (0 : ℚ) 1)).exists_eq_range hne
  refine ⟨f, fun i => ?_, fun s hs0 hs1 => ?_⟩
  · have hmem : f i ∈ Set.Ioo (0 : ℚ) 1 := by rw [hf]; exact Set.mem_range_self i
    exact ⟨hmem.1, hmem.2⟩
  · have hmem : s ∈ Set.range f := by rw [← hf]; exact ⟨hs0, hs1⟩
    obtain ⟨i, hi⟩ := hmem
    exact ⟨i, hi⟩

/-- A term of a finite family is below its supremum. -/
theorem le_ciSup_fin (F : ℕ → ℝ) {n : ℕ} (i : Fin n) :
    F (i : ℕ) ≤ ⨆ j : Fin n, F (j : ℕ) :=
  le_ciSup (f := fun j : Fin n => F (j : ℕ))
    (Set.Finite.bddAbove (Set.finite_range _)) i

/-- The supremum over a longer prefix is larger. -/
theorem ciSup_fin_prefix_mono (F : ℕ → ℝ) {n m : ℕ} (hn : 0 < n) (h : n ≤ m) :
    (⨆ i : Fin n, F (i : ℕ)) ≤ ⨆ i : Fin m, F (i : ℕ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ciSup_le fun i => ?_
  exact le_ciSup (f := fun j : Fin m => F (j : ℕ))
    (Set.Finite.bddAbove (Set.finite_range _))
    (⟨(i : ℕ), lt_of_lt_of_le i.isLt h⟩ : Fin m)

/-- `⌈4/x⌉ ≤ n` bounds `4/n` by `x`. -/
theorem four_div_le_of_ceil {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : ⌈4 / x⌉₊ ≤ n) :
    4 / (n : ℝ) ≤ x := by
  have h1 : (4 : ℝ) / x ≤ (⌈4 / x⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ((⌈4 / x⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : (4 : ℝ) / x ≤ (n : ℝ) := le_trans h1 h2
  have hpos : (0 : ℝ) < 4 / x := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hpos h3
  rw [div_le_iff₀ hnpos]
  rw [div_le_iff₀ hx] at h3
  nlinarith

/-- A countable directed family whose union is almost sure has a member of
probability at least any `r < 1`.  The members need not be measurable. -/
theorem exists_index_of_full {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type} [Countable ι] [Nonempty ι] (E : ι → Set Ω)
    (hd : Directed (· ⊆ ·) E) (hfull : P (⋃ i, E i) = 1) {r : ℝ≥0∞} (hr : r < 1) :
    ∃ i, r ≤ P (E i) := by
  have hsup : P (⋃ i, E i) = ⨆ i, P (E i) := hd.measure_iUnion
  rw [hfull] at hsup
  have hlt : r < ⨆ i, P (E i) := by rw [← hsup]; exact hr
  obtain ⟨i, hi⟩ := lt_iSup_iff.mp hlt
  exact ⟨i, hi.le⟩

variable {Ω : Type*}

/-- The event of `lem:finite-scale-extraction` at level `4/(n+1)` for the first
`n+1` scales of the enumeration `q`. -/
def prefixEvent {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (dir : Fin N → Fin 2)
    (Y : ℚ → Sandpile.Continuum.Space 2 → Ω → ℝ) (q : ℕ → ℚ) (n : ℕ) : Set Ω :=
  {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j)
    {u | 4 * ((n : ℝ) + 1)⁻¹ ≤ ⨆ i : Fin (n + 1), Y (q (i : ℕ)) u ω}}

/-- The prefix events increase: the level falls and the family of scales grows. -/
theorem prefixEvent_mono {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (dir : Fin N → Fin 2)
    (Y : ℚ → Sandpile.Continuum.Space 2 → Ω → ℝ) (q : ℕ → ℚ) :
    Monotone (prefixEvent a b dir Y q) := by
  intro n m hnm ω hω j
  refine crosses_mono (fun u hu => ?_) (hω j)
  have hlvl : 4 * ((m : ℝ) + 1)⁻¹ ≤ 4 * ((n : ℝ) + 1)⁻¹ := by
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnm' : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
      have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      linarith
    have := one_div_le_one_div_of_le hn0 hnm'
    simp only [one_div] at this
    linarith
  have hsup : (⨆ i : Fin (n + 1), Y (q (i : ℕ)) u ω)
      ≤ ⨆ i : Fin (m + 1), Y (q (i : ℕ)) u ω :=
    ciSup_fin_prefix_mono (fun i => Y (q i) u ω) (Nat.succ_pos n)
      (Nat.succ_le_succ hnm)
  exact le_trans hlvl (le_trans hu hsup)

/-- The almost-sure statement of Step 1, applied to all `N` rectangles at once,
fills the union of the prefix events: a finite family of rational scales sits in
a prefix, and the level `4/(n+1)` is below every `b(s_j)` once `n` is large. -/
theorem prefixEvent_union_eq_one [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (dir : Fin N → Fin 2) (Y : ℚ → Sandpile.Continuum.Space 2 → Ω → ℝ)
    (q : ℕ → ℚ) (hsurj : ∀ s : ℚ, 0 < s → s < 1 → ∃ i, q i = s)
    (bsc : ℚ → ℝ) (hbsc : ∀ s : ℚ, 0 < s → s < 1 → 0 < bsc s)
    (hAS : ∀ᵐ ω ∂P, ∀ j : Fin N, ∃ s : ℚ, 0 < s ∧ s < 1 ∧
      Crosses (a j) (b j) (dir j) {u | bsc s ≤ Y s u ω}) :
    P (⋃ n : ℕ, prefixEvent a b dir Y q n) = 1 := by
  set Q : Set Ω := {ω | ∀ j : Fin N, ∃ s : ℚ, 0 < s ∧ s < 1 ∧
    Crosses (a j) (b j) (dir j) {u | bsc s ≤ Y s u ω}} with hQdef
  have hQ : (1 : ℝ≥0∞) ≤ P Q := by
    have h1 : P Set.univ ≤ P Q + P Qᶜ := by
      refine le_trans (measure_mono ?_) (measure_union_le _ _)
      intro x _
      by_cases h : x ∈ Q
      · exact Or.inl h
      · exact Or.inr h
    rw [measure_univ] at h1
    have hnull : P Qᶜ = 0 := by
      rw [MeasureTheory.ae_iff] at hAS
      exact hAS
    simpa [hnull] using h1
  have hsub : Q ⊆ ⋃ n : ℕ, prefixEvent a b dir Y q n := by
    intro ω hω
    choose s hs0 hs1 hcr using hω
    choose ii hii using fun j => hsurj (s j) (hs0 j) (hs1 j)
    refine Set.mem_iUnion.mpr ⟨max (Finset.univ.sup fun j => ii j)
      (Finset.univ.sup fun j => ⌈4 / bsc (s j)⌉₊), ?_⟩
    set n := max (Finset.univ.sup fun j => ii j)
      (Finset.univ.sup fun j => ⌈4 / bsc (s j)⌉₊) with hndef
    intro j
    refine crosses_mono (fun u hu => ?_) (hcr j)
    have hun : bsc (s j) ≤ Y (s j) u ω := hu
    have hij : ii j ≤ n :=
      le_trans (Finset.le_sup (f := fun j => ii j) (Finset.mem_univ j)) (le_max_left _ _)
    have hce : ⌈4 / bsc (s j)⌉₊ ≤ n :=
      le_trans (Finset.le_sup (f := fun j => ⌈4 / bsc (s j)⌉₊) (Finset.mem_univ j))
        (le_max_right _ _)
    have hlev : 4 / ((n + 1 : ℕ) : ℝ) ≤ bsc (s j) :=
      four_div_le_of_ceil (hbsc (s j) (hs0 j) (hs1 j)) (le_trans hce (Nat.le_succ n))
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hlev' : 4 * ((n : ℝ) + 1)⁻¹ ≤ bsc (s j) := by
      rw [hcast] at hlev
      rwa [div_eq_mul_inv] at hlev
    have hidx : Y (q (ii j)) u ω ≤ ⨆ i : Fin (n + 1), Y (q (i : ℕ)) u ω :=
      le_ciSup_fin (fun i => Y (q i) u ω) (⟨ii j, Nat.lt_succ_of_le hij⟩ : Fin (n + 1))
    rw [hii j] at hidx
    show 4 * ((n : ℝ) + 1)⁻¹ ≤ ⨆ i : Fin (n + 1), Y (q (i : ℕ)) u ω
    exact le_trans hlev' (le_trans hun hidx)
  exact le_antisymm prob_le_one (le_trans hQ (measure_mono hsub))

/-- The conclusion of `lem:finite-scale-extraction`: a positive level `c` and a
finite list of rational scales in `(0,1)` for which all `N` rectangles are
crossed with probability at least `1 - ε`. -/
theorem exists_finite_scales [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (dir : Fin N → Fin 2) (Y : ℚ → Sandpile.Continuum.Space 2 → Ω → ℝ)
    (q : ℕ → ℚ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (hfull : P (⋃ n : ℕ, prefixEvent a b dir Y q n) = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ) (k : ℕ) (s : Fin k → ℚ), 0 < c ∧ 0 < k ∧
      (∀ i, 0 < s i ∧ s i < 1) ∧
      ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N, Crosses (a j) (b j) (dir j)
        {u | 4 * c ≤ ⨆ i : Fin k, Y (s i) u ω}} := by
  have hr : ENNReal.ofReal (1 - ε) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  obtain ⟨n, hn⟩ := exists_index_of_full P (prefixEvent a b dir Y q)
    ((prefixEvent_mono a b dir Y q).directed_le) hfull hr
  exact ⟨((n : ℝ) + 1)⁻¹, n + 1, fun i => q (i : ℕ), by positivity,
    Nat.succ_pos n, fun i => hq _, hn⟩

end Sandpile.Support
