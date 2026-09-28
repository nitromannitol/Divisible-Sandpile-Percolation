import Sandpile.Support.CrossExploreArm
import Sandpile.Support.CrossExplore
import Mathlib.Data.Pi.Interval

/-!
# The subquadratic count of the exploration

The count of Step 2 (`sandpile.tex:2288-2296`): the exploration reveals `C R^{2-α₁}` cells in
expectation. Every cell the rule reveals belongs to a square it has discovered, and each
square carries a bounded number of cells, so the number of revealed cells is at most a
constant times the number of discovered squares. A square discovered at distance more than
three from the starting side of the rectangle carries a positive arm to that side, so the arm
estimate bounds the probability that it is discovered by `C (1+k)^{-α}`, where `k` is its
distance from that side; summing this over the squares of the rectangle is the layer sum
already proved in `CrossExplore`.
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

namespace Sandpile.Support

attribute [local instance 0] Classical.propDecidable

/-! ### Every revealed cell belongs to a discovered square -/

variable {Ω ι : Type*}

/-- The revealed set at step `n` is contained in the revealed set at step `n + 1`: the
exploration only ever adds one further index, when there is one to add. -/
theorem exploreStep_subset_succ [DecidableEq ι] (next : Finset ι → Ω → Option ι) (n : ℕ)
    (ω : Ω) : exploreStep next n ω ⊆ exploreStep next (n + 1) ω := by
  cases hv : next (exploreStep next n ω) ω with
  | none => rw [exploreStep_succ_of_none next n ω hv]
  | some i =>
      rw [exploreStep_succ_of_some next n ω hv]
      exact Finset.subset_insert _ _

/-- The revealed set `exploreStep next n` is monotone in the step count `n`. -/
theorem exploreStep_mono [DecidableEq ι] (next : Finset ι → Ω → Option ι) {m n : ℕ}
    (h : m ≤ n) (ω : Ω) : exploreStep next m ω ⊆ exploreStep next n ω := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
      refine ih.trans ?_
      have : m + (k + 1) = (m + k) + 1 := by omega
      rw [this]
      exact exploreStep_subset_succ next (m + k) ω

/-- Once the exploration has taken as many steps as there are indices, it has stabilised: any
further steps leave the revealed set unchanged. -/
theorem exploreStep_eq_of_card_le [Fintype ι] [DecidableEq ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) (ω : Ω) (m : ℕ) :
    exploreStep next (Fintype.card ι + m) ω = exploreStep next (Fintype.card ι) ω := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have hnone : next (exploreStep next (Fintype.card ι + m) ω) ω = none := by
        rw [ih]
        exact exploreStep_stabilises h ω
      have : Fintype.card ι + (m + 1) = (Fintype.card ι + m) + 1 := by omega
      rw [this, exploreStep_succ_of_none next _ ω hnone, ih]

/-- Every step's revealed set is contained in the final revealed set `exploreSet next`, which
is `exploreStep next` at any step past `Fintype.card ι`. -/
theorem exploreStep_subset_exploreSet [Fintype ι] [DecidableEq ι] {G : ι → MeasurableSpace Ω}
    {next : Finset ι → Ω → Option ι} (h : IsExplorationRule G next) (n : ℕ) (ω : Ω) :
    exploreStep next n ω ⊆ exploreSet next ω := by
  rcases le_or_gt n (Fintype.card ι) with hn | hn
  · exact exploreStep_mono next hn ω
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hn)
    rw [exploreSet, exploreStep_eq_of_card_le h ω m]

variable {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {a b : Fin 2 → ℝ} {lev : ℝ}
  {bf : Space 2 → Ω → ℝ} {G : cellIdx d a b → MeasurableSpace Ω}

omit [MeasurableSpace Ω] in
/-- Whenever `pickIdx` selects an index `i` from `A` restricted to a set `T` of sites, that
index lies in the block `blockIdx d a b z` of some site `z ∈ T`. -/
theorem pickIdx_mem_blockIdx {A : Finset (cellIdx d a b)} {T : Finset (Sandpile.Site 2)}
    {i : cellIdx d a b} (h : pickIdx d a b A T = some i) :
    ∃ z ∈ T, i ∈ blockIdx d a b z := by
  rw [pickIdx] at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      have hi : i = h2.choose := by simpa using h.symm
      refine ⟨h1.choose, (Finset.mem_sdiff.mp h1.choose_spec).1, ?_⟩
      rw [hi]
      exact (Finset.mem_sdiff.mp h2.choose_spec).1
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [MeasurableSpace Ω] in
/-- Every cell the rule reveals belongs to a square it has discovered. -/
theorem exploreStep_subset_reach (hrule : IsExplorationRule G (exploreNext d a b lev bf))
    (n : ℕ) (ω : Ω) :
    exploreStep (exploreNext d a b lev bf) n ω ⊆
      (reachSq a b lev bf
        (doneSq d a b (exploreSet (exploreNext d a b lev bf) ω)) ω).biUnion
          (blockIdx d a b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases hv : exploreNext d a b lev bf (exploreStep (exploreNext d a b lev bf) n ω) ω with
      | none =>
          rw [exploreStep_succ_of_none _ n ω hv]
          exact ih
      | some i =>
          rw [exploreStep_succ_of_some _ n ω hv]
          refine Finset.insert_subset ?_ ih
          obtain ⟨z, hz, hi⟩ := pickIdx_mem_blockIdx hv
          refine Finset.mem_biUnion.mpr ⟨z, ?_, hi⟩
          exact reachSq_mono
            (doneSq_mono (exploreStep_subset_exploreSet hrule n ω)) hz

omit [MeasurableSpace Ω] in
/-- The final revealed set of the exploration is contained in the union of the blocks of the
squares it has discovered: `exploreStep_subset_reach` at the stabilised step. -/
theorem exploreSet_subset_reach (hrule : IsExplorationRule G (exploreNext d a b lev bf))
    (ω : Ω) :
    exploreSet (exploreNext d a b lev bf) ω ⊆
      (reachSq a b lev bf
        (doneSq d a b (exploreSet (exploreNext d a b lev bf) ω)) ω).biUnion
          (blockIdx d a b) :=
  exploreStep_subset_reach hrule _ ω

/-! ### A square carries a bounded number of cells -/

/-- The block of lattice sites `blockSites d z` has at most `5 ^ d` elements, since each of
its `d` coordinate ranges has length at most `5`. -/
theorem card_blockSites_le (d : ℕ) (z : Sandpile.Site 2) : (blockSites d z).card ≤ 5 ^ d := by
  rw [blockSites, Pi.card_Icc]
  calc ∏ i : Fin d, (Finset.Icc (blockLo d z i) (blockHi d z i)).card
      ≤ ∏ _i : Fin d, 5 := by
        refine Finset.prod_le_prod' ?_
        intro i _
        rw [Int.card_Icc, blockLo, blockHi]
        by_cases hi : (i : ℕ) < 2
        · rw [dif_pos hi, dif_pos hi]
          omega
        · rw [dif_neg hi, dif_neg hi]
          omega
    _ = 5 ^ d := by simp

omit [MeasurableSpace Ω] in
/-- The block of cell indices `blockIdx d a b z` has at most `5 ^ d` elements, by an
injection into the site block `blockSites d z`. -/
theorem card_blockIdx_le (d : ℕ) (a b : Fin 2 → ℝ) (z : Sandpile.Site 2) :
    (blockIdx d a b z).card ≤ 5 ^ d := by
  refine le_trans ?_ (card_blockSites_le d z)
  refine Finset.card_le_card_of_injOn (fun i => (i : Sandpile.Site d)) ?_ ?_
  · intro i hi
    exact mem_blockIdx.mp hi
  · intro i _ j _ hij
    exact Subtype.ext hij

/-! ### The squares the exploration discovers -/

/-- The squares the exploration has discovered when it stops. -/
noncomputable def finalReach (d : ℕ) (a b : Fin 2 → ℝ) (lev : ℝ) (bf : Space 2 → Ω → ℝ)
    (ω : Ω) : Finset (Sandpile.Site 2) :=
  reachSq a b lev bf (doneSq d a b (exploreSet (exploreNext d a b lev bf) ω)) ω

/-- Membership of a site `z` in `finalReach` is measurable: it is the countable union, over
the possible values `A` of the exploration's final revealed set, of the intersection of the
event `exploreSet = A` with the (independent) event that `z` lies in the squares `A` reaches. -/
theorem measurableSet_mem_finalReach (hGle : ∀ i, G i ≤ (inferInstance : MeasurableSpace Ω))
    (hm : BlockMeasurable d a b G bf) (hrule : IsExplorationRule G (exploreNext d a b lev bf))
    (z : Sandpile.Site 2) : MeasurableSet {ω | z ∈ finalReach d a b lev bf ω} := by
  classical
  have hrw : {ω | z ∈ finalReach d a b lev bf ω}
      = ⋃ A : Finset (cellIdx d a b),
          ({ω | exploreSet (exploreNext d a b lev bf) ω = A} ∩
            {ω | z ∈ reachSq a b lev bf (doneSq d a b A) ω}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨exploreSet (exploreNext d a b lev bf) ω, rfl, h⟩
    · rintro ⟨A, hA, hz⟩
      rw [finalReach, hA]
      exact hz
  rw [hrw]
  refine MeasurableSet.iUnion fun A => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact indepAlg_le hGle _ _ (isIndepStoppingSet_exploreSet hrule A)
  · exact indepAlg_le hGle _ _ (measurableSet_mem_reachSq hm z)

variable {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}

/-- **The probability that a square is discovered.**  A square at distance more than three from
the starting side of the rectangle is discovered only if the positive set has an arm from a
ball of radius three about it to that side. -/
theorem measure_mem_finalReach_le [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) (hcont : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω)
    (hlev : 0 < lev) {C α : ℝ}
    (harm : ∀ (x : Space 2) (r Rr : ℝ), 1 ≤ r → r ≤ Rr →
      P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r Rr}
        ≤ ENNReal.ofReal (C * (r / Rr) ^ α))
    {z : Sandpile.Site 2} (hfar : (3 : ℝ) ≤ (z 0 : ℝ) - a 0) :
    P {ω | z ∈ finalReach d a b lev (blockField d W) ω}
      ≤ ENNReal.ofReal (C * (3 / ((z 0 : ℝ) - a 0)) ^ α) := by
  refine le_trans (measure_mono_ae ?_) (harm (sqPoint z) 3 ((z 0 : ℝ) - a 0) (by norm_num) hfar)
  filter_upwards [hcont, ae_blockField_eq_on_stepPts hd hW a b] with ω hc heq hz
  exact positiveArm_of_mem_reachSq hlev hc heq hz hfar

/-! ### The expected number of revealed cells -/

omit [MeasurableSpace Ω] in
/-- The number of cells the exploration reveals is at most `5 ^ d` times the sum, over the
squares of the rectangle, of the indicator that each is discovered: each discovered square
carries at most `5 ^ d` cells. -/
theorem card_exploreSet_le (hrule : IsExplorationRule G (exploreNext d a b lev bf)) (ω : Ω) :
    ((exploreSet (exploreNext d a b lev bf) ω).card : ℝ)
      ≤ (5 : ℝ) ^ d * ∑ z ∈ rectSq a b,
          Set.indicator {ω | z ∈ finalReach d a b lev bf ω} (1 : Ω → ℝ) ω := by
  classical
  have hsub : finalReach d a b lev bf ω ⊆ rectSq a b := reachSq_subset
  have hcard : (exploreSet (exploreNext d a b lev bf) ω).card
      ≤ (finalReach d a b lev bf ω).card * 5 ^ d := by
    calc (exploreSet (exploreNext d a b lev bf) ω).card
        ≤ ((finalReach d a b lev bf ω).biUnion (blockIdx d a b)).card :=
          Finset.card_le_card (exploreSet_subset_reach hrule ω)
      _ ≤ ∑ z ∈ finalReach d a b lev bf ω, (blockIdx d a b z).card := Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ finalReach d a b lev bf ω, 5 ^ d :=
          Finset.sum_le_sum fun z _ => card_blockIdx_le d a b z
      _ = (finalReach d a b lev bf ω).card * 5 ^ d := by
          rw [Finset.sum_const, smul_eq_mul]
  have hind : ∑ z ∈ rectSq a b,
      Set.indicator {ω | z ∈ finalReach d a b lev bf ω} (1 : Ω → ℝ) ω
      = ((finalReach d a b lev bf ω).card : ℝ) := by
    have hstep : ∀ z ∈ rectSq a b,
        Set.indicator {ω | z ∈ finalReach d a b lev bf ω} (1 : Ω → ℝ) ω
          = if z ∈ finalReach d a b lev bf ω then (1 : ℝ) else 0 := by
      intro z _
      by_cases hz : z ∈ finalReach d a b lev bf ω
      · rw [Set.indicator_of_mem (by exact hz), if_pos hz]; rfl
      · rw [Set.indicator_of_notMem (by exact hz), if_neg hz]
    rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hind]
  have hcast : ((exploreSet (exploreNext d a b lev bf) ω).card : ℝ)
      ≤ ((finalReach d a b lev bf ω).card : ℝ) * (5 : ℝ) ^ d := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this
    linarith
  linarith [hcast]

/-- Taking expectations in `card_exploreSet_le`: the expected number of revealed cells is at
most `5 ^ d` times the sum, over the squares of the rectangle, of the probability that each is
discovered. -/
theorem integral_card_exploreSet_le [IsProbabilityMeasure P]
    (hGle : ∀ i, G i ≤ (inferInstance : MeasurableSpace Ω))
    (hm : BlockMeasurable d a b G bf) (hrule : IsExplorationRule G (exploreNext d a b lev bf)) :
    ∫ ω, ((exploreSet (exploreNext d a b lev bf) ω).card : ℝ) ∂P
      ≤ (5 : ℝ) ^ d * ∑ z ∈ rectSq a b, P.real {ω | z ∈ finalReach d a b lev bf ω} := by
  classical
  have hmeas : ∀ z : Sandpile.Site 2, MeasurableSet {ω | z ∈ finalReach d a b lev bf ω} :=
    fun z => measurableSet_mem_finalReach hGle hm hrule z
  have hint1 : Integrable (fun ω => ((exploreSet (exploreNext d a b lev bf) ω).card : ℝ)) P :=
    integrable_card_stoppingSet hGle (isIndepStoppingSet_exploreSet hrule)
  have hint2 : Integrable (fun ω => (5 : ℝ) ^ d * ∑ z ∈ rectSq a b,
      Set.indicator {ω | z ∈ finalReach d a b lev bf ω} (1 : Ω → ℝ) ω) P := by
    refine Integrable.const_mul ?_ _
    exact integrable_finsetSum _ fun z _ =>
      (integrable_const (1 : ℝ)).indicator (hmeas z)
  have hmono := integral_mono hint1 hint2 (fun ω => card_exploreSet_le hrule ω)
  refine le_trans hmono ?_
  rw [integral_const_mul, integral_sum_indicator P (rectSq a b) _ hmeas]

/-! ### Summing over the squares of the rectangle -/

/-- The square of the rectangle in the column `j` and at distance `k` from the starting side. -/
noncomputable def gridSite (a : Fin 2 → ℝ) (j k : ℕ) : Sandpile.Site 2 :=
  fun i => if i = 0 then ⌊a 0⌋ + (k : ℤ) else ⌊a 1⌋ + (j : ℤ)

/-- The first coordinate of `gridSite a j k` is `⌊a 0⌋ + k`. -/
theorem gridSite_zero (a : Fin 2 → ℝ) (j k : ℕ) : gridSite a j k 0 = ⌊a 0⌋ + (k : ℤ) := by
  simp [gridSite]

/-- The second coordinate of `gridSite a j k` is `⌊a 1⌋ + j`. -/
theorem gridSite_one (a : Fin 2 → ℝ) (j k : ℕ) : gridSite a j k 1 = ⌊a 1⌋ + (j : ℤ) := by
  simp [gridSite]

/-- `gridSite a` is injective in its column and row arguments `(j, k)`. -/
theorem gridSite_injOn (a : Fin 2 → ℝ) {p q : ℕ × ℕ}
    (h : gridSite a p.1 p.2 = gridSite a q.1 q.2) : p = q := by
  have h0 : gridSite a p.1 p.2 0 = gridSite a q.1 q.2 0 := by rw [h]
  have h1 : gridSite a p.1 p.2 1 = gridSite a q.1 q.2 1 := by rw [h]
  rw [gridSite_zero, gridSite_zero] at h0
  rw [gridSite_one, gridSite_one] at h1
  have e2 : p.2 = q.2 := by omega
  have e1 : p.1 = q.1 := by omega
  exact Prod.ext e1 e2

/-- Every site of the rectangle `rectSq a b` is `gridSite a j k` for some column `j` and row
`k` within the rectangle's ranges. -/
theorem rectSq_subset_grid (a b : Fin 2 → ℝ) :
    rectSq a b ⊆ ((Finset.range ((⌊b 1⌋ - ⌊a 1⌋).toNat + 1) ×ˢ
      Finset.range ((⌊b 0⌋ - ⌊a 0⌋).toNat + 1)).image (fun p : ℕ × ℕ => gridSite a p.1 p.2)) := by
  intro z hz
  rw [rectSq, Finset.mem_Icc] at hz
  obtain ⟨hlo, hhi⟩ := hz
  have hlo0 : ⌊a 0⌋ ≤ z 0 := hlo 0
  have hlo1 : ⌊a 1⌋ ≤ z 1 := hlo 1
  have hhi0 : z 0 ≤ ⌊b 0⌋ := hhi 0
  have hhi1 : z 1 ≤ ⌊b 1⌋ := hhi 1
  refine Finset.mem_image.mpr ⟨((z 1 - ⌊a 1⌋).toNat, (z 0 - ⌊a 0⌋).toNat), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  · refine funext ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [gridSite_zero]; omega
    · rw [gridSite_one]; omega

/-- A sum of nonnegative values over the rectangle's sites is bounded by the corresponding
double sum indexed by `gridSite`'s row and column, since `rectSq_subset_grid` embeds the
rectangle in the grid. -/
theorem sum_rectSq_le (a b : Fin 2 → ℝ) (f : Sandpile.Site 2 → ℝ) (hf : ∀ z, 0 ≤ f z) :
    ∑ z ∈ rectSq a b, f z
      ≤ ∑ j ∈ Finset.range ((⌊b 1⌋ - ⌊a 1⌋).toNat + 1),
          ∑ k ∈ Finset.range ((⌊b 0⌋ - ⌊a 0⌋).toNat + 1), f (gridSite a j k) := by
  classical
  have h1 : ∑ z ∈ rectSq a b, f z
      ≤ ∑ z ∈ ((Finset.range ((⌊b 1⌋ - ⌊a 1⌋).toNat + 1) ×ˢ
          Finset.range ((⌊b 0⌋ - ⌊a 0⌋).toNat + 1)).image
            (fun p : ℕ × ℕ => gridSite a p.1 p.2)), f z :=
    Finset.sum_le_sum_of_subset_of_nonneg (rectSq_subset_grid a b) fun z _ _ => hf z
  refine le_trans h1 (le_of_eq ?_)
  rw [Finset.sum_image (fun p _ q _ h => gridSite_injOn a h), Finset.sum_product]

/-- `(x / y) ^ α = x ^ α * y ^ (-α)`, for `x ≥ 0` and `y > 0`. -/
theorem rpow_div_eq {x y α : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    (x / y) ^ α = x ^ α * y ^ (-α) := by
  rw [Real.div_rpow hx hy.le, Real.rpow_neg hy.le, div_eq_mul_inv]

/-- **The layer bound of Step 2**: the probability that the square in the column `j` at
distance `k` from the starting side is discovered is at most `C (1+k)^{-α}`. -/
theorem measureReal_grid_le [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) (hcont : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω)
    (hlev : 0 < lev) {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (harm : ∀ (x : Space 2) (r Rr : ℝ), 1 ≤ r → r ≤ Rr →
      P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r Rr}
        ≤ ENNReal.ofReal (C * (r / Rr) ^ α)) (j k : ℕ) :
    P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω}
      ≤ (C * 9 ^ α + 4 ^ α) * (1 + (k : ℝ)) ^ (-α) := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkpos : (0 : ℝ) < 1 + (k : ℝ) := by linarith
  have hpow : (0 : ℝ) < (1 + (k : ℝ)) ^ (-α) := Real.rpow_pos_of_pos hkpos _
  have hfour : (0 : ℝ) < (4 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hnine : (0 : ℝ) < (9 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
  have hz0 : ((gridSite a j k 0 : ℤ) : ℝ) = ((⌊a 0⌋ : ℤ) : ℝ) + (k : ℝ) := by
    rw [gridSite_zero]; push_cast; ring
  have hfl : a 0 - 1 < ((⌊a 0⌋ : ℤ) : ℝ) := by
    have := Int.sub_one_lt_floor (a 0)
    linarith [Int.lt_floor_add_one (a 0)]
  rcases le_or_gt 4 k with hk | hk
  · -- far from the starting side: the arm estimate applies
    have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hfar : (3 : ℝ) ≤ ((gridSite a j k 0 : ℤ) : ℝ) - a 0 := by
      rw [hz0]; linarith
    have hfar' : (0 : ℝ) < ((gridSite a j k 0 : ℤ) : ℝ) - a 0 := by linarith
    have hmeas := measure_mem_finalReach_le (a := a) (b := b) hd hW hcont hlev harm hfar
    have hnn : (0 : ℝ) ≤ C * (3 / (((gridSite a j k 0 : ℤ) : ℝ) - a 0)) ^ α := by positivity
    have hreal : P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω}
        ≤ C * (3 / (((gridSite a j k 0 : ℤ) : ℝ) - a 0)) ^ α :=
      ENNReal.toReal_le_of_le_ofReal hnn hmeas
    have hratio : 3 / (((gridSite a j k 0 : ℤ) : ℝ) - a 0) ≤ 9 / (1 + (k : ℝ)) := by
      rw [div_le_div_iff₀ hfar' hkpos]
      rw [hz0]
      linarith
    have hrpow : (3 / (((gridSite a j k 0 : ℤ) : ℝ) - a 0)) ^ α ≤ (9 / (1 + (k : ℝ))) ^ α :=
      Real.rpow_le_rpow (by positivity) hratio hα.le
    have hsplit : (9 / (1 + (k : ℝ))) ^ α = (9 : ℝ) ^ α * (1 + (k : ℝ)) ^ (-α) :=
      rpow_div_eq (by norm_num) hkpos
    calc P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω}
        ≤ C * (3 / (((gridSite a j k 0 : ℤ) : ℝ) - a 0)) ^ α := hreal
      _ ≤ C * ((9 : ℝ) ^ α * (1 + (k : ℝ)) ^ (-α)) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hrpow hC.le
      _ ≤ (C * 9 ^ α + 4 ^ α) * (1 + (k : ℝ)) ^ (-α) := by nlinarith
  · -- close to the starting side: the trivial bound
    have hk3 : (k : ℝ) ≤ 3 := by
      have : k ≤ 3 := by omega
      exact_mod_cast this
    have hone : (1 : ℝ) ≤ (4 : ℝ) ^ α * (1 + (k : ℝ)) ^ (-α) := by
      have hsplit : (4 / (1 + (k : ℝ))) ^ α = (4 : ℝ) ^ α * (1 + (k : ℝ)) ^ (-α) :=
        rpow_div_eq (by norm_num) hkpos
      rw [← hsplit]
      refine Real.one_le_rpow ?_ hα.le
      rw [le_div_iff₀ hkpos]
      linarith
    have htriv : P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω} ≤ 1 :=
      measureReal_le_one
    nlinarith [mul_pos hC hnine, mul_pos (mul_pos hC hnine) hpow]

/-- **The subquadratic count of Step 2** (`sandpile.tex:2288-2296`): the exploration reveals
`C R^{2-α₁}` cells in expectation, with `α₁ = α/(1+α)` for the exponent `α` of the arm
estimate. -/
theorem expected_cells_le [IsProbabilityMeasure P] (hd : d = 2 ∨ d = 3)
    (hW : IsWhiteNoise d W P) (hcont : ∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω)
    (hlev : 0 < lev) {C α : ℝ} (hC : 0 < C) (hα : 0 < α)
    (harm : ∀ (x : Space 2) (r Rr : ℝ), 1 ≤ r → r ≤ Rr →
      P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r Rr}
        ≤ ENNReal.ofReal (C * (r / Rr) ^ α))
    {R' : ℝ} (hR' : 1 ≤ R')
    (hJ : (((⌊b 1⌋ - ⌊a 1⌋).toNat : ℕ) : ℝ) + 1 ≤ 3 * R')
    (hK : (((⌊b 0⌋ - ⌊a 0⌋).toNat : ℕ) : ℝ) + 1 ≤ 3 * R') :
    ∫ ω, ((exploreSet (exploreNext d a b lev (blockField d W)) ω).card : ℝ) ∂P
      ≤ (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α))) * R' ^ (2 - α / (1 + α)) := by
  classical
  have hbm := blockMeasurable_blockField (W := W) hd a b
  have hrule := isExplorationRule_exploreNext (lev := lev) hbm
  have hGle : ∀ i : cellIdx d a b,
      noiseBlockAlg W (cell d 1 (i : Sandpile.Site d)) ≤ (inferInstance : MeasurableSpace Ω) :=
    fun i => noiseBlockAlg_le hW _
  have hChat : (0 : ℝ) ≤ C * 9 ^ α + 4 ^ α := by positivity
  have h1 := integral_card_exploreSet_le (P := P) hGle hbm hrule
  refine le_trans h1 ?_
  have h2 : ∑ z ∈ rectSq a b, P.real {ω | z ∈ finalReach d a b lev (blockField d W) ω}
      ≤ ∑ j ∈ Finset.range ((⌊b 1⌋ - ⌊a 1⌋).toNat + 1),
          ∑ k ∈ Finset.range ((⌊b 0⌋ - ⌊a 0⌋).toNat + 1),
            P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω} :=
    sum_rectSq_le a b _ fun z => measureReal_nonneg
  have h3 := expected_processed_le (C := C * 9 ^ α + 4 ^ α) hα hChat hR'
    ((⌊b 1⌋ - ⌊a 1⌋).toNat) ((⌊b 0⌋ - ⌊a 0⌋).toNat) hJ hK
    (fun j k => P.real {ω | gridSite a j k ∈ finalReach d a b lev (blockField d W) ω})
    (fun j k => measureReal_le_one)
    (fun j k => measureReal_grid_le (a := a) (b := b) hd hW hcont hlev hC hα harm j k)
  have hpow : (0 : ℝ) ≤ (5 : ℝ) ^ d := by positivity
  calc (5 : ℝ) ^ d * ∑ z ∈ rectSq a b,
        P.real {ω | z ∈ finalReach d a b lev (blockField d W) ω}
      ≤ (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α)) * R' ^ (2 - α / (1 + α))) := by
        exact mul_le_mul_of_nonneg_left (le_trans h2 h3) hpow
    _ = (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α))) * R' ^ (2 - α / (1 + α)) := by ring

end Sandpile.Support
