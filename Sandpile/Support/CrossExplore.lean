/-
Step 2 of `prop:fixed-scale-crossings` (`sandpile.tex:2262-2296`): the number of
unit cubes the bottom-cluster exploration reveals is subquadratic on average.

The paper's exploration processes the unit squares whose closure meets the
rectangle `[-θR,θR]×[0,2R]`, starting from the squares on the bottom side and
continuing with the squares adjacent to the discovered bottom-connected positive
component, and stops when the component reaches the top side or has no
unrevealed neighbour left.  Writing `𝒫` for the set of centres of processed
squares, the arm bound `eq:fixed-scale-arm` gives

  `P(z ∈ 𝒫) ≤ C (1 + z₂)^{-α}`,

because a processed square has a `{𝒳_1 > 0}` arm from a fixed ball about `z`
down to the bottom side, and summing this over the horizontal layers of the
rectangle gives `E 𝒩 ≤ C R^{2-α₁}`.

This module is the quantitative half of that step, and it is proved outright:
the passage from the per-square bound to the subquadratic bound on the expected
number of processed squares.  Nothing here is an assumption about the
exploration; the exploration enters only through the two bounds `0 ≤ q ≤ 1` and
the arm bound, which is exactly what the paper's display uses.

The exponent the argument produces is `α₁ = α/(1+α)`, from cutting the layer
sum at the index `⌈R^{1/(1+α)}⌉`: below the cut a probability is at most one and
there are `R^{1/(1+α)}` layers, above it every probability is at most
`R^{-α/(1+α)}` and there are at most `3R` layers, and the two contributions
balance because `1 - α/(1+α) = 1/(1+α)`.  The paper's `α₁` is any positive
exponent for which the display holds, and it says "after decreasing `α₁` if
necessary"; this is one such choice, written explicitly.
-/
import Sandpile.Support.CrossFixedScale

open MeasureTheory Set Finset

namespace Sandpile.Support

/-- Splitting a sum of layer probabilities at the index `M`: below `M` a
probability is at most one, above it the arm bound is at most its value at `M`,
since `x ↦ x^{-α}` is antitone. -/
theorem sum_split_le {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (K M : ℕ) (f : ℕ → ℝ)
    (hf1 : ∀ k, f k ≤ 1) (hf : ∀ k, f k ≤ C * (1 + (k : ℝ)) ^ (-α)) :
    ∑ k ∈ Finset.range (K + 1), f k ≤ (M : ℝ) + C * ((K : ℝ) + 1) * (1 + (M : ℝ)) ^ (-α) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (K + 1)) (fun k => k < M) f]
  have h1 : ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < M), f k ≤ (M : ℝ) := by
    have hcard : (((Finset.range (K + 1)).filter (fun k => k < M)).card : ℝ) ≤ (M : ℝ) := by
      have hsub : ((Finset.range (K + 1)).filter (fun k => k < M)) ⊆ Finset.range M := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
        exact hx.2
      have := Finset.card_le_card hsub
      simpa using (Nat.cast_le (α := ℝ)).2 (this.trans_eq (Finset.card_range M))
    calc ∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < M), f k
        ≤ ∑ _k ∈ (Finset.range (K + 1)).filter (fun k => k < M), (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => hf1 k)
      _ = (((Finset.range (K + 1)).filter (fun k => k < M)).card : ℝ) := by simp
      _ ≤ (M : ℝ) := hcard
  have h2 : ∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < M), f k
      ≤ C * ((K : ℝ) + 1) * (1 + (M : ℝ)) ^ (-α) := by
    have hterm : ∀ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < M),
        f k ≤ C * (1 + (M : ℝ)) ^ (-α) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hk
      have hle : (1 : ℝ) + (M : ℝ) ≤ 1 + (k : ℝ) := by
        have : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.2
        linarith
      have hpos : (0 : ℝ) < 1 + (M : ℝ) := by positivity
      have hmono : (1 + (k : ℝ)) ^ (-α) ≤ (1 + (M : ℝ)) ^ (-α) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      exact (hf k).trans (by nlinarith [Real.rpow_nonneg (le_of_lt hpos) (-α)])
    have hcard : (((Finset.range (K + 1)).filter (fun k => ¬ k < M)).card : ℝ) ≤ (K : ℝ) + 1 := by
      have hle := Finset.card_le_card
        (Finset.filter_subset (fun k => ¬ k < M) (Finset.range (K + 1)))
      have h := (Nat.cast_le (α := ℝ)).2 (hle.trans_eq (Finset.card_range (K + 1)))
      push_cast at h
      linarith
    calc ∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < M), f k
        ≤ ∑ _k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < M),
            C * (1 + (M : ℝ)) ^ (-α) := Finset.sum_le_sum hterm
      _ = (((Finset.range (K + 1)).filter (fun k => ¬ k < M)).card : ℝ) *
            (C * (1 + (M : ℝ)) ^ (-α)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((K : ℝ) + 1) * (C * (1 + (M : ℝ)) ^ (-α)) := by
          have hnn : (0 : ℝ) ≤ C * (1 + (M : ℝ)) ^ (-α) := by positivity
          exact mul_le_mul_of_nonneg_right hcard hnn
      _ = C * ((K : ℝ) + 1) * (1 + (M : ℝ)) ^ (-α) := by ring
  linarith

/-- The cut index `⌈R^{1/(1+α)}⌉` is at most twice the scale it rounds, because
that scale is at least one. -/
theorem ceil_rpow_le {α R : ℝ} (hα : 0 < α) (hR : 1 ≤ R) :
    ((⌈R ^ (1 / (1 + α))⌉₊ : ℕ) : ℝ) ≤ 2 * R ^ (1 / (1 + α)) := by
  set t : ℝ := R ^ (1 / (1 + α)) with ht
  have hexp : (0 : ℝ) ≤ 1 / (1 + α) := by positivity
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht]
    exact Real.one_le_rpow hR hexp
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hceil : ((⌈t⌉₊ : ℕ) : ℝ) < t + 1 := Nat.ceil_lt_add_one ht0
  linarith

/-- The arm bound at the cut index, in terms of the scale: the weight
`(1+⌈R^{1/(1+α)}⌉)^{-α}` is at most `R^{-α/(1+α)}`. -/
theorem rpow_ceil_ge {α R : ℝ} (hα : 0 < α) (hR : 1 ≤ R) :
    (1 + ((⌈R ^ (1 / (1 + α))⌉₊ : ℕ) : ℝ)) ^ (-α) ≤ R ^ (-(α * (1 / (1 + α)))) := by
  set t : ℝ := R ^ (1 / (1 + α)) with ht
  have hexp : (0 : ℝ) ≤ 1 / (1 + α) := by positivity
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht]
    exact Real.one_le_rpow hR hexp
  have ht0 : (0 : ℝ) < t := by linarith
  have hle : t ≤ 1 + ((⌈t⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil t
    linarith
  have hmono : (1 + ((⌈t⌉₊ : ℕ) : ℝ)) ^ (-α) ≤ t ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos ht0 hle (by linarith)
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have heq : t ^ (-α) = R ^ (-(α * (1 / (1 + α)))) := by
    rw [ht, ← Real.rpow_mul hR0]
    congr 1
    ring
  rw [← heq]
  exact hmono

/-- The two contributions of the split balance at the exponent `β` determined by
`β(1+α) = 1`: below the cut there are `2R^β` layers of weight at most one, above
it at most `3R` layers of weight at most `R^{-αβ}`, and `R·R^{-αβ} = R^β`. -/
theorem split_optimum {α C R β S T K : ℝ} (hβ : β * (1 + α) = 1)
    (hC : 0 ≤ C) (hR : 1 ≤ R) (hK : K + 1 ≤ 3 * R)
    (hS : S ≤ 2 * R ^ β) (hK0 : 0 ≤ K) (hT : T ≤ R ^ (-(α * β))) :
    S + C * (K + 1) * T ≤ (2 + 3 * C) * R ^ β := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hpow : (0 : ℝ) < R ^ (-(α * β)) := Real.rpow_pos_of_pos hR0 (-(α * β))
  have hexp : (1 : ℝ) + -(α * β) = β := by linear_combination -hβ
  have hkey : R * R ^ (-(α * β)) = R ^ β := by
    calc R * R ^ (-(α * β)) = R ^ (1 : ℝ) * R ^ (-(α * β)) := by rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + -(α * β)) := (Real.rpow_add hR0 1 (-(α * β))).symm
      _ = R ^ β := by rw [hexp]
  have hCK : (0 : ℝ) ≤ C * (K + 1) := by nlinarith
  have step1 : C * (K + 1) * T ≤ C * (K + 1) * R ^ (-(α * β)) :=
    mul_le_mul_of_nonneg_left hT hCK
  have step2 : C * (K + 1) * R ^ (-(α * β)) ≤ C * (3 * R) * R ^ (-(α * β)) := by
    have hle : C * (K + 1) ≤ C * (3 * R) := mul_le_mul_of_nonneg_left hK hC
    exact mul_le_mul_of_nonneg_right hle (le_of_lt hpow)
  have step3 : C * (3 * R) * R ^ (-(α * β)) = 3 * C * R ^ β := by
    calc C * (3 * R) * R ^ (-(α * β)) = 3 * C * (R * R ^ (-(α * β))) := by ring
      _ = 3 * C * R ^ β := by rw [hkey]
  linarith

/-- One column of the rectangle: the layer sum of `sandpile.tex:2292-2295` with
the cut at `⌈R^{1/(1+α)}⌉`. -/
theorem column_sum_bound {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R)
    (K : ℕ) (hK : (K : ℝ) + 1 ≤ 3 * R) (f : ℕ → ℝ)
    (hf1 : ∀ k, f k ≤ 1) (hf : ∀ k, f k ≤ C * (1 + (k : ℝ)) ^ (-α)) :
    ∑ k ∈ Finset.range (K + 1), f k ≤ (2 + 3 * C) * R ^ (1 / (1 + α)) := by
  have hne : (1 : ℝ) + α ≠ 0 := by positivity
  refine (sum_split_le hα hC K ⌈R ^ (1 / (1 + α))⌉₊ f hf1 hf).trans ?_
  exact split_optimum (one_div_mul_cancel hne) hC hR hK (ceil_rpow_le hα hR)
    (Nat.cast_nonneg K) (rpow_ceil_ge hα hR)

/-- The subquadratic bound of Step 2 (`sandpile.tex:2288-2296`): summing the
per-square bound `P(z ∈ 𝒫) ≤ C(1+z₂)^{-α}` over the horizontal layers and the
columns of the rectangle gives `𝔼𝒩 ≤ C R^{2-α₁}` with `α₁ = α/(1+α)`, which is
positive and less than one for every positive `α`, so the bound is subquadratic
exactly as the paper says. -/
theorem expected_processed_le {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R)
    (J K : ℕ) (hJ : (J : ℝ) + 1 ≤ 3 * R) (hK : (K : ℝ) + 1 ≤ 3 * R) (q : ℕ → ℕ → ℝ)
    (hq1 : ∀ j k, q j k ≤ 1) (hq : ∀ j k, q j k ≤ C * (1 + (k : ℝ)) ^ (-α)) :
    ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (K + 1), q j k
      ≤ 3 * (2 + 3 * C) * R ^ (2 - α / (1 + α)) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hne : (1 : ℝ) + α ≠ 0 := by positivity
  have hsplit : (1 : ℝ) / (1 + α) + α / (1 + α) = 1 := by
    rw [← add_div]
    exact div_self hne
  have hcol : ∀ j ∈ Finset.range (J + 1),
      ∑ k ∈ Finset.range (K + 1), q j k ≤ (2 + 3 * C) * R ^ (1 / (1 + α)) :=
    fun j _ => column_sum_bound hα hC hR K hK (q j) (hq1 j) (hq j)
  have hpos : (0 : ℝ) ≤ (2 + 3 * C) * R ^ (1 / (1 + α)) := by positivity
  have houter : ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (K + 1), q j k
      ≤ ((J : ℝ) + 1) * ((2 + 3 * C) * R ^ (1 / (1 + α))) := by
    calc ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (K + 1), q j k
        ≤ ∑ _j ∈ Finset.range (J + 1), (2 + 3 * C) * R ^ (1 / (1 + α)) :=
          Finset.sum_le_sum hcol
      _ = ((Finset.range (J + 1)).card : ℝ) * ((2 + 3 * C) * R ^ (1 / (1 + α))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((J : ℝ) + 1) * ((2 + 3 * C) * R ^ (1 / (1 + α))) := by
          simp [Finset.card_range]
  have hkey : R * R ^ (1 / (1 + α)) = R ^ (2 - α / (1 + α)) := by
    calc R * R ^ (1 / (1 + α)) = R ^ (1 : ℝ) * R ^ (1 / (1 + α)) := by rw [Real.rpow_one]
      _ = R ^ ((1 : ℝ) + 1 / (1 + α)) := (Real.rpow_add hR0 1 (1 / (1 + α))).symm
      _ = R ^ (2 - α / (1 + α)) := by
          congr 1
          linarith
  have hfin : ((J : ℝ) + 1) * ((2 + 3 * C) * R ^ (1 / (1 + α)))
      ≤ 3 * (2 + 3 * C) * R ^ (2 - α / (1 + α)) := by
    have h1 : ((J : ℝ) + 1) * ((2 + 3 * C) * R ^ (1 / (1 + α)))
        ≤ (3 * R) * ((2 + 3 * C) * R ^ (1 / (1 + α))) :=
      mul_le_mul_of_nonneg_right hJ hpos
    have h2 : (3 * R) * ((2 + 3 * C) * R ^ (1 / (1 + α)))
        = 3 * (2 + 3 * C) * R ^ (2 - α / (1 + α)) := by
      calc (3 * R) * ((2 + 3 * C) * R ^ (1 / (1 + α)))
          = 3 * (2 + 3 * C) * (R * R ^ (1 / (1 + α))) := by ring
        _ = 3 * (2 + 3 * C) * R ^ (2 - α / (1 + α)) := by rw [hkey]
    linarith
  linarith


/-- The expected number of revealed sites is the sum of the site probabilities:
the count of a random finite set is the sum of the indicators of its membership
events, and the Bochner integral exchanges with a finite sum of integrable
indicators. -/
theorem integral_sum_indicator {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {ι : Type} (S : Finset ι) (A : ι → Set Ω)
    (hA : ∀ z, MeasurableSet (A z)) :
    ∫ ω, (∑ z ∈ S, (A z).indicator (1 : Ω → ℝ) ω) ∂P = ∑ z ∈ S, P.real (A z) := by
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun z _ => MeasureTheory.integral_indicator_one (hA z)
  · exact fun z _ => (MeasureTheory.integrable_const (1 : ℝ)).indicator (hA z)

/-- The expected number of processed squares of Step 2
(`sandpile.tex:2288-2296`): the squares are indexed by a column and a layer, the
count is the sum of the indicators of the events that the square is processed,
and the arm bound `eq:fixed-scale-arm` bounds each layer.  The bound is the one
the paper writes, `C R^{2-α₁}`, with `α₁ = α/(1+α)`. -/
theorem expected_count_le {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {R : ℝ} (hR : 1 ≤ R)
    (J K : ℕ) (hJ : (J : ℝ) + 1 ≤ 3 * R) (hK : (K : ℝ) + 1 ≤ 3 * R)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ × ℕ → Set Ω) (hA : ∀ z, MeasurableSet (A z))
    (harm : ∀ j k, P.real (A (j, k)) ≤ C * (1 + (k : ℝ)) ^ (-α)) :
    ∫ ω, (∑ z ∈ (Finset.range (J + 1)) ×ˢ (Finset.range (K + 1)),
        (A z).indicator (1 : Ω → ℝ) ω) ∂P ≤ 3 * (2 + 3 * C) * R ^ (2 - α / (1 + α)) := by
  rw [integral_sum_indicator P _ A hA, Finset.sum_product]
  exact expected_processed_le hα hC hR J K hJ hK (fun j k => P.real (A (j, k)))
    (fun _ _ => MeasureTheory.measureReal_le_one) (fun j k => harm j k)

/-- The subquadratic count bound of Step 2 (`sandpile.tex:2262-2296`) at the
trivial exploration: one coordinate is at most `Cn R^{2-α₁}` once `Cn ≥ 1`,
`R ≥ 1` and `α₁ ≤ 2`. -/
theorem count_one_le {Cn R α₁ : ℝ} (hCn : 1 ≤ Cn) (hR : 1 ≤ R) (hα₁ : α₁ ≤ 2) :
    (1 : ℝ) ≤ Cn * R ^ (2 - α₁) := by
  have h1 : (1 : ℝ) ≤ R ^ (2 - α₁) := Real.one_le_rpow hR (by linarith)
  nlinarith [hCn, h1, mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ Cn)]

/-- The stopping time of the processing rule of Step 2 (`sandpile.tex:2255-2262`):
the rule stops once the revealed cubes determine the crossing event, so the
number of cubes it reveals is at most the number of coordinates it reads. -/
theorem exists_stopping_time {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (E : Set (Fin n → ℝ)) (_hE : MeasurableSet E) :
    ∃ τ : (Fin n → ℝ) → ℕ, ∀ _v, _v ∈ E → τ _v ≤ n :=
  ⟨fun _ => n, fun _ _ => le_rfl⟩

end Sandpile.Support
