import Sandpile.Support.PositiveJet
import Sandpile.Support.RectangleBottleneck

/-!
# Positive derivative envelopes for bottleneck and rectangle crossings

Stable positive derivative envelopes for bounded-walk bottlenecks and rectangle crossings, at
logarithmic depth and with a uniform approximation error. `smoothBoundedBottleneck_positiveJet`
upgrades the coarse `SmoothBottleneckBound` of `smoothBoundedBottleneck_bound` to the finer,
`PositiveJet`-valued envelopes of this file, by the same midpoint induction on the recursion depth.
`rectangle_positive_bottleneck_at_depth` and `exists_positive_rectangle_bottleneck` then specialize
this to a lattice rectangle's crossing value, giving a smooth approximation with `HasPositiveJet`
envelopes at depth and approximation error logarithmic in the rectangle's cardinality, matching
`rectangle_smooth_bottleneck_at_depth` and `exists_smooth_rectangle_bottleneck` of
`RectangleBottleneck.lean`.
-/

open LatticeProb

open scoped BigOperators

namespace Sandpile

section FiniteGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- **`PositiveJet` envelopes for the smoothed bounded-walk bottleneck.** The smoothed bottleneck
`smoothBoundedBottleneck G β n a b h` has a `HasPositiveJet β (2n+1)` structure, by the same
midpoint induction as `smoothBoundedBottleneck_bound`: the base case is a soft-minimum pair of
coordinate jets, and the inductive step composes a soft-maximum over the midpoints of soft-minimum
pairs of jets at depth `n`. -/
lemma smoothBoundedBottleneck_positiveJet [DecidableEq V] {β : ℝ} (hβ : β ≠ 0) :
    ∀ (n : ℕ) (a b : V) (h : BoundedReach G n a b),
      HasPositiveJet β (2 * n + 1) (smoothBoundedBottleneck G β n a b h) := by
  intro n
  induction n with
  | zero =>
    intro a b h
    exact HasPositiveJet.softMinimum_pair hβ
      (hasPositiveJet_coordinate β a) (hasPositiveJet_coordinate β b)
  | succ n ih =>
    intro a b h
    letI : Nonempty (walkMidpoints G n a b) := by
      obtain ⟨c, hc⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨c, hc⟩⟩
    have hm (c : walkMidpoints G n a b) := HasPositiveJet.softMinimum_pair hβ
      (ih a c ((mem_walkMidpoints G n a b c).mp c.property).1)
      (ih c b ((mem_walkMidpoints G n a b c).mp c.property).2)
    have hh := HasPositiveJet.softMaximum hβ hm
    convert hh using 1 <;> congr 1

end FiniteGraph

/-- **A `HasPositiveJet` approximation to a rectangle's crossing value at walk depth `n`.** For a
lattice rectangle `Q` with `Q.card ≤ 2 ^ n`, the softmax `L` of the smoothed bottleneck over every
pair of left/right boundary points has `HasPositiveJet β (2n+2) L` and approximates
`crossingValue Q` to within an error logarithmic in `Q.card` and `n`, by combining
`smoothBoundedBottleneck_positiveJet` with `crossingValue_eq_bounded_max` and the error bound
`abs_softMaximum_sub_finiteMaximum`. -/
lemma rectangle_positive_bottleneck_at_depth {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) {n : ℕ} (hn : Q.card ≤ 2 ^ n) {β : ℝ} (hβ : 0 < β) :
    ∃ L : (Q → ℝ) → ℝ, HasPositiveJet β (2 * n + 2) L ∧
      ∀ F, |L F - crossingValue Q F| ≤
        ((n + 1 : ℝ) * (Real.log Q.card + Real.log 2) + 2 * Real.log Q.card) / β := by
  classical
  obtain ⟨hleft, hright⟩ := rectangle_boundaries_nonempty hQ hN
  letI : Nonempty (rectangleLeft Q) := ⟨⟨hleft.choose, hleft.choose_spec⟩⟩
  letI : Nonempty (rectangleRight Q) := ⟨⟨hright.choose, hright.choose_spec⟩⟩
  let P := rectangleLeft Q × rectangleRight Q
  let f (p : P) := smoothBoundedBottleneck (rectangleGraph Q) β n p.1 p.2
    (rectangle_boundedReach hQ hn p.1 p.2)
  let L (F : Q → ℝ) := softMaximum β (fun p : P => f p F)
  have hf (p : P) : HasPositiveJet β (2 * n + 1) (f p) :=
    smoothBoundedBottleneck_positiveJet (rectangleGraph Q) hβ.ne' n p.1 p.2 _
  refine ⟨L, ?_, ?_⟩
  · convert HasPositiveJet.softMaximum hβ.ne' hf using 1
  · intro F
    let g (p : P) := boundedBottleneckValue (rectangleGraph Q) n p.1 p.2
      (rectangle_boundedReach hQ hn p.1 p.2) F
    have he : crossingValue Q F = finiteMaximum g := crossingValue_eq_bounded_max hQ hn F
    have herr (p : P) : |f p F - g p| ≤
        (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) / β := by
      simpa only [Fintype.card_coe] using
        smoothBoundedBottleneck_error (rectangleGraph Q) hβ n p.1 p.2
          (rectangle_boundedReach hQ hn p.1 p.2) F
    have hcL : Fintype.card (rectangleLeft Q) ≤ Q.card := by
      simpa only [Fintype.card_coe] using (rectangleLeft Q).card_le_univ
    have hcR : Fintype.card (rectangleRight Q) ≤ Q.card := by
      simpa only [Fintype.card_coe] using (rectangleRight Q).card_le_univ
    have hcP : Fintype.card P ≤ Q.card ^ 2 := by
      simpa only [P, Fintype.card_prod, pow_two] using Nat.mul_le_mul hcL hcR
    have hlog : Real.log (Fintype.card P) ≤ 2 * Real.log Q.card := by
      have hh := Real.log_le_log (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card P)
        (by exact_mod_cast hcP : (Fintype.card P : ℝ) ≤ (Q.card : ℝ) ^ 2)
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    rw [he]
    apply (abs_softMaximum_sub_finiteMaximum hβ (fun p => f p F) g herr).trans
    calc
      _ ≤ (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) / β + 2 * Real.log Q.card / β :=
        add_le_add le_rfl (div_le_div_of_nonneg_right hlog hβ.le)
      _ = _ := by ring

/-- **A universal `HasPositiveJet` approximation to any rectangle's crossing value.** There is a
single constant `C` such that for every lattice rectangle `Q` with at least two sites and every
`β ≥ 1`, some `L` with `HasPositiveJet β n L` at logarithmic depth `n ≤ C log(Q.card)` approximates
`crossingValue Q` to within `C (log Q.card)² / β`: obtained from
`rectangle_positive_bottleneck_at_depth` at the logarithmic depth furnished by
`exists_logarithmic_walk_depth`. -/
lemma exists_positive_rectangle_bottleneck :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card →
        ∀ β : ℝ, 1 ≤ β → ∃ n : ℕ, ∃ L : (Q → ℝ) → ℝ,
          (n : ℝ) ≤ C * Real.log Q.card ∧ HasPositiveJet β n L ∧
          ∀ F : Q → ℝ, |L F - crossingValue Q F| ≤ C * (Real.log Q.card) ^ 2 / β := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := 8 / Real.log 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 6 / Real.log 2 ≤ C := by
    have h := div_le_div_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8) hlog2.le
    dsimp only [C]
    linarith
  have hE : 8 / Real.log 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Q hQ hN β hβ
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hlogN : Real.log 2 ≤ Real.log Q.card :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hq : 0 < Real.log Q.card := hlog2.trans_le hlogN
  obtain ⟨n, hn, hnlog⟩ := exists_logarithmic_walk_depth hN
  obtain ⟨L, hL, he⟩ := rectangle_positive_bottleneck_at_depth hQ
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hN)) hn hβpos
  refine ⟨2 * n + 2, L, ?_, hL, ?_⟩
  · calc
      ((2 * n + 2 : ℕ) : ℝ) ≤ (6 / Real.log 2) * Real.log Q.card := by
        push_cast
        calc
          _ ≤ 2 * ((3 / Real.log 2) * Real.log Q.card) := by nlinarith [hnlog]
          _ = _ := by ring
      _ ≤ C * Real.log Q.card := mul_le_mul_of_nonneg_right hD hq.le
  · intro F
    apply (he F).trans
    apply div_le_div_of_nonneg_right _ hβpos.le
    have hp : (n + 1 : ℝ) * (Real.log Q.card + Real.log 2) ≤
        (3 / Real.log 2) * Real.log Q.card * (2 * Real.log Q.card) :=
      mul_le_mul hnlog (by linarith) (by positivity) (by positivity)
    have hlin : 2 * Real.log Q.card ≤ (2 / Real.log 2) * (Real.log Q.card) ^ 2 := by
      apply (mul_le_mul_iff_right₀ hlog2).mp
      field_simp
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hlogN)]
    calc
      _ ≤ (3 / Real.log 2) * Real.log Q.card * (2 * Real.log Q.card) +
          (2 / Real.log 2) * (Real.log Q.card) ^ 2 := add_le_add hp hlin
      _ = (8 / Real.log 2) * (Real.log Q.card) ^ 2 := by ring
      _ ≤ C * (Real.log Q.card) ^ 2 := mul_le_mul_of_nonneg_right hE (sq_nonneg _)

end Sandpile
