/-
The crossing bottleneck of a finite lattice rectangle is Lipschitz in the
uniform field norm, hence continuous and measurable.
-/
import Sandpile.Support.RectangleBottleneck

open scoped BigOperators

noncomputable section

namespace Sandpile

lemma abs_finiteMaximum_sub_le {I : Type*} [Fintype I] [Nonempty I]
    (f g : I → ℝ) {a : ℝ} (ha : ∀ i, |f i - g i| ≤ a) :
    |finiteMaximum f - finiteMaximum g| ≤ a := by
  have hu : finiteMaximum f ≤ finiteMaximum g + a := (finiteMaximum_le_iff _ _).mpr (fun i => by
    have hh := (abs_le.mp (ha i)).2
    linarith [le_finiteMaximum g i])
  have hl : finiteMaximum g ≤ finiteMaximum f + a := (finiteMaximum_le_iff _ _).mpr (fun i => by
    have hh := (abs_le.mp (ha i)).1
    linarith [le_finiteMaximum f i])
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma boundedBottleneckValue_abs_sub_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F H : V → ℝ) {a : ℝ} (ha : ∀ i, |F i - H i| ≤ a) :
    ∀ (n : ℕ) (x y : V) (h : BoundedReach G n x y),
      |boundedBottleneckValue G n x y h F - boundedBottleneckValue G n x y h H| ≤ a := by
  intro n
  induction n with
  | zero =>
    intro x y h
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (ha x) (ha y))
  | succ n ih =>
    intro x y h
    letI : Nonempty (walkMidpoints G n x y) := by
      obtain ⟨z, hz⟩ := walkMidpoints_nonempty G h
      exact ⟨⟨z, hz⟩⟩
    apply abs_finiteMaximum_sub_le
    intro z
    exact (abs_min_sub_min_le_max _ _ _ _).trans
      (max_le (ih x z _) (ih z y _))

lemma crossingValue_abs_sub_le {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) (F H : Q → ℝ) {a : ℝ} (ha : ∀ i, |F i - H i| ≤ a) :
    |crossingValue Q F - crossingValue Q H| ≤ a := by
  classical
  obtain ⟨hl, hr⟩ := rectangle_boundaries_nonempty hQ hN
  letI : Nonempty (rectangleLeft Q) := ⟨⟨hl.choose, hl.choose_spec⟩⟩
  letI : Nonempty (rectangleRight Q) := ⟨⟨hr.choose, hr.choose_spec⟩⟩
  have hn : Q.card ≤ 2 ^ Q.card := Nat.le_of_lt (Nat.lt_two_pow_self)
  rw [crossingValue_eq_bounded_max hQ hn F, crossingValue_eq_bounded_max hQ hn H]
  apply abs_finiteMaximum_sub_le
  intro p
  exact boundedBottleneckValue_abs_sub_le _ F H ha _ p.1 p.2 _

lemma lipschitzWith_crossingValue {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) : LipschitzWith 1 (crossingValue Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro F H
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  exact crossingValue_abs_sub_le hQ hN F H (fun i => by
    simpa only [Real.dist_eq] using dist_le_pi_dist F H i)

lemma continuous_crossingValue {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) : Continuous (crossingValue Q) :=
  (lipschitzWith_crossingValue hQ hN).continuous

lemma measurable_crossingValue {Q : Finset (Site 2)} (hQ : IsLatticeRectangle Q)
    (hN : Q.Nonempty) : Measurable (crossingValue Q) :=
  (continuous_crossingValue hQ hN).measurable

end Sandpile
