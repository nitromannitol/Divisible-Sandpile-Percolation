/-
Positive envelopes for the first three coordinate derivatives of smooth max/min
compositions, with dimension-independent sums and multiplicative stability.
-/
import LatticeProb.Analysis.SoftStability

open LatticeProb

open scoped BigOperators

namespace Sandpile

structure PositiveJet (V : Type*) where
  one : V → (V → ℝ) → ℝ
  two : V → V → (V → ℝ) → ℝ
  three : V → V → V → (V → ℝ) → ℝ

namespace PositiveJet

variable {V I : Type*} [Fintype I] [Nonempty I]

noncomputable def softOne (β : ℝ) (f : I → (V → ℝ) → ℝ)
    (A : I → PositiveJet V) (j : V) (x : V → ℝ) : ℝ :=
  ∑ i, softWeight β (fun i => f i x) i * (A i).one j x

noncomputable def softTwo (β : ℝ) (f : I → (V → ℝ) → ℝ)
    (A : I → PositiveJet V) (j k : V) (x : V → ℝ) : ℝ :=
  ∑ i, softWeight β (fun i => f i x) i *
    ((A i).two j k x + |β| * ((A i).one k x + softOne β f A k x) * (A i).one j x)

noncomputable def softThree (β : ℝ) (f : I → (V → ℝ) → ℝ)
    (A : I → PositiveJet V) (j k l : V) (x : V → ℝ) : ℝ :=
  ∑ i, softWeight β (fun i => f i x) i *
    ((A i).three j k l x +
      |β| * ((A i).one l x + softOne β f A l x) * (A i).two j k x +
      |β| * ((A i).one k x + softOne β f A k x) * (A i).two j l x +
      |β| * ((A i).two k l x + softTwo β f A k l x) * (A i).one j x +
      β ^ 2 * ((A i).one l x + softOne β f A l x) *
        ((A i).one k x + softOne β f A k x) * (A i).one j x)

noncomputable def softCompose (β : ℝ) (f : I → (V → ℝ) → ℝ)
    (A : I → PositiveJet V) : PositiveJet V where
  one := softOne β f A
  two := softTwo β f A
  three := softThree β f A

variable [Fintype V] [DecidableEq V]

structure Bounds (A : PositiveJet V) (β : ℝ) (n : ℕ) (f : (V → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) f
  nonexpansive : FieldNonexpansive f
  smooth_one : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (A.one j)
  smooth_two : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (A.two j k)
  smooth_three : ∀ j k l, ContDiff ℝ (⊤ : ℕ∞) (A.three j k l)
  stable_one : ∀ j, ExpStable (2 * |β| * n) (A.one j)
  stable_two : ∀ j k, ExpStable (4 * |β| * n) (A.two j k)
  stable_three : ∀ j k l, ExpStable (6 * |β| * n) (A.three j k l)
  bound_one : ∀ j x, |coordPartial f j x| ≤ A.one j x
  bound_two : ∀ j k x, |coordPartial (coordPartial f j) k x| ≤ A.two j k x
  bound_three : ∀ j k l x, |coordPartial (coordPartial (coordPartial f j) k) l x| ≤ A.three j k l x
  sum_one : ∀ x, ∑ j, A.one j x ≤ 1
  sum_two : ∀ x, ∑ j, ∑ k, A.two j k x ≤ 2 * |β| * n
  sum_three : ∀ x, ∑ j, ∑ k, ∑ l, A.three j k l x ≤ 6 * β ^ 2 * (n : ℝ) ^ 2

lemma Bounds.stable_softOne {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j : V) :
    ExpStable (2 * |β| * (n + 1 : ℕ)) (softOne β f A j) := by
  have h := ExpStable.sum (fun i =>
    (expStable_softWeightComposition hβ (fun i => (hA i).nonexpansive) i).mul
      ((hA i).stable_one j))
  convert h using 1 <;> first | rfl | (push_cast; ring)

lemma Bounds.stable_softTwo {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k : V) :
    ExpStable (4 * |β| * (n + 1 : ℕ)) (softTwo β f A j k) := by
  have hr (i : I) (a : V) : ExpStable (2 * |β| * (n + 1 : ℕ))
      (fun x => (A i).one a x + softOne β f A a x) := by
    apply ExpStable.add ?_ (Bounds.stable_softOne hβ hA a)
    exact ((hA i).stable_one a).mono (by push_cast; nlinarith [abs_nonneg β])
  have hrow (i : I) : ExpStable (4 * |β| * n + 2 * |β|)
      (fun x => (A i).two j k x + |β| *
        ((A i).one k x + softOne β f A k x) * (A i).one j x) := by
    apply ExpStable.add
      (((hA i).stable_two j k).mono (by nlinarith [abs_nonneg β]))
    have h := ((hr i k).const_mul (abs_nonneg β)).mul ((hA i).stable_one j)
    convert h using 1
    push_cast
    ring
  have h := ExpStable.sum (fun i =>
    (expStable_softWeightComposition hβ (fun i => (hA i).nonexpansive) i).mul (hrow i))
  convert h using 1 <;> first | rfl | (push_cast; ring)

lemma Bounds.stable_softThree {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k l : V) :
    ExpStable (6 * |β| * (n + 1 : ℕ)) (softThree β f A j k l) := by
  have hr (i : I) (a : V) : ExpStable (2 * |β| * (n + 1 : ℕ))
      (fun x => (A i).one a x + softOne β f A a x) := by
    apply ExpStable.add ?_ (Bounds.stable_softOne hβ hA a)
    exact ((hA i).stable_one a).mono (by push_cast; nlinarith [abs_nonneg β])
  have hdiff (i : I) (a b : V) : ExpStable (4 * |β| * (n + 1 : ℕ))
      (fun x => (A i).two a b x + softTwo β f A a b x) := by
    apply ExpStable.add ?_ (Bounds.stable_softTwo hβ hA a b)
    exact ((hA i).stable_two a b).mono (by push_cast; nlinarith [abs_nonneg β])
  let K := 6 * |β| * (n : ℝ) + 4 * |β|
  have h2 (i : I) (a b c : V) : ExpStable K
      (fun x => |β| * ((A i).one a x + softOne β f A a x) * (A i).two b c x) := by
    exact (((hr i a).const_mul (abs_nonneg β)).mul ((hA i).stable_two b c)).mono
      (by dsimp [K]; push_cast; nlinarith [abs_nonneg β])
  have h3 (i : I) : ExpStable K
      (fun x => |β| * ((A i).two k l x + softTwo β f A k l x) * (A i).one j x) := by
    exact (((hdiff i k l).const_mul (abs_nonneg β)).mul ((hA i).stable_one j)).mono
      (by dsimp [K]; push_cast; nlinarith)
  have h4 (i : I) : ExpStable K
      (fun x => β ^ 2 * ((A i).one l x + softOne β f A l x) *
        ((A i).one k x + softOne β f A k x) * (A i).one j x) := by
    exact ((((hr i l).const_mul (sq_nonneg β)).mul (hr i k)).mul
      ((hA i).stable_one j)).mono (by dsimp [K]; push_cast; nlinarith)
  have hrow (i : I) : ExpStable K
      (fun x => (A i).three j k l x +
        |β| * ((A i).one l x + softOne β f A l x) * (A i).two j k x +
        |β| * ((A i).one k x + softOne β f A k x) * (A i).two j l x +
        |β| * ((A i).two k l x + softTwo β f A k l x) * (A i).one j x +
        β ^ 2 * ((A i).one l x + softOne β f A l x) *
          ((A i).one k x + softOne β f A k x) * (A i).one j x) :=
    (((((hA i).stable_three j k l).mono (by dsimp [K]; nlinarith [abs_nonneg β])).add
      (h2 i l j k)).add (h2 i k j l)).add (h3 i) |>.add (h4 i)
  have h := ExpStable.sum (fun i =>
    (expStable_softWeightComposition hβ (fun i => (hA i).nonexpansive) i).mul (hrow i))
  convert h using 1 <;> try rfl
  dsimp [K]
  push_cast
  ring

lemma Bounds.smooth_softOne {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j : V) :
    ContDiff ℝ (⊤ : ℕ∞) (softOne β f A j) := by
  exact ContDiff.sum (fun i _ =>
    (contDiff_softWeightComposition hβ (fun i => (hA i).smooth) i).mul ((hA i).smooth_one j))

lemma Bounds.smooth_softTwo {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k : V) :
    ContDiff ℝ (⊤ : ℕ∞) (softTwo β f A j k) := by
  exact ContDiff.sum (fun i _ =>
    (contDiff_softWeightComposition hβ (fun i => (hA i).smooth) i).mul
      (((hA i).smooth_two j k).add
        ((contDiff_const.mul (((hA i).smooth_one k).add (Bounds.smooth_softOne hβ hA k))).mul
          ((hA i).smooth_one j))))

lemma Bounds.smooth_softThree {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k l : V) :
    ContDiff ℝ (⊤ : ℕ∞) (softThree β f A j k l) := by
  have hr (i : I) (a : V) := ((hA i).smooth_one a).add (Bounds.smooth_softOne hβ hA a)
  have hd (i : I) (a b : V) := ((hA i).smooth_two a b).add (Bounds.smooth_softTwo hβ hA a b)
  exact ContDiff.sum (fun i _ =>
    (contDiff_softWeightComposition hβ (fun i => (hA i).smooth) i).mul
      ((((((hA i).smooth_three j k l).add
        ((contDiff_const.mul (hr i l)).mul ((hA i).smooth_two j k))).add
        ((contDiff_const.mul (hr i k)).mul ((hA i).smooth_two j l))).add
        ((contDiff_const.mul (hd i k l)).mul ((hA i).smooth_one j))).add
        (((contDiff_const.mul (hr i l)).mul (hr i k)).mul ((hA i).smooth_one j))))

lemma Bounds.bound_softOne {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j : V) (x : V → ℝ) :
    |coordPartial (fun y => softMaximum β (fun i => f i y)) j x| ≤ softOne β f A j x := by
  rw [coordPartial_softComposition hβ (fun i => (hA i).smooth.differentiable (by simp))]
  calc
    _ ≤ ∑ i, softWeight β (fun i => f i x) i * |coordPartial (f i) j x| :=
      (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [abs_mul, abs_of_pos (softWeight_pos β _ _)])
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ((hA i).bound_one j x) (softWeight_pos β _ i).le

lemma Bounds.bound_softTwo {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k : V) (x : V → ℝ) :
    |coordPartial (coordPartial (fun y => softMaximum β (fun i => f i y)) j) k x| ≤
      softTwo β f A j k x := by
  let L := fun y => softMaximum β (fun i => f i y)
  have hr (i : I) (a : V) : |coordPartial (f i) a x - coordPartial L a x| ≤
      (A i).one a x + softOne β f A a x :=
    (abs_sub _ _).trans (add_le_add ((hA i).bound_one a x) (Bounds.bound_softOne hβ hA a x))
  rw [coordPartial_softComposition_two hβ (fun i => (hA i).smooth)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_of_pos (softWeight_pos β _ i)]
  apply mul_le_mul_of_nonneg_left _ (softWeight_pos β _ i).le
  calc
    _ ≤ |coordPartial (coordPartial (f i) j) k x| +
        |β| * |coordPartial (f i) k x - coordPartial L k x| * |coordPartial (f i) j x| := by
      simpa only [abs_mul] using abs_add_le
        (coordPartial (coordPartial (f i) j) k x)
        (β * (coordPartial (f i) k x - coordPartial L k x) * coordPartial (f i) j x)
    _ ≤ _ := add_le_add ((hA i).bound_two j k x)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hr i k) (abs_nonneg β)) ((hA i).bound_one j x)
        (abs_nonneg _) (mul_nonneg (abs_nonneg β)
          (add_nonneg (((hA i).stable_one k).nonneg x) ((Bounds.stable_softOne hβ hA k).nonneg x))))

lemma Bounds.bound_softThree {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (j k l : V) (x : V → ℝ) :
    |coordPartial (coordPartial
      (coordPartial (fun y => softMaximum β (fun i => f i y)) j) k) l x| ≤
      softThree β f A j k l x := by
  let L := fun y => softMaximum β (fun i => f i y)
  let d (i : I) (a : V) := coordPartial (f i) a x
  let H (i : I) (a b : V) := coordPartial (coordPartial (f i) a) b x
  let T (i : I) (a b c : V) := coordPartial (coordPartial (coordPartial (f i) a) b) c x
  let r (i : I) (a : V) := d i a - coordPartial L a x
  let D (i : I) (a b : V) := H i a b - coordPartial (coordPartial L a) b x
  have hr (i : I) (a : V) : |r i a| ≤ (A i).one a x + softOne β f A a x :=
    (abs_sub _ _).trans (add_le_add ((hA i).bound_one a x) (Bounds.bound_softOne hβ hA a x))
  have hD (i : I) (a b : V) : |D i a b| ≤ (A i).two a b x + softTwo β f A a b x :=
    (abs_sub _ _).trans (add_le_add ((hA i).bound_two a b x) (Bounds.bound_softTwo hβ hA a b x))
  have hr0 (i : I) (a : V) : 0 ≤ (A i).one a x + softOne β f A a x :=
    (abs_nonneg _).trans (hr i a)
  have hD0 (i : I) (a b : V) : 0 ≤ (A i).two a b x + softTwo β f A a b x :=
    (abs_nonneg _).trans (hD i a b)
  rw [coordPartial_softComposition_three hβ (fun i => (hA i).smooth)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_of_pos (softWeight_pos β _ i)]
  apply mul_le_mul_of_nonneg_left _ (softWeight_pos β _ i).le
  change |T i j k l + β * r i l * H i j k + β * r i k * H i j l +
    β * D i k l * d i j + β ^ 2 * r i l * r i k * d i j| ≤ _
  calc
    _ ≤ |T i j k l| + |β| * |r i l| * |H i j k| + |β| * |r i k| * |H i j l| +
        |β| * |D i k l| * |d i j| + β ^ 2 * |r i l| * |r i k| * |d i j| := by
      have h := abs_add_le (T i j k l + β * r i l * H i j k + β * r i k * H i j l +
        β * D i k l * d i j) (β ^ 2 * r i l * r i k * d i j)
      have h' := abs_add_le (T i j k l + β * r i l * H i j k + β * r i k * H i j l)
        (β * D i k l * d i j)
      have h'' := abs_add_le (T i j k l + β * r i l * H i j k) (β * r i k * H i j l)
      have h''' := abs_add_le (T i j k l) (β * r i l * H i j k)
      simp only [abs_mul, abs_pow, sq_abs] at h h' h'' h'''
      linarith only [h, h', h'', h''']
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · apply add_le_add ((hA i).bound_three j k l x)
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hr i l) (abs_nonneg β))
              ((hA i).bound_two j k x) (abs_nonneg _) (mul_nonneg (abs_nonneg β) (hr0 i l))
          · exact mul_le_mul (mul_le_mul_of_nonneg_left (hr i k) (abs_nonneg β))
              ((hA i).bound_two j l x) (abs_nonneg _) (mul_nonneg (abs_nonneg β) (hr0 i k))
        · exact mul_le_mul (mul_le_mul_of_nonneg_left (hD i k l) (abs_nonneg β))
            ((hA i).bound_one j x) (abs_nonneg _) (mul_nonneg (abs_nonneg β) (hD0 i k l))
      · exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left (hr i l) (sq_nonneg β)) (hr i k)
            (abs_nonneg _) (mul_nonneg (sq_nonneg β) (hr0 i l))) ((hA i).bound_one j x)
          (abs_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg β) (hr0 i l)) (hr0 i k))

lemma Bounds.sum_softOne {β : ℝ} {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (x : V → ℝ) :
    ∑ j, softOne β f A j x ≤ 1 := by
  simp only [softOne]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ ≤ ∑ i, softWeight β (fun i => f i x) i * 1 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left ((hA i).sum_one x) (softWeight_pos β _ i).le
    _ = 1 := by simp only [mul_one, sum_softWeight]

lemma Bounds.sum_softTwo {β : ℝ} {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (x : V → ℝ) :
    ∑ j, ∑ k, softTwo β f A j k x ≤ 2 * |β| * (n + 1 : ℕ) := by
  let r (i : I) (a : V) := (A i).one a x + softOne β f A a x
  have hr (i : I) : ∑ j, r i j ≤ 2 := by
    dsimp [r]
    rw [Finset.sum_add_distrib]
    linarith only [(hA i).sum_one x, Bounds.sum_softOne hA x]
  have h1 (i : I) : 0 ≤ ∑ j, (A i).one j x :=
    Finset.sum_nonneg (fun j _ => ((hA i).stable_one j).nonneg x)
  have hrow (i : I) :
      ∑ j, ∑ k, ((A i).two j k x + |β| * r i k * (A i).one j x) ≤
        2 * |β| * (n + 1 : ℕ) := by
    calc
      _ = (∑ j, ∑ k, (A i).two j k x) +
          |β| * (∑ k, r i k) * ∑ j, (A i).one j x := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ 2 * |β| * n + |β| * 2 * 1 := add_le_add ((hA i).sum_two x)
        (mul_le_mul (mul_le_mul_of_nonneg_left (hr i) (abs_nonneg β)) ((hA i).sum_one x)
          (h1 i) (by positivity))
      _ = _ := by push_cast; ring
  change (∑ j, ∑ k, ∑ i, softWeight β (fun i => f i x) i *
    ((A i).two j k x + |β| * r i k * (A i).one j x)) ≤ _
  calc
    _ = ∑ i, softWeight β (fun i => f i x) i *
        ∑ j, ∑ k, ((A i).two j k x + |β| * r i k * (A i).one j x) := by
      simp only [Finset.mul_sum]
      rw [show (∑ j, ∑ k, ∑ i, softWeight β (fun i => f i x) i *
          ((A i).two j k x + |β| * r i k * (A i).one j x)) =
        ∑ j, ∑ i, ∑ k, softWeight β (fun i => f i x) i *
          ((A i).two j k x + |β| * r i k * (A i).one j x) from
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
      exact Finset.sum_comm
    _ ≤ ∑ i, softWeight β (fun i => f i x) i * (2 * |β| * (n + 1 : ℕ)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (softWeight_pos β _ i).le
    _ = _ := by rw [← Finset.sum_mul, sum_softWeight, one_mul]

lemma Bounds.sum_softThree {β : ℝ} {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) (x : V → ℝ) :
    ∑ j, ∑ k, ∑ l, softThree β f A j k l x ≤ 6 * β ^ 2 * (n + 1 : ℕ) ^ 2 := by
  let r (i : I) (a : V) := (A i).one a x + softOne β f A a x
  let D (i : I) (a b : V) := (A i).two a b x + softTwo β f A a b x
  let U (i : I) (j k l : V) := (A i).three j k l x +
    |β| * r i l * (A i).two j k x + |β| * r i k * (A i).two j l x +
    |β| * D i k l * (A i).one j x + β ^ 2 * r i l * r i k * (A i).one j x
  have hr (i : I) : ∑ j, r i j ≤ 2 := by
    dsimp [r]
    rw [Finset.sum_add_distrib]
    linarith only [(hA i).sum_one x, Bounds.sum_softOne hA x]
  have hD (i : I) : ∑ k, ∑ l, D i k l ≤ 4 * |β| * n + 2 * |β| := by
    dsimp [D]
    simp only [Finset.sum_add_distrib]
    have h := add_le_add ((hA i).sum_two x) (Bounds.sum_softTwo hA x)
    convert h using 1 <;> first | rfl | (push_cast; ring)
  have h1 (i : I) : 0 ≤ ∑ j, (A i).one j x :=
    Finset.sum_nonneg (fun j _ => ((hA i).stable_one j).nonneg x)
  have h2 (i : I) : 0 ≤ ∑ j, ∑ k, (A i).two j k x :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => ((hA i).stable_two j k).nonneg x))
  have hr0 (i : I) : 0 ≤ ∑ j, r i j := by
    apply Finset.sum_nonneg
    intro j _
    exact add_nonneg (((hA i).stable_one j).nonneg x)
      (Finset.sum_nonneg (fun a _ => mul_nonneg (softWeight_pos β _ a).le
        (((hA a).stable_one j).nonneg x)))
  have hrow (i : I) : ∑ j, ∑ k, ∑ l, U i j k l ≤ 6 * β ^ 2 * (n + 1 : ℕ) ^ 2 := by
    have hb2 : ∑ j, ∑ k, ∑ l, |β| * r i l * (A i).two j k x ≤
        |β| * 2 * (2 * |β| * n) := by
      calc
        _ = |β| * (∑ l, r i l) * ∑ j, ∑ k, (A i).two j k x := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hr i) (abs_nonneg β))
          ((hA i).sum_two x) (h2 i) (by positivity)
    have hb3 : ∑ j, ∑ k, ∑ l, |β| * r i k * (A i).two j l x ≤
        |β| * 2 * (2 * |β| * n) := by
      calc
        _ = |β| * (∑ k, r i k) * ∑ j, ∑ l, (A i).two j l x := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hr i) (abs_nonneg β))
          ((hA i).sum_two x) (h2 i) (by positivity)
    have hb4 : ∑ j, ∑ k, ∑ l, |β| * D i k l * (A i).one j x ≤
        |β| * (4 * |β| * n + 2 * |β|) := by
      calc
        _ = |β| * (∑ k, ∑ l, D i k l) * ∑ j, (A i).one j x := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ |β| * (4 * |β| * n + 2 * |β|) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hD i) (abs_nonneg β)) ((hA i).sum_one x)
            (h1 i) (by positivity)
        _ = _ := mul_one _
    have hb5 : ∑ j, ∑ k, ∑ l, β ^ 2 * r i l * r i k * (A i).one j x ≤ 4 * β ^ 2 := by
      calc
        _ = β ^ 2 * (∑ l, r i l) * (∑ k, r i k) * ∑ j, (A i).one j x := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ β ^ 2 * 2 * 2 * 1 := mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left (hr i) (sq_nonneg β)) (hr i) (hr0 i)
            (by positivity)) ((hA i).sum_one x) (h1 i) (by positivity)
        _ = _ := by ring
    dsimp only [U]
    simp only [Finset.sum_add_distrib]
    apply (add_le_add (add_le_add (add_le_add (add_le_add ((hA i).sum_three x) hb2) hb3) hb4) hb5).trans_eq
    push_cast
    nlinarith [sq_abs β]
  change (∑ j, ∑ k, ∑ l, ∑ i, softWeight β (fun i => f i x) i * U i j k l) ≤ _
  calc
    _ = ∑ i, softWeight β (fun i => f i x) i * ∑ j, ∑ k, ∑ l, U i j k l := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ j, ∑ k, ∑ i, ∑ l, softWeight β (fun i => f i x) i * U i j k l :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
        _ = ∑ j, ∑ i, ∑ k, ∑ l, softWeight β (fun i => f i x) i * U i j k l :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ ≤ ∑ i, softWeight β (fun i => f i x) i * (6 * β ^ 2 * (n + 1 : ℕ) ^ 2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (softWeight_pos β _ i).le
    _ = _ := by rw [← Finset.sum_mul, sum_softWeight, one_mul]

lemma Bounds.softMaximum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) :
    (softCompose β f A).Bounds β (n + 1) (fun y => LatticeProb.softMaximum β (fun i => f i y)) where
  smooth := contDiff_softComposition β (fun i => (hA i).smooth)
  nonexpansive := FieldNonexpansive.softMaximum hβ (fun i => (hA i).nonexpansive)
  smooth_one := Bounds.smooth_softOne hβ hA
  smooth_two := Bounds.smooth_softTwo hβ hA
  smooth_three := Bounds.smooth_softThree hβ hA
  stable_one := Bounds.stable_softOne hβ hA
  stable_two := Bounds.stable_softTwo hβ hA
  stable_three := Bounds.stable_softThree hβ hA
  bound_one := Bounds.bound_softOne hβ hA
  bound_two := Bounds.bound_softTwo hβ hA
  bound_three := Bounds.bound_softThree hβ hA
  sum_one := Bounds.sum_softOne hA
  sum_two := Bounds.sum_softTwo hA
  sum_three := Bounds.sum_softThree hA

omit [Fintype I] [Nonempty I] in
lemma Bounds.neg_beta {β : ℝ} {n : ℕ} {f : (V → ℝ) → ℝ} {A : PositiveJet V}
    (hA : A.Bounds β n f) : A.Bounds (-β) n f where
  smooth := hA.smooth
  nonexpansive := hA.nonexpansive
  smooth_one := hA.smooth_one
  smooth_two := hA.smooth_two
  smooth_three := hA.smooth_three
  stable_one j := by simpa only [abs_neg] using hA.stable_one j
  stable_two j k := by simpa only [abs_neg] using hA.stable_two j k
  stable_three j k l := by simpa only [abs_neg] using hA.stable_three j k l
  bound_one := hA.bound_one
  bound_two := hA.bound_two
  bound_three := hA.bound_three
  sum_one := hA.sum_one
  sum_two x := by simpa only [abs_neg] using hA.sum_two x
  sum_three x := by simpa only [neg_sq] using hA.sum_three x

lemma Bounds.softMinimum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} {A : I → PositiveJet V}
    (hA : ∀ i, (A i).Bounds β n (f i)) :
    (softCompose (-β) f A).Bounds β (n + 1) (fun y => LatticeProb.softMinimum β (fun i => f i y)) := by
  have h := (Bounds.softMaximum (neg_ne_zero.mpr hβ) (fun i => (hA i).neg_beta)).neg_beta
  simpa only [neg_neg, LatticeProb.softMinimum] using h

omit [Fintype I] [Nonempty I] in
lemma Bounds.mono {β : ℝ} {n m : ℕ} {f : (V → ℝ) → ℝ} {A : PositiveJet V}
    (hA : A.Bounds β n f) (hnm : n ≤ m) : A.Bounds β m f where
  smooth := hA.smooth
  nonexpansive := hA.nonexpansive
  smooth_one := hA.smooth_one
  smooth_two := hA.smooth_two
  smooth_three := hA.smooth_three
  stable_one j := (hA.stable_one j).mono (by gcongr)
  stable_two j k := (hA.stable_two j k).mono (by gcongr)
  stable_three j k l := (hA.stable_three j k l).mono (by gcongr)
  bound_one := hA.bound_one
  bound_two := hA.bound_two
  bound_three := hA.bound_three
  sum_one := hA.sum_one
  sum_two x := (hA.sum_two x).trans (by gcongr)
  sum_three x := (hA.sum_three x).trans (by gcongr)

omit [Fintype I] [Nonempty I] in
lemma Bounds.smoothBottleneckBound {β : ℝ} {n : ℕ} {f : (V → ℝ) → ℝ} {A : PositiveJet V}
    (hA : A.Bounds β n f) : SmoothBottleneckBound β n f := by
  refine ⟨hA.smooth, fun x => ⟨?_, ?_, ?_⟩⟩
  · exact (Finset.sum_le_sum (fun j _ => hA.bound_one j x)).trans (hA.sum_one x)
  · exact (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum
      (fun k _ => hA.bound_two j k x))).trans (hA.sum_two x)
  · exact (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
      Finset.sum_le_sum (fun l _ => hA.bound_three j k l x)))).trans (hA.sum_three x)

omit [Fintype I] [Nonempty I] in
def coordinate (i : V) : PositiveJet V where
  one j _ := if i = j then 1 else 0
  two _ _ _ := 0
  three _ _ _ _ := 0

omit [Fintype I] [Nonempty I] in
lemma bounds_coordinate (β : ℝ) (i : V) :
    (coordinate i).Bounds β 0 (fun x : V → ℝ => x i) := by
  have hpartial (j : V) (x : V → ℝ) :
      coordPartial (fun x : V → ℝ => x i) j x = if i = j then 1 else 0 := by
    simp only [coordPartial, (hasFDerivAt_apply i x).fderiv, ContinuousLinearMap.proj_apply]
    simp [Pi.single_apply]
  have hzero (j k : V) (x : V → ℝ) :
      coordPartial (coordPartial (fun x : V → ℝ => x i) j) k x = 0 := by
    have he : coordPartial (fun x : V → ℝ => x i) j = fun _ => if i = j then 1 else 0 :=
      funext (hpartial j)
    rw [he]
    simp [coordPartial]
  refine ⟨contDiff_apply ℝ ℝ i, fieldNonexpansive_coordinate i,
    fun _ => contDiff_const, fun _ _ => contDiff_const, fun _ _ _ => contDiff_const,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [Nat.cast_zero, mul_zero, coordinate] using
      expStable_const (V := V) (show 0 ≤ (if i = j then 1 else 0 : ℝ) by split_ifs <;> norm_num)
  · intro j k
    simpa only [Nat.cast_zero, mul_zero, coordinate] using expStable_const (V := V) (le_refl (0 : ℝ))
  · intro j k l
    simpa only [Nat.cast_zero, mul_zero, coordinate] using expStable_const (V := V) (le_refl (0 : ℝ))
  · intro j x
    simp [hpartial, coordinate, apply_ite abs]
  · intro j k x
    simp [hzero, coordinate]
  · intro j k l x
    have he : coordPartial (coordPartial (fun x : V → ℝ => x i) j) k = fun _ => 0 :=
      funext (hzero j k)
    simp [he, coordPartial, coordinate]
  · intro x
    simp [coordinate]
  · intro x
    simp [coordinate]
  · intro x
    simp [coordinate]

end PositiveJet

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A smooth function with positive derivative envelopes and stable coordinate weights. -/
def HasPositiveJet (β : ℝ) (n : ℕ) (f : (V → ℝ) → ℝ) : Prop :=
  ∃ A : PositiveJet V, A.Bounds β n f

lemma hasPositiveJet_coordinate (β : ℝ) (i : V) :
    HasPositiveJet β 0 (fun x : V → ℝ => x i) :=
  ⟨PositiveJet.coordinate i, PositiveJet.bounds_coordinate β i⟩

lemma HasPositiveJet.mono {β : ℝ} {n m : ℕ} {f : (V → ℝ) → ℝ}
    (hf : HasPositiveJet β n f) (hnm : n ≤ m) : HasPositiveJet β m f := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, hA.mono hnm⟩

lemma HasPositiveJet.smoothBottleneckBound {β : ℝ} {n : ℕ} {f : (V → ℝ) → ℝ}
    (hf : HasPositiveJet β n f) : SmoothBottleneckBound β n f := by
  obtain ⟨A, hA⟩ := hf
  exact hA.smoothBottleneckBound

variable {I : Type*} [Fintype I] [Nonempty I]

lemma HasPositiveJet.softMaximum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, HasPositiveJet β n (f i)) :
    HasPositiveJet β (n + 1) (fun x => LatticeProb.softMaximum β (fun i => f i x)) := by
  classical
  choose A hA using hf
  exact ⟨_, PositiveJet.Bounds.softMaximum hβ hA⟩

lemma HasPositiveJet.softMinimum {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f : I → (V → ℝ) → ℝ} (hf : ∀ i, HasPositiveJet β n (f i)) :
    HasPositiveJet β (n + 1) (fun x => LatticeProb.softMinimum β (fun i => f i x)) := by
  classical
  choose A hA using hf
  exact ⟨_, PositiveJet.Bounds.softMinimum hβ hA⟩

omit [Fintype I] [Nonempty I] in
lemma HasPositiveJet.softMinimum_pair {β : ℝ} (hβ : β ≠ 0) {n : ℕ}
    {f g : (V → ℝ) → ℝ} (hf : HasPositiveJet β n f) (hg : HasPositiveJet β n g) :
    HasPositiveJet β (n + 1) (fun F => LatticeProb.softMinimum β ![f F, g F]) := by
  have hh : ∀ i : Fin 2, HasPositiveJet β n (![f, g] i) := by
    intro i
    fin_cases i
    · exact hf
    · exact hg
  have he : (fun F => LatticeProb.softMinimum β (fun i => ![f, g] i F)) =
      (fun F => LatticeProb.softMinimum β ![f F, g F]) := by
    funext F
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [← he]
  exact HasPositiveJet.softMinimum hβ hh

end Sandpile
