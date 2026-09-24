/-
Ray parity along a nearest-neighbor walk and its constancy near vertices outside the walk.
-/
import Sandpile.Support.RectangleDuality

open scoped BigOperators
noncomputable section
namespace Sandpile

def edgeRay (v x y : Site 2) : ZMod 2 := by
  classical
  exact if ((x 0 ≤ v 0 ∧ v 0 < y 0) ∨ (y 0 ≤ v 0 ∧ v 0 < x 0)) ∧
      max (x 1) (y 1) ≤ v 1 then 1 else 0

def columnBelow (v x : Site 2) : ZMod 2 := by
  classical
  exact if x 0 = v 0 ∧ x 1 ≤ v 1 then 1 else 0

lemma lattice_two_adj_cases {x y : Site 2} (hxy : (lattice 2).Adj x y) :
    (y 0 = x 0 + 1 ∧ y 1 = x 1) ∨ (x 0 = y 0 + 1 ∧ x 1 = y 1) ∨
    (y 1 = x 1 + 1 ∧ y 0 = x 0) ∨ (x 1 = y 1 + 1 ∧ x 0 = y 0) := by
  obtain ⟨i, hi | hi⟩ := hxy
  · have h0 := congrArg (fun z : Site 2 => z 0) hi
    have h1 := congrArg (fun z : Site 2 => z 1) hi
    fin_cases i <;> simp [unit] at h0 h1 <;> omega
  · have h0 := congrArg (fun z : Site 2 => z 0) hi
    have h1 := congrArg (fun z : Site 2 => z 1) hi
    fin_cases i <;> simp [unit] at h0 h1 <;> omega

lemma site_two_ne_iff (x y : Site 2) : x ≠ y ↔ x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    apply h
    ext i
    fin_cases i
    · exact hn.1
    · exact hn.2
  · rintro (h | h) he <;> exact h (congrFun he _)

lemma edgeRay_horizontal_coboundary {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) :
    edgeRay v x y + edgeRay (v - unit (0 : Fin 2)) x y = columnBelow v x + columnBelow v y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, columnBelow, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num <;> first | exact CharTwo.two_eq_zero.symm | omega

lemma edgeRay_vertical_right {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) : edgeRay v x y = edgeRay (v - unit (1 : Fin 2)) x y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num [CharTwo.two_eq_zero] <;> omega

lemma edgeRay_vertical_left {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) :
    edgeRay (v - unit (0 : Fin 2)) x y =
      edgeRay (v - unit (0 : Fin 2) - unit (1 : Fin 2)) x y := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, Pi.sub_apply, unit, Pi.single_apply, Fin.isValue,
      ite_true, max_le_iff]
    split_ifs <;> norm_num [CharTwo.two_eq_zero] <;> omega

def walkEdgeSum {V : Type*} {G : SimpleGraph V} (f : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b) : ZMod 2 :=
  match p with
  | .nil => 0
  | .cons (v := c) _ q => f a c + walkEdgeSum f q

lemma walkEdgeSum_coboundary {V : Type*} {G : SimpleGraph V} (f : V → ZMod 2)
    {a b : V} (p : G.Walk a b) : walkEdgeSum (fun x y => f x + f y) p = f a + f b := by
  induction p with
  | nil => exact (CharTwo.add_self_eq_zero _).symm
  | @cons a b c hab p ih =>
    simp only [walkEdgeSum, ih]
    linear_combination CharTwo.add_self_eq_zero (f b)

lemma walkEdgeSum_add {V : Type*} {G : SimpleGraph V} (f g : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b) :
    walkEdgeSum (fun x y => f x y + g x y) p = walkEdgeSum f p + walkEdgeSum g p := by
  induction p with
  | nil => simp [walkEdgeSum]
  | @cons a b c hab p ih => simp only [walkEdgeSum, ih]; ring

lemma walkEdgeSum_congr_on_support {V : Type*} {G : SimpleGraph V} (f g : V → V → ZMod 2)
    {a b : V} (p : G.Walk a b)
    (hfg : ∀ x ∈ p.support, ∀ y ∈ p.support, G.Adj x y → f x y = g x y) :
    walkEdgeSum f p = walkEdgeSum g p := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    change f a b + walkEdgeSum f p = g a b + walkEdgeSum g p
    rw [hfg a (by simp) b (by simp), ih]
    · intro x hx y hy hxy
      exact hfg x (by simp [hx]) y (by simp [hy]) hxy
    · exact hab

def walkRay {a b : Site 2} (p : (lattice 2).Walk a b) (v : Site 2) : ZMod 2 :=
  walkEdgeSum (edgeRay v) p

lemma walkRay_horizontal {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (ha : a 0 ≠ v 0) (hb : b 0 ≠ v 0) :
    walkRay p v = walkRay p (v - unit (0 : Fin 2)) := by
  have he := walkEdgeSum_congr_on_support
    (fun x y => edgeRay v x y + edgeRay (v - unit (0 : Fin 2)) x y)
    (fun x y => columnBelow v x + columnBelow v y) p
    (fun x hx y hy hxy => edgeRay_horizontal_coboundary hxy
      (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))
  rw [walkEdgeSum_add, walkEdgeSum_coboundary] at he
  have hh : walkRay p v + walkRay p (v - unit (0 : Fin 2)) = 0 := by
    simpa only [columnBelow, ha, hb, false_and, if_false, zero_add, walkRay] using he
  have hc := congrArg (fun z => z + walkRay p (v - unit (0 : Fin 2))) hh
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hc

lemma walkRay_vertical_right {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) : walkRay p v = walkRay p (v - unit (1 : Fin 2)) := by
  exact walkEdgeSum_congr_on_support _ _ p (fun x hx y hy hxy =>
    edgeRay_vertical_right hxy (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))

lemma walkRay_vertical_left {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) :
    walkRay p (v - unit (0 : Fin 2)) = walkRay p (v - unit (0 : Fin 2) - unit (1 : Fin 2)) := by
  exact walkEdgeSum_congr_on_support _ _ p (fun x hx y hy hxy =>
    edgeRay_vertical_left hxy (fun he => hv (he ▸ hx)) (fun he => hv (he ▸ hy)))

def leftOfCut (v x : Site 2) : ZMod 2 := by
  classical
  exact if x 0 ≤ v 0 then 1 else 0

lemma edgeRay_above {v x y : Site 2} (hx : x 1 ≤ v 1) (hy : y 1 ≤ v 1) :
    edgeRay v x y = leftOfCut v x + leftOfCut v y := by
  simp only [edgeRay, leftOfCut, max_le_iff, hx, hy, and_self, and_true]
  split_ifs <;> norm_num
  all_goals first | exact CharTwo.two_eq_zero.symm | omega

lemma edgeRay_below {v x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x ≠ v) (hy : y ≠ v) (hvx : v 1 ≤ x 1) (hvy : v 1 ≤ y 1) : edgeRay v x y = 0 := by
  have hx' := (site_two_ne_iff x v).mp hx
  have hy' := (site_two_ne_iff y v).mp hy
  obtain h | h | h | h := lattice_two_adj_cases hxy
  all_goals
    simp only [edgeRay, max_le_iff]
    split_ifs <;> norm_num
    all_goals omega

lemma walkEdgeSum_zero {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    walkEdgeSum (fun _ _ => 0) p = 0 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [walkEdgeSum, ih]

lemma walkRay_below {a b v : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (hbelow : ∀ z ∈ p.support, v 1 ≤ z 1) : walkRay p v = 0 := by
  have he := walkEdgeSum_congr_on_support (edgeRay v) (fun _ _ => 0) p
    (fun x hx y hy hxy => edgeRay_below hxy (fun he => hv (he ▸ hx))
      (fun he => hv (he ▸ hy)) (hbelow x hx) (hbelow y hy))
  exact he.trans (walkEdgeSum_zero p)

lemma walkRay_above {a b v : Site 2} (p : (lattice 2).Walk a b)
    (habove : ∀ z ∈ p.support, z 1 ≤ v 1) (ha : a 0 ≤ v 0) (hb : v 0 < b 0) : walkRay p v = 1 := by
  have he := walkEdgeSum_congr_on_support (edgeRay v)
    (fun x y => leftOfCut v x + leftOfCut v y) p
    (fun x hx y hy _ => edgeRay_above (habove x hx) (habove y hy))
  rw [walkEdgeSum_coboundary] at he
  simpa only [walkRay, leftOfCut, ha, not_le.mpr hb, if_true, if_false, add_zero] using he

lemma walkRay_four_faces {a b v u : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (ha : a 0 ≠ v 0) (hb : b 0 ≠ v 0)
    (hu0 : u 0 = v 0 ∨ u 0 = v 0 - 1) (hu1 : u 1 = v 1 ∨ u 1 = v 1 - 1) :
    walkRay p v = walkRay p u := by
  obtain hu0 | hu0 := hu0
  · obtain hu1 | hu1 := hu1
    · have he : u = v := by ext i; fin_cases i <;> assumption
      rw [he]
    · have he : u = v - unit (1 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact walkRay_vertical_right p hv
  · obtain hu1 | hu1 := hu1
    · have he : u = v - unit (0 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact walkRay_horizontal p hv ha hb
    · have he : u = v - unit (0 : Fin 2) - unit (1 : Fin 2) := by
        ext i
        fin_cases i <;> simp [unit, hu0, hu1]
      rw [he]
      exact (walkRay_horizontal p hv ha hb).trans (walkRay_vertical_left p hv)

lemma walkRay_star_step {a b v w : Site 2} (p : (lattice 2).Walk a b)
    (hv : v ∉ p.support) (hw : w ∉ p.support)
    (hav : a 0 ≠ v 0) (hbv : b 0 ≠ v 0) (haw : a 0 ≠ w 0) (hbw : b 0 ≠ w 0)
    (hvw : (starLatticeGraph 2).Adj v w) : walkRay p v = walkRay p w := by
  let u : Site 2 := ![min (v 0) (w 0), min (v 1) (w 1)]
  have hdist (i : Fin 2) : |v i - w i| ≤ 1 := by
    have hh := hvw.2 i
    simpa only [Int.natCast_natAbs, Nat.cast_one] using (show ((v i - w i).natAbs : ℤ) ≤ (1 : ℕ) from by exact_mod_cast hh)
  have hfaces (i : Fin 2) :
      (min (v i) (w i) = v i ∨ min (v i) (w i) = v i - 1) ∧
      (min (v i) (w i) = w i ∨ min (v i) (w i) = w i - 1) := by
    have hh := abs_le.mp (hdist i)
    omega
  exact (walkRay_four_faces p hv hav hbv (u := u) (hfaces 0).1 (hfaces 1).1).trans
    (walkRay_four_faces p hw haw hbw (u := u) (hfaces 0).2 (hfaces 1).2).symm

end Sandpile
