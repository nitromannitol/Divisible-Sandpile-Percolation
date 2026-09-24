/-
The deterministic core of Step 3 of `lem:dgt4-path-survival` (`sandpile.tex:5584-5610`).

After the threshold replacement, the factorized approximation to
`P(S_{n_R,i}(X)=S_{n_R,j}(Y)=1\mid X,Y)` is a product over the union of the two ranges,
carrying at a site shared by the two paths the factor `1-\max\{\pi_{R,r},\pi_{R,h}\}` of
the smaller threshold, while the approximation to the product of the two marginals carries
`(1-\pi_{R,r})(1-\pi_{R,h})` there; off the shared sites the two agree.  Three lemmas
separate that bookkeeping from the probability.

`prod_union_sep` is the identity that the separated product over the union IS the product of
the two marginal products.  `abs_prod_joint_sub_prod_sep_le` is the paper's estimate: by
`|\prod s-\prod t|\leq\sum|s-t|` and `0\leq1-\max\{a,b\}-(1-a)(1-b)\leq a+b`, the two
products differ by at most `\sum_{x\text{ shared}}(\pi_{R,r_x}+\pi_{R,h_x})`.
`card_inter_image_le_pairs` is the paper's passage from shared SITES to the double sum
`\sum_{r=0}^i\sum_{h=0}^j\one_{\{X_r=Y_h\}}`: a shared site is carried to one pair of
times realizing it, and that map is injective because the site is recovered from the time.
`abs_prod_joint_sub_prod_sep_le_count` is the combination, in the shape
`eq:dgt4-positive-path-covariance` needs, with `2c=C/(\delta R^2)`.
-/
import Sandpile.Support.LinStep2Split

open MeasureTheory Filter Topology

namespace Sandpile

variable {ι : Type*} [DecidableEq ι]

/-- The separated product over the union of the two ranges is the product of the two
marginal products. -/
theorem prod_union_sep (AX AY : Finset ι) (p q : ι → ℝ) :
    ∏ x ∈ AX ∪ AY, ((if x ∈ AX then 1 - p x else 1) * (if x ∈ AY then 1 - q x else 1))
      = (∏ x ∈ AX, (1 - p x)) * ∏ x ∈ AY, (1 - q x) := by
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ x ∈ AX ∪ AY, (if x ∈ AX then 1 - p x else 1) = ∏ x ∈ AX, (1 - p x) := by
    rw [← Finset.prod_subset (Finset.subset_union_left (s₁ := AX) (s₂ := AY))
      (fun x _ hx => if_neg hx)]
    exact Finset.prod_congr rfl fun x hx => if_pos hx
  have h2 : ∏ x ∈ AX ∪ AY, (if x ∈ AY then 1 - q x else 1) = ∏ x ∈ AY, (1 - q x) := by
    rw [← Finset.prod_subset (Finset.subset_union_right (s₁ := AX) (s₂ := AY))
      (fun x _ hx => if_neg hx)]
    exact Finset.prod_congr rfl fun x hx => if_pos hx
  rw [h1, h2]

/-- **The estimate of Step 3** (`sandpile.tex:5590-5601`).  The joint factorization and the
product of the two marginal factorizations differ by at most the sum of the two thresholds
over the shared sites. -/
theorem abs_prod_joint_sub_prod_sep_le (AX AY : Finset ι) (p q : ι → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1) :
    |(∏ x ∈ AX ∪ AY, (if x ∈ AX then (if x ∈ AY then 1 - max (p x) (q x) else 1 - p x)
          else 1 - q x))
        - (∏ x ∈ AX, (1 - p x)) * ∏ x ∈ AY, (1 - q x)|
      ≤ ∑ x ∈ AX ∩ AY, (p x + q x) := by
  classical
  have hmax0 : ∀ x, 0 ≤ max (p x) (q x) := fun x => le_trans (hp0 x) (le_max_left _ _)
  have hmax1 : ∀ x, max (p x) (q x) ≤ 1 := fun x => max_le (hp1 x) (hq1 x)
  set s : ι → ℝ := fun x => if x ∈ AX then (if x ∈ AY then 1 - max (p x) (q x) else 1 - p x)
    else 1 - q x with hs
  set t : ι → ℝ := fun x => (if x ∈ AX then 1 - p x else 1) * (if x ∈ AY then 1 - q x else 1)
    with ht
  rw [← prod_union_sep AX AY p q]
  have hs0 : ∀ x, 0 ≤ s x := by
    intro x
    simp only [hs]
    split_ifs with h1 h2
    · linarith [hmax1 x]
    · linarith [hp1 x]
    · linarith [hq1 x]
  have hs1 : ∀ x, s x ≤ 1 := by
    intro x
    simp only [hs]
    split_ifs with h1 h2
    · linarith [hmax0 x]
    · linarith [hp0 x]
    · linarith [hq0 x]
  have hfx : ∀ x, 0 ≤ (if x ∈ AX then 1 - p x else 1) ∧ (if x ∈ AX then 1 - p x else 1) ≤ 1 := by
    intro x
    constructor
    · split_ifs with h
      · linarith [hp1 x]
      · norm_num
    · split_ifs with h
      · linarith [hp0 x]
      · norm_num
  have hfy : ∀ x, 0 ≤ (if x ∈ AY then 1 - q x else 1) ∧ (if x ∈ AY then 1 - q x else 1) ≤ 1 := by
    intro x
    constructor
    · split_ifs with h
      · linarith [hq1 x]
      · norm_num
    · split_ifs with h
      · linarith [hq0 x]
      · norm_num
  have ht0 : ∀ x, 0 ≤ t x := fun x => mul_nonneg (hfx x).1 (hfy x).1
  have ht1 : ∀ x, t x ≤ 1 := fun x => mul_le_one₀ (hfx x).2 (hfy x).1 (hfy x).2
  refine le_trans (abs_prod_sub_prod_le (AX ∪ AY) s t hs0 hs1 ht0 ht1) ?_
  have hsum : ∑ x ∈ AX ∪ AY, |s x - t x| = ∑ x ∈ AX ∩ AY, |s x - t x| := by
    refine (Finset.sum_subset Finset.inter_subset_union ?_).symm
    intro x hx hnx
    simp only [hs, ht]
    by_cases hX : x ∈ AX
    · have hY : x ∉ AY := fun hY => hnx (Finset.mem_inter.mpr ⟨hX, hY⟩)
      simp [hX, hY]
    · have hY : x ∈ AY := by
        rcases Finset.mem_union.mp hx with h | h
        · exact absurd h hX
        · exact h
      simp [hX, hY]
  rw [hsum]
  refine Finset.sum_le_sum fun x hx => ?_
  obtain ⟨hX, hY⟩ := Finset.mem_inter.mp hx
  simp only [hs, ht, if_pos hX, if_pos hY]
  have h := one_sub_max_sub_mul_le (p x) (q x) (hp0 x) (hp1 x) (hq0 x) (hq1 x)
  rw [abs_of_nonneg h.1]
  exact h.2

/-- **Shared sites are counted by shared times** (`sandpile.tex:5601-5605`).  Each site
visited by both paths is carried to one pair of times realizing it; the map is injective
because the site is recovered from the time. -/
theorem card_inter_image_le_pairs (i j : ℕ) (X Y : ℕ → ι) :
    ((((Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y).card : ℕ) : ℝ)
      ≤ ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
          Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) := by
  classical
  have hind : ∀ r h : ℕ,
      Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)
        = if X r = Y h then (1 : ℝ) else 0 := by
    intro r h
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  have hsum : ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
      Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h)
      = (((Finset.range (i + 1) ×ˢ Finset.range (j + 1)).filter
          (fun p : ℕ × ℕ => X p.1 = Y p.2)).card : ℝ) := by
    rw [← Finset.sum_product']
    rw [Finset.sum_congr rfl (fun p _ => hind p.1 p.2)]
    rw [Finset.sum_boole]
  rw [hsum]
  have hXex : ∀ z : ι, ∃ r : ℕ,
      (z ∈ (Finset.range (i + 1)).image X → r ∈ Finset.range (i + 1) ∧ X r = z) := by
    intro z
    by_cases hz : z ∈ (Finset.range (i + 1)).image X
    · obtain ⟨r, hr, hrz⟩ := Finset.mem_image.mp hz
      exact ⟨r, fun _ => ⟨hr, hrz⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  have hYex : ∀ z : ι, ∃ h : ℕ,
      (z ∈ (Finset.range (j + 1)).image Y → h ∈ Finset.range (j + 1) ∧ Y h = z) := by
    intro z
    by_cases hz : z ∈ (Finset.range (j + 1)).image Y
    · obtain ⟨h, hh, hhz⟩ := Finset.mem_image.mp hz
      exact ⟨h, fun _ => ⟨hh, hhz⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose rz hrz using hXex
  choose hz hhz using hYex
  have hcard : ((Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y).card
      ≤ ((Finset.range (i + 1) ×ˢ Finset.range (j + 1)).filter
          (fun p : ℕ × ℕ => X p.1 = Y p.2)).card := by
    refine Finset.card_le_card_of_injOn (fun z => (rz z, hz z)) ?_ ?_
    · intro z hzmem
      obtain ⟨hzX, hzY⟩ := Finset.mem_inter.mp hzmem
      obtain ⟨hr1, hr2⟩ := hrz z hzX
      obtain ⟨hh1, hh2⟩ := hhz z hzY
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr1, hh1⟩, ?_⟩
      simp only
      rw [hr2, hh2]
    · intro z1 hz1 z2 hz2 heq
      have h1 := Finset.mem_coe.mp hz1
      have h2 := Finset.mem_coe.mp hz2
      obtain ⟨_, hr1⟩ := hrz z1 (Finset.mem_inter.mp h1).1
      obtain ⟨_, hr2⟩ := hrz z2 (Finset.mem_inter.mp h2).1
      have : rz z1 = rz z2 := congrArg Prod.fst heq
      rw [← hr1, ← hr2, this]
  exact_mod_cast hcard


/-- **Step 3 in the shape `eq:dgt4-positive-path-covariance` needs.**  With every threshold
at most `c`, the two products differ by at most `2c` times the number of shared time pairs. -/
theorem abs_prod_joint_sub_prod_sep_le_count (i j : ℕ) (X Y : ℕ → ι) (p q : ι → ℝ) (c : ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1)
    (hc0 : 0 ≤ c) (hpc : ∀ x, p x ≤ c) (hqc : ∀ x, q x ≤ c) :
    |(∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
        (if x ∈ (Finset.range (i + 1)).image X then
            (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
          else 1 - q x))
        - (∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)) *
            ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x)|
      ≤ 2 * c * ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
          Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) := by
  classical
  refine le_trans (abs_prod_joint_sub_prod_sep_le ((Finset.range (i + 1)).image X)
    ((Finset.range (j + 1)).image Y) p q hp0 hp1 hq0 hq1) ?_
  have hstep : ∑ x ∈ (Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y,
      (p x + q x)
      ≤ ∑ _x ∈ (Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y, 2 * c :=
    Finset.sum_le_sum fun x _ => by linarith [hpc x, hqc x]
  have hconst : ∑ _x ∈ (Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y,
      (2 * c)
      = ((((Finset.range (i + 1)).image X ∩ (Finset.range (j + 1)).image Y).card : ℕ) : ℝ)
        * (2 * c) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcount := card_inter_image_le_pairs i j X Y
  have hfinal : ((((Finset.range (i + 1)).image X ∩
        (Finset.range (j + 1)).image Y).card : ℕ) : ℝ) * (2 * c)
      ≤ 2 * c * ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
          Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcount (by linarith)
  linarith [hstep, hconst.le, hconst.ge, hfinal]

end Sandpile
