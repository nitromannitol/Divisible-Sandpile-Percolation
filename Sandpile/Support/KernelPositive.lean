import Sandpile.Support.ContParity

/-!
# Positivity of the lattice transition kernel

Positivity of the lattice transition kernel: the walk reaches `y` from `x` in `n` steps with
positive probability (`heatKernel_pos`) exactly when `n` is at least the path distance
`pathDist x y = ∑_i|x_i-y_i|` and has its parity (`sameParity_iff_pathDist`).

This is the criterion the local central limit theorem of `sandpile.tex:1145-1161` needs in order
to be applied. That statement is a bound on the admissible triples, those with `p_ℓ(x,y)>0`, and
the double time sum of `prop:weighted-membrane-limit` runs instead over the parity class of the
total time, which is where `p_ℓ(x,y)` can be positive. The two agree once `ℓ` exceeds the path
distance, and in the application `ℓ ≥ δR²` while the path distance is `O(R)`, so they agree for
every large scale (`heatKernel_pos_of_sameParity`). The paper does not record the criterion; it is
the standard fact that the simple random walk on `ℤ^d` connects two sites in any admissible number
of steps.
-/

open Filter Topology

namespace Sandpile

variable {d : ℕ}

/-! ### The path distance -/

/-- The path distance `∑_i|x_i-y_i|`, the least number of nearest-neighbour steps
joining `x` to `y`. -/
def pathDist (x y : Site d) : ℕ := ∑ i, (x i - y i).natAbs

/-- The path distance from a site to itself is `0`. -/
theorem pathDist_self (x : Site d) : pathDist x x = 0 := by simp [pathDist]

/-- A vanishing path distance forces the two sites to be equal, since each coordinate's
absolute difference is then `0`. -/
theorem eq_of_pathDist_eq_zero {x y : Site d} (h : pathDist x y = 0) : x = y := by
  funext i
  have hi : (x i - y i).natAbs = 0 :=
    (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
  omega

/-- Stepping `x` one unit towards `y` along a coordinate `i` where `x i > y i` decreases the
path distance to `y` by exactly `1`. -/
theorem pathDist_sub_unit {x y : Site d} {i : Fin d} (h : y i < x i) :
    pathDist (x - Sandpile.unit i) y + 1 = pathDist x y := by
  classical
  unfold pathDist
  rw [← Finset.add_sum_erase _ (fun j => ((x - Sandpile.unit i) j - y j).natAbs)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => (x j - y j).natAbs) (Finset.mem_univ i)]
  have hterm : ((x - Sandpile.unit i) i - y i).natAbs + 1 = (x i - y i).natAbs := by
    have hx : (x - Sandpile.unit i) i = x i - 1 := by simp [Sandpile.unit]
    rw [hx]
    omega
  have herase : ∑ j ∈ Finset.univ.erase i, ((x - Sandpile.unit i) j - y j).natAbs
      = ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hx : (x - Sandpile.unit i) j = x j := by
      simp [Sandpile.unit, Pi.single_eq_of_ne hne]
    rw [hx]
  omega

/-- Stepping `x` one unit towards `y` along a coordinate `i` where `x i < y i` decreases the
path distance to `y` by exactly `1`. -/
theorem pathDist_add_unit {x y : Site d} {i : Fin d} (h : x i < y i) :
    pathDist (x + Sandpile.unit i) y + 1 = pathDist x y := by
  classical
  unfold pathDist
  rw [← Finset.add_sum_erase _ (fun j => ((x + Sandpile.unit i) j - y j).natAbs)
      (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => (x j - y j).natAbs) (Finset.mem_univ i)]
  have hterm : ((x + Sandpile.unit i) i - y i).natAbs + 1 = (x i - y i).natAbs := by
    have hx : (x + Sandpile.unit i) i = x i + 1 := by simp [Sandpile.unit]
    rw [hx]
    omega
  have herase : ∑ j ∈ Finset.univ.erase i, ((x + Sandpile.unit i) j - y j).natAbs
      = ∑ j ∈ Finset.univ.erase i, (x j - y j).natAbs := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hx : (x + Sandpile.unit i) j = x j := by
      simp [Sandpile.unit, Pi.single_eq_of_ne hne]
    rw [hx]
  omega

/-- The path distance from `x` to a neighbour obtained by adding a unit vector is `1`. -/
theorem pathDist_add_unit_eq_one (x : Site d) (i : Fin d) :
    pathDist (x + Sandpile.unit i) x = 1 := by
  classical
  unfold pathDist
  rw [← Finset.add_sum_erase _ (fun j => ((x + Sandpile.unit i) j - x j).natAbs)
      (Finset.mem_univ i)]
  have hterm : ((x + Sandpile.unit i) i - x i).natAbs = 1 := by
    have hx : (x + Sandpile.unit i) i = x i + 1 := by simp [Sandpile.unit]
    rw [hx]; omega
  have herase : ∑ j ∈ Finset.univ.erase i, ((x + Sandpile.unit i) j - x j).natAbs = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hx : (x + Sandpile.unit i) j = x j := by
      simp [Sandpile.unit, Pi.single_eq_of_ne hne]
    rw [hx]; omega
  omega

/-! ### The parity of the path distance -/

/-- Two integer-valued families agreeing coordinatewise mod `2` have sums agreeing mod `2`. -/
theorem sum_emod_two (f g : Fin d → ℤ) (h : ∀ i, f i % 2 = g i % 2) :
    (∑ i, f i) % 2 = (∑ i, g i) % 2 := by
  have hex : ∀ i, ∃ k : ℤ, f i = g i + 2 * k := by
    intro i
    have hi := h i
    have h2 : (2:ℤ) ∣ (f i - g i) := by omega
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, by omega⟩
  choose k hk using hex
  have hsum : ∑ i, f i = ∑ i, g i + 2 * ∑ i, k i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hk i
  omega

/-- The path distance's parity is the parity of the difference of coordinate sums, since
`sum_emod_two` transfers the coordinatewise identity `|x_i - y_i| ≡ x_i - y_i (mod 2)`. -/
theorem pathDist_emod_two (x y : Site d) :
    ((pathDist x y : ℕ) : ℤ) % 2 = ((∑ i, x i) - (∑ i, y i)) % 2 := by
  have hcast : ((pathDist x y : ℕ) : ℤ) = ∑ i, (((x i - y i).natAbs : ℕ) : ℤ) := by
    unfold pathDist
    push_cast
    ring
  have hdiff : (∑ i, x i) - (∑ i, y i) = ∑ i, (x i - y i) := by
    rw [Finset.sum_sub_distrib]
  rw [hcast, hdiff]
  refine sum_emod_two _ _ fun i => ?_
  rcases Int.natAbs_eq (x i - y i) with h | h <;> omega

/-! ### One step of the kernel -/

/-- One step of the kernel towards `x + unit i` dominates `1/(2d)` of the `n`-step kernel value
there, by isolating that term from the transition-kernel averaging sum. -/
theorem heatKernel_succ_ge_add (hd : 1 ≤ d) (n : ℕ) (x y : Site d) (i : Fin d) :
    Sandpile.heatKernel d n (x + unit i) y / (2 * d) ≤ Sandpile.heatKernel d (n + 1) x y := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnn : ∀ j : Fin d, (0 : ℝ) ≤
      Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y :=
    fun j => add_nonneg (heatKernel_nonneg _ _ _) (heatKernel_nonneg _ _ _)
  have hsingle := Finset.single_le_sum
    (f := fun j : Fin d =>
      Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y)
    (fun j _ => hnn j) (Finset.mem_univ i)
  have hstep : Sandpile.heatKernel d n (x + unit i) y
      ≤ ∑ j : Fin d,
        (Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y) := by
    refine le_trans ?_ hsingle
    have := heatKernel_nonneg n (x - unit i) y
    linarith
  show Sandpile.heatKernel d n (x + unit i) y / (2 * d) ≤ _ / (2 * (d : ℝ))
  gcongr

/-- One step of the kernel towards `x - unit i` dominates `1/(2d)` of the `n`-step kernel value
there, the mirror image of `heatKernel_succ_ge_add`. -/
theorem heatKernel_succ_ge_sub (hd : 1 ≤ d) (n : ℕ) (x y : Site d) (i : Fin d) :
    Sandpile.heatKernel d n (x - unit i) y / (2 * d) ≤ Sandpile.heatKernel d (n + 1) x y := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnn : ∀ j : Fin d, (0 : ℝ) ≤
      Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y :=
    fun j => add_nonneg (heatKernel_nonneg _ _ _) (heatKernel_nonneg _ _ _)
  have hsingle := Finset.single_le_sum
    (f := fun j : Fin d =>
      Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y)
    (fun j _ => hnn j) (Finset.mem_univ i)
  have hstep : Sandpile.heatKernel d n (x - unit i) y
      ≤ ∑ j : Fin d,
        (Sandpile.heatKernel d n (x + unit j) y + Sandpile.heatKernel d n (x - unit j) y) := by
    refine le_trans ?_ hsingle
    have := heatKernel_nonneg n (x + unit i) y
    linarith
  show Sandpile.heatKernel d n (x - unit i) y / (2 * d) ≤ _ / (2 * (d : ℝ))
  gcongr

/-! ### Positivity -/

/-- **Positivity of the transition kernel.**  The walk joins `x` to `y` in `n`
steps with positive probability as soon as `n` is at least the path distance and
has its parity: move one step towards `y` while the two differ, and take a step
out and back once they agree. -/
theorem heatKernel_pos (hd : 1 ≤ d) :
    ∀ (n : ℕ) (x y : Site d), pathDist x y ≤ n → pathDist x y % 2 = n % 2 →
      0 < Sandpile.heatKernel d n x y := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  intro n
  induction n with
  | zero =>
      intro x y hle hpar
      have h0 : pathDist x y = 0 := Nat.le_zero.mp hle
      have hxy : x = y := eq_of_pathDist_eq_zero h0
      subst hxy
      show (0 : ℝ) < (if x = x then (1 : ℝ) else 0)
      simp
  | succ n ih =>
      intro x y hle hpar
      by_cases hxy : x = y
      · subst hxy
        have h0 : pathDist x x = 0 := pathDist_self x
        have hstep : pathDist (x + unit ⟨0, hd⟩) x = 1 := pathDist_add_unit_eq_one x ⟨0, hd⟩
        have hpos := ih (x + unit ⟨0, hd⟩) x (by omega) (by omega)
        have hge := heatKernel_succ_ge_add hd n x x ⟨0, hd⟩
        have hq : (0:ℝ) < Sandpile.heatKernel d n (x + unit ⟨0, hd⟩) x / (2 * d) := by positivity
        linarith
      · have hne : pathDist x y ≠ 0 := fun h => hxy (eq_of_pathDist_eq_zero h)
        have hex : ∃ i : Fin d, (x i - y i).natAbs ≠ 0 := by
          by_contra hc
          have hc' : ∀ i : Fin d, (x i - y i).natAbs = 0 := by
            intro i
            by_contra h
            exact hc ⟨i, h⟩
          exact hne (Finset.sum_eq_zero fun i _ => hc' i)
        obtain ⟨i, hi⟩ := hex
        have hnei : x i ≠ y i := fun h => hi (by omega)
        rcases lt_or_gt_of_ne hnei with hlt | hgt
        · have hstep := pathDist_add_unit (x := x) (y := y) (i := i) hlt
          have hpos := ih (x + unit i) y (by omega) (by omega)
          have hge := heatKernel_succ_ge_add hd n x y i
          have hq : (0:ℝ) < Sandpile.heatKernel d n (x + unit i) y / (2 * d) := by positivity
          linarith
        · have hstep := pathDist_sub_unit (x := x) (y := y) (i := i) hgt
          have hpos := ih (x - unit i) y (by omega) (by omega)
          have hge := heatKernel_succ_ge_sub hd n x y i
          have hq : (0:ℝ) < Sandpile.heatKernel d n (x - unit i) y / (2 * d) := by positivity
          linarith

/-! ### The two parity conditions agree -/

/-- The parity condition of `Sandpile.Support.SameParity`, which is what a
positive transition probability forces, is the parity of the path distance. -/
theorem sameParity_iff_pathDist (n : ℕ) (x y : Site d) :
    Sandpile.Support.SameParity n x y ↔ pathDist x y % 2 = n % 2 := by
  have h := pathDist_emod_two x y
  unfold Sandpile.Support.SameParity
  omega

/-- The path distance is at most the dimension times the box distance. -/
theorem pathDist_le_mul_boxDist (x y : Site d) : pathDist x y ≤ d * boxDist x y := by
  classical
  have hle : ∀ i : Fin d, (x i - y i).natAbs ≤ boxDist x y := fun i =>
    Finset.le_sup (f := fun j => (x j - y j).natAbs) (Finset.mem_univ i)
  calc pathDist x y = ∑ i : Fin d, (x i - y i).natAbs := rfl
    _ ≤ ∑ _i : Fin d, boxDist x y := Finset.sum_le_sum fun i _ => hle i
    _ = d * boxDist x y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **The transition kernel is positive on the parity class beyond the path
distance.**  This is the form in which the hypothesis `0 < p_ℓ(x,y)` of the local
central limit theorem of `sandpile.tex:1145-1161` is discharged. -/
theorem heatKernel_pos_of_sameParity (hd : 1 ≤ d) (n : ℕ) (x y : Site d)
    (hle : pathDist x y ≤ n) (hp : Sandpile.Support.SameParity n x y) :
    0 < Sandpile.heatKernel d n x y :=
  heatKernel_pos hd n x y hle ((sameParity_iff_pathDist n x y).mp hp)

end Sandpile
