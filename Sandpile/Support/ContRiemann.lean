/-
The sum of squares of the coefficients of `prop:weighted-membrane-limit`
(`sandpile.tex:4717-4731`) written out as a double space sum against a double
time sum, and the crude bound on the contribution of a block of times.

The convergence half of the proposition was reduced in
`Sandpile.Support.ContWeightedLimit` to the single limit

  `lim_R ∑_z a_R(z)^2 = Var(𝒢(φ)) / Var(ζ(0))`,

which is the paper's "the local central limit theorem, followed by a Riemann-sum
argument, gives `Var(𝓕_R(φ)) → Var(𝓖(φ))`".  This file writes the left side of
that limit in the form the Riemann-sum argument works with,

  `∑_z a_R(z)^2 = R^{d-4} ∑_{x,x'} m_R(x) m_R(x')
                    ∑_{a,b<⌊R^2T⌋} q(a/R^2) q(b/R^2) p_{a+b}(x,x')`,

with `m_R(x) = ∫_{cell(x)} φ`, and proves the estimate that removes the block of
small times from it: for any set `A` of time pairs,

  `|R^{d-4} ∑_{(a,b)∈A} q(a/R^2)q(b/R^2) ∑_{x,x'} m_R(x)m_R(x')p_{a+b}(x,x')|
     ≤ |A| ‖q‖_∞^2 ‖φ‖_∞ ‖φ‖_1 R^{-4}`,

which at `A = {(a,b) : a+b < δR^2}`, where `|A| ≤ δ^2R^4`, is
`δ^2 ‖q‖_∞^2 ‖φ‖_∞ ‖φ‖_1`.  Only the total mass one of the transition kernel,
the cell bound `|m_R(x)| ≤ ‖φ‖_∞ R^{-d}` and the disjointness of the cells are
used, so the estimate holds in every dimension and needs no kernel asymptotic.
-/
import Sandpile.Support.ContWeightedLimit

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The sum of squares of the coefficients, written out -/

/-- The coefficients vanish outside `coeffBox`, so the unordered sum of their
squares is the finite sum over that box. -/
theorem tsum_pairCoeff_sq_eq_sum_coeffBox (R L T : ℝ) (q : ℕ → ℝ) (φ : Space d → ℝ) :
    ∑' z : Site d, pairCoeff d R q ⌊R ^ 2 * T⌋₊ φ (supportBox d R L) z ^ 2
      = ∑ z ∈ coeffBox d R L T,
        pairCoeff d R q ⌊R ^ 2 * T⌋₊ φ (supportBox d R L) z ^ 2 := by
  refine tsum_eq_sum ?_
  intro z hz
  have hfar : ∀ x ∈ supportBox d R L, ⌊R ^ 2 * T⌋₊ < Sandpile.boxDist x z := by
    intro x hx
    have h1 : Sandpile.boxDist (0 : Site d) x ≤ ⌈|R| * L⌉₊ + 1 :=
      Sandpile.mem_boxFinset_iff.mp hx
    have h2 : ¬ (Sandpile.boxDist (0 : Site d) z ≤ ⌈|R| * L⌉₊ + 1 + ⌊R ^ 2 * T⌋₊) :=
      fun h => hz (Sandpile.mem_boxFinset h)
    have h3 := Sandpile.boxDist_trans (0 : Site d) x z
    omega
  rw [pairCoeff_eq_zero_of_far R q _ φ (supportBox d R L) z hfar]
  ring

/-- **The sum of squares of the coefficients of the pairing, written out.**  This
is the left side of the limit `Var(𝓕_R(φ)) → Var(𝓖(φ))` of
`sandpile.tex:4719-4724`, divided by the scenery variance: a double sum over the
cells of the mesh against the double time sum of transition probabilities. -/
theorem sum_scaledCoeff_sq_eq {R : ℝ} (hR : 0 < R) (L T : ℝ) (q : ℝ → ℝ)
    (φ : Space d → ℝ) :
    ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2
      = R ^ ((d : ℝ) - 4) *
        ∑ p ∈ (supportBox d R L) ×ˢ (supportBox d R L),
          cellMass R φ p.1 * cellMass R φ p.2 *
            ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
              q ((a : ℝ) / R ^ 2) * q ((b : ℝ) / R ^ 2) *
                Sandpile.heatKernel d (a + b) p.1 p.2 := by
  have hpow : (R ^ (((d : ℝ) - 4) / 2)) ^ (2 : ℕ) = R ^ ((d : ℝ) - 4) := by
    rw [← Real.rpow_natCast (R ^ (((d : ℝ) - 4) / 2)) 2, ← Real.rpow_mul hR.le]
    norm_num
  have hstep : ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2
      = (R ^ (((d : ℝ) - 4) / 2)) ^ (2 : ℕ) *
        ∑ z ∈ coeffBox d R L T,
          pairCoeff d R (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊ φ
            (supportBox d R L) z ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [scaledCoeff, mul_pow]
  rw [hstep, hpow,
    ← tsum_pairCoeff_sq_eq_sum_coeffBox R L T (fun j => q ((j : ℝ) / R ^ 2)) φ,
    tsum_pairCoeff_sq R (fun j => q ((j : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊ φ (supportBox d R L)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tsum_weightedKernel_mul_weightedKernel (fun j => q ((j : ℝ) / R ^ 2))
    ⌊R ^ 2 * T⌋₊ p.1 p.2]

/-- The double space sum and the double time sum may be exchanged. -/
theorem sum_space_time_comm (s : Finset (Site d)) (m : Site d → ℝ) (q : ℕ → ℝ) (N : ℕ)
    (K : ℕ → Site d → Site d → ℝ) :
    ∑ p ∈ s ×ˢ s, m p.1 * m p.2 *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, q a * q b * K (a + b) p.1 p.2
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          q a * q b * ∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y := by
  have e1 : ∀ x y : Site d, m x * m y *
      (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, q a * q b * K (a + b) x y)
      = ∑ r ∈ (Finset.range N) ×ˢ (Finset.range N),
          q r.1 * q r.2 * (m x * m y * K (r.1 + r.2) x y) := by
    intro x y
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ a b : ℕ, q a * q b * (∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y)
      = ∑ p ∈ s ×ˢ s, q a * q b * (m p.1 * m p.2 * K (a + b) p.1 p.2) := by
    intro a b
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  have hR : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        q a * q b * ∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y)
      = ∑ r ∈ (Finset.range N) ×ˢ (Finset.range N), ∑ p ∈ s ×ˢ s,
          q r.1 * q r.2 * (m p.1 * m p.2 * K (r.1 + r.2) p.1 p.2) := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e2 a b
  rw [hR, Finset.sum_congr rfl fun p (_ : p ∈ s ×ˢ s) => e1 p.1 p.2]
  exact Finset.sum_comm

/-! ### The crude bound on a block of times -/

/-- A finite sum of the transition kernel in its second variable is at most one. -/
theorem sum_heatKernel_le_one (hd : 1 ≤ d) (n : ℕ) (x : Site d)
    (s : Finset (Site d)) : ∑ y ∈ s, Sandpile.heatKernel d n x y ≤ 1 := by
  have hsum : Summable (fun y : Site d => Sandpile.heatKernel d n x y) := by
    simpa using summable_heatKernel_mul n x (fun _ => (1 : ℝ))
  rw [← tsum_heatKernel hd n x]
  exact hsum.sum_le_tsum s (fun y _ => heatKernel_nonneg n x y)

/-- The crude bound on a double space sum against the transition kernel: the
kernel has total mass one, so the sum is at most the sup-norm of the weights
times their total mass. -/
theorem abs_sum_double_heatKernel_le (hd : 1 ≤ d) (n : ℕ) (s : Finset (Site d))
    (m : Site d → ℝ) (K : ℝ) (hK : ∀ x, |m x| ≤ K) (hK0 : 0 ≤ K) :
    |∑ x ∈ s, ∑ y ∈ s, m x * m y * Sandpile.heatKernel d n x y| ≤ K * ∑ x ∈ s, |m x| := by
  calc |∑ x ∈ s, ∑ y ∈ s, m x * m y * Sandpile.heatKernel d n x y|
      ≤ ∑ x ∈ s, |∑ y ∈ s, m x * m y * Sandpile.heatKernel d n x y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ s, |m x| * K := by
        refine Finset.sum_le_sum fun x _ => ?_
        calc |∑ y ∈ s, m x * m y * Sandpile.heatKernel d n x y|
            ≤ ∑ y ∈ s, |m x * m y * Sandpile.heatKernel d n x y| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ y ∈ s, |m x| * |m y| * Sandpile.heatKernel d n x y := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg n x y)]
          _ ≤ ∑ y ∈ s, |m x| * K * Sandpile.heatKernel d n x y := by
              refine Finset.sum_le_sum fun y _ => ?_
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hK y) (abs_nonneg (m x)))
                (heatKernel_nonneg n x y)
          _ = |m x| * K * ∑ y ∈ s, Sandpile.heatKernel d n x y := by rw [Finset.mul_sum]
          _ ≤ |m x| * K * 1 :=
              mul_le_mul_of_nonneg_left (sum_heatKernel_le_one hd n x s)
                (mul_nonneg (abs_nonneg (m x)) hK0)
          _ = |m x| * K := by ring
    _ = K * ∑ x ∈ s, |m x| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- The crude bound on the contribution of a block of time pairs. -/
theorem abs_time_double_le (hd : 1 ≤ d) (s : Finset (Site d)) (m : Site d → ℝ)
    (K : ℝ) (hK : ∀ x, |m x| ≤ K) (hK0 : 0 ≤ K) (M : ℝ) (hM : ∑ x ∈ s, |m x| ≤ M)
    (w : ℕ × ℕ → ℝ) (Q : ℝ) (hQ : ∀ p, |w p| ≤ Q) (hQ0 : 0 ≤ Q)
    (A : Finset (ℕ × ℕ)) :
    |∑ p ∈ A, w p * ∑ x ∈ s, ∑ y ∈ s, m x * m y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ (A.card : ℝ) * (Q * (K * M)) := by
  have hKM : (0 : ℝ) ≤ K * M :=
    mul_nonneg hK0 (le_trans (Finset.sum_nonneg fun x _ => abs_nonneg (m x)) hM)
  calc |∑ p ∈ A, w p *
        ∑ x ∈ s, ∑ y ∈ s, m x * m y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ ∑ p ∈ A, |w p *
          ∑ x ∈ s, ∑ y ∈ s, m x * m y * Sandpile.heatKernel d (p.1 + p.2) x y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ A, Q * (K * M) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [abs_mul]
        refine mul_le_mul (hQ p) ?_ (abs_nonneg _) hQ0
        exact le_trans (abs_sum_double_heatKernel_le hd (p.1 + p.2) s m K hK hK0)
          (mul_le_mul_of_nonneg_left hM hK0)
    _ = (A.card : ℝ) * (Q * (K * M)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The cells are disjoint, so the total mass a test function puts on a finite
family of them is at most its `L¹` norm. -/
theorem sum_abs_cellMass_le (R : ℝ) (φ : Space d → ℝ) (hφ : Integrable φ)
    (s : Finset (Site d)) : ∑ x ∈ s, |cellMass R φ x| ≤ ∫ z, |φ z| := by
  have habs : Integrable (fun z : Space d => |φ z|) := hφ.abs
  have h1 : ∀ x ∈ s, |cellMass R φ x| ≤ ∫ z in cell d R x, |φ z| := by
    intro x _
    exact MeasureTheory.abs_integral_le_integral_abs
  calc ∑ x ∈ s, |cellMass R φ x|
      ≤ ∑ x ∈ s, ∫ z in cell d R x, |φ z| := Finset.sum_le_sum h1
    _ = ∫ z in ⋃ x ∈ s, cell d R x, |φ z| := by
        rw [MeasureTheory.integral_biUnion_finset s
          (fun x _ => measurableSet_cell d R x)
          (fun x _ y _ hxy => cell_disjoint hxy)
          (fun x _ => habs.integrableOn)]
    _ ≤ ∫ z, |φ z| :=
        MeasureTheory.setIntegral_le_integral habs
          (Filter.Eventually.of_forall fun z => abs_nonneg (φ z))

theorem card_time_block_le (N M : ℕ) :
    (((Finset.range N) ×ˢ (Finset.range N)).filter (fun p : ℕ × ℕ => p.1 + p.2 < M)).card
      ≤ M * M := by
  have hsub : (((Finset.range N) ×ˢ (Finset.range N)).filter
      (fun p : ℕ × ℕ => p.1 + p.2 < M)) ⊆ (Finset.range M) ×ˢ (Finset.range M) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    omega
  calc (((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => p.1 + p.2 < M)).card
      ≤ ((Finset.range M) ×ˢ (Finset.range M)).card := Finset.card_le_card hsub
    _ = M * M := by simp

theorem abs_scaled_time_block_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (L : ℝ)
    (q : ℝ → ℝ) (Q : ℝ) (hQ : ∀ r : ℝ, |q r| ≤ Q) (hQ0 : 0 ≤ Q)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C)
    (A : Finset (ℕ × ℕ)) :
    |R ^ ((d : ℝ) - 4) * ∑ p ∈ A, (q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)) *
        ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
          cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ (A.card : ℝ) * ((Q * Q) * (C * ∫ z, |φ z|)) * R ^ (-4 : ℝ) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hinv : (0 : ℝ) ≤ R⁻¹ ^ d := pow_nonneg (inv_pos.mpr hR).le d
  have hK0 : (0 : ℝ) ≤ C * R⁻¹ ^ d := mul_nonneg hC0 hinv
  have hpre : (0 : ℝ) < R ^ ((d : ℝ) - 4) := Real.rpow_pos_of_pos hR _
  have hw : ∀ p : ℕ × ℕ, |q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)| ≤ Q * Q := by
    intro p
    rw [abs_mul]
    exact mul_le_mul (hQ _) (hQ _) (abs_nonneg _) hQ0
  have hmain := abs_time_double_le hd (supportBox d R L) (cellMass R φ)
    (C * R⁻¹ ^ d) (fun x => abs_cellMass_le hR φ C hC x) hK0
    (∫ z, |φ z|) (sum_abs_cellMass_le R φ hφ _)
    (fun p => q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)) (Q * Q) hw
    (mul_nonneg hQ0 hQ0) A
  have hexp : R ^ ((d : ℝ) - 4) * (R⁻¹ ^ d) = R ^ (-4 : ℝ) := by
    have h1 : (R⁻¹ : ℝ) ^ d = R ^ (-(d : ℝ)) := by
      rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
    rw [h1, ← Real.rpow_add hR]
    congr 1
    ring
  rw [abs_mul, abs_of_pos hpre]
  calc R ^ ((d : ℝ) - 4) * |∑ p ∈ A, (q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)) *
        ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
          cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ R ^ ((d : ℝ) - 4) * ((A.card : ℝ) * ((Q * Q) * ((C * R⁻¹ ^ d) * ∫ z, |φ z|))) :=
        mul_le_mul_of_nonneg_left hmain hpre.le
    _ = (A.card : ℝ) * ((Q * Q) * (C * ∫ z, |φ z|)) * (R ^ ((d : ℝ) - 4) * R⁻¹ ^ d) := by
        ring
    _ = (A.card : ℝ) * ((Q * Q) * (C * ∫ z, |φ z|)) * R ^ (-4 : ℝ) := by rw [hexp]


/-- **The double cell sum against a lattice kernel is a double integral.**  Both
space sums of the previous display are Riemann sums for the mesh `R^{-1}ℤ^d`,
and this is the exact identity behind that: the kernel is read at the embedded
sites, and no error term appears. -/
theorem sum_double_cellMass_eq (R : ℝ) (φ : Space d → ℝ) (hφ : Integrable φ)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s)
    (h : Site d → Site d → ℝ) :
    ∑ x ∈ s, ∑ y ∈ s, cellMass R φ x * cellMass R φ y * h x y
      = ∫ u : Space d,
          (∫ v : Space d, h (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v) * φ u := by
  have inner : ∀ x : Site d, ∑ y ∈ s, h x y * cellMass R φ y
      = ∫ v : Space d, h x (fun i => ⌊R * v i⌋) * φ v :=
    fun x => (latticePairing_eq_sum R (h x) φ hφ s hs).symm
  have outer : ∑ x ∈ s, (∑ y ∈ s, h x y * cellMass R φ y) * cellMass R φ x
      = ∫ u : Space d, (∑ y ∈ s, h (fun i => ⌊R * u i⌋) y * cellMass R φ y) * φ u :=
    (latticePairing_eq_sum R (fun x => ∑ y ∈ s, h x y * cellMass R φ y) φ hφ s hs).symm
  calc ∑ x ∈ s, ∑ y ∈ s, cellMass R φ x * cellMass R φ y * h x y
      = ∑ x ∈ s, (∑ y ∈ s, h x y * cellMass R φ y) * cellMass R φ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∫ u : Space d, (∑ y ∈ s, h (fun i => ⌊R * u i⌋) y * cellMass R φ y) * φ u := outer
    _ = ∫ u : Space d,
          (∫ v : Space d, h (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v) * φ u := by
        simp_rw [inner]

/-! ### The mesh -/

/-- The mesh point of `x` is within `1/R` of `x`: the mesh `R^{-1}ℤ` has spacing
`R^{-1}`, which is the space mesh of the Riemann sum. -/
theorem abs_floor_div_sub_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |(⌊R * x⌋ : ℝ) / R - x| ≤ 1 / R := by
  have h1 : ((⌊R * x⌋ : ℝ)) ≤ R * x := Int.floor_le (R * x)
  have h2 : R * x - 1 < ((⌊R * x⌋ : ℝ)) := Int.sub_one_lt_floor (R * x)
  have hne : R ≠ 0 := ne_of_gt hR
  have key : (⌊R * x⌋ : ℝ) / R - x = ((⌊R * x⌋ : ℝ) - R * x) / R := by field_simp
  rw [key, abs_div, abs_of_pos hR, div_le_div_iff_of_pos_right hR]
  rw [abs_le]
  constructor <;> nlinarith

/-- The cells above the support carry the whole mass of the test function. -/
theorem sum_cellMass_eq_integral (R : ℝ) (φ : Space d → ℝ) (hφ : Integrable φ)
    (s : Finset (Site d)) (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    ∑ x ∈ s, cellMass R φ x = ∫ z, φ z := by
  have h := latticePairing_eq_sum R (fun _ => (1 : ℝ)) φ hφ s hs
  simp only [one_mul] at h
  rw [← h]
  show ∫ z : Space d, (1 : ℝ) * φ z = ∫ z, φ z
  simp

/-- **The block of small times contributes at most `δ²` times a constant,
uniformly in `R`.**  The pairs of times below `δR²` number at most `δ²R⁴`, and
each block of time pairs contributes at most its cardinality times `R^{-4}`
times a constant, so the whole block is `O(δ²)` with no kernel asymptotic and no
Gaussian bound.  This is the cut that removes the small times from the Riemann
sum of `sandpile.tex:4719-4724`. -/
theorem abs_small_time_block_le (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (L T : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (q : ℝ → ℝ) (Q : ℝ) (hQ : ∀ r : ℝ, |q r| ≤ Q) (hQ0 : 0 ≤ Q)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) :
    |R ^ ((d : ℝ) - 4) *
        ∑ p ∈ ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
          (fun p : ℕ × ℕ => p.1 + p.2 < ⌊δ * R ^ 2⌋₊),
          (q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)) *
            ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
              cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ δ ^ 2 * ((Q * Q) * (C * ∫ z, |φ z|)) := by
  classical
  set A := ((Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊)).filter
    (fun p : ℕ × ℕ => p.1 + p.2 < ⌊δ * R ^ 2⌋₊) with hA
  have hbase := abs_scaled_time_block_le hd hR L q Q hQ hQ0 φ hφ C hC A
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hL1 : (0 : ℝ) ≤ ∫ z, |φ z| :=
    MeasureTheory.integral_nonneg fun z => abs_nonneg (φ z)
  have hK0 : (0 : ℝ) ≤ (Q * Q) * (C * ∫ z, |φ z|) :=
    mul_nonneg (mul_nonneg hQ0 hQ0) (mul_nonneg hC0 hL1)
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hcard : (A.card : ℝ) ≤ δ ^ 2 * R ^ 4 := by
    have h1 : A.card ≤ ⌊δ * R ^ 2⌋₊ * ⌊δ * R ^ 2⌋₊ :=
      card_time_block_le ⌊R ^ 2 * T⌋₊ ⌊δ * R ^ 2⌋₊
    have h2 : ((⌊δ * R ^ 2⌋₊ : ℕ) : ℝ) ≤ δ * R ^ 2 := Nat.floor_le (by positivity)
    have h3 : (0 : ℝ) ≤ ((⌊δ * R ^ 2⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (A.card : ℝ) ≤ ((⌊δ * R ^ 2⌋₊ * ⌊δ * R ^ 2⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((⌊δ * R ^ 2⌋₊ : ℕ) : ℝ) * ((⌊δ * R ^ 2⌋₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (δ * R ^ 2) * (δ * R ^ 2) := by nlinarith
      _ = δ ^ 2 * R ^ 4 := by ring
  have hpow : R ^ (-4 : ℝ) = (R ^ 4)⁻¹ := by
    rw [Real.rpow_neg hR.le]
    norm_num
  have hR4 : (0 : ℝ) < R ^ 4 := by positivity
  refine le_trans hbase ?_
  rw [hpow]
  have hstep : (A.card : ℝ) * ((Q * Q) * (C * ∫ z, |φ z|)) * (R ^ 4)⁻¹
      ≤ (δ ^ 2 * R ^ 4) * ((Q * Q) * (C * ∫ z, |φ z|)) * (R ^ 4)⁻¹ := by
    have := mul_le_mul_of_nonneg_right hcard hK0
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine le_trans hstep ?_
  have : (δ ^ 2 * R ^ 4) * ((Q * Q) * (C * ∫ z, |φ z|)) * (R ^ 4)⁻¹
      = δ ^ 2 * ((Q * Q) * (C * ∫ z, |φ z|)) := by
    field_simp
  rw [this]

/-- **The sum of squares of the coefficients as a double space integral against
the double time sum.**  The double space sum over the cells of the mesh is an
exact integral, so the whole quantity whose limit `prop:weighted-membrane-limit`
asks for is a double integral over `ℝ^d × ℝ^d` of the double time sum read at the
mesh sites of the two integration variables. -/
theorem sum_scaledCoeff_sq_eq_integral {R : ℝ} (hR : 0 < R) (L T : ℝ) (q : ℝ → ℝ)
    (φ : Space d → ℝ) (hint : Integrable φ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2
      = R ^ ((d : ℝ) - 4) *
        ∫ u : Space d, (∫ v : Space d,
          (∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q ((a : ℝ) / R ^ 2) * q ((b : ℝ) / R ^ 2) *
              Sandpile.heatKernel d (a + b) (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋))
            * φ v) * φ u := by
  have hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ supportBox d R L :=
    fun z hz => floor_mem_boxFinset R z (hsupp z hz)
  rw [sum_scaledCoeff_sq_eq hR L T q φ, Finset.sum_product]
  congr 1
  exact sum_double_cellMass_eq R φ hint (supportBox d R L) hs _

end Sandpile.Support
