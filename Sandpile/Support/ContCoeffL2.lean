/-
The `ℓ²` norm of the increment of the coefficient vector of the interpolated
rescaled field `Z_R^{\rm lin}`, at two arbitrary points of `[0,∞) × ℝ^d`.

`Z_R^{\rm lin}(r,w)` is the linear functional `ζ ↦ ∑_y c_{r,w}(y) ζ(y)` of
`Sandpile/Support/ContHeatPotential.lean`, and the moment bound the tightness
clause of `prop:dlt4-heat-potential-invariance` needs is a bound on
`‖c_p - c_q‖₂`.  The device that produces it uses no `ℓ²`-valued interpolation
theory: apply the interpolation itself to the SINGLE scenery `a := c_p - c_q`.
Then

  `Z_R^{\rm lin}(a; p) - Z_R^{\rm lin}(a; q) = ⟨c_p - c_q, a⟩ = ‖a‖₂²`,

while the sharp modulus of `ContInterpSpace` bounds the left side by
`K · dist(p,q)` with `K` the largest mesh increment of the scenery `a`, and that
increment is bounded by Cauchy-Schwarz against the `L²` increment of the Green
kernels, which is `exists_tsum_greenTime_sub_sq_bound` in space and the `L²`
mass of the heat kernel in time.  Dividing by `‖a‖₂` gives the bound.

The increment hypotheses of `ContInterpSpace` ask for a bound at EVERY time
index; the `L²` increment of the Green kernels in space grows with the time
index, so the first three lemmas here restate the space modulus with the bound
asked only at time indices at most `N`, which is all the interpolation at a time
`r` with `⌊R^2 r⌋ + 1 ≤ N` ever reads.
-/
import Sandpile.Support.ContInterpSpace
import Sandpile.Support.ContHeatPotential
import Sandpile.Support.ContGreenIncrementSum
import Sandpile.Support.ContPairedGradient
import Sandpile.Support.ContInterpBound
import LatticeProb.Support.ContSums

open LatticeProb

namespace Sandpile.Support

open Sandpile Sandpile.Frozen.HeatPotentialInvariance

variable {d : ℕ}

/-- The interpolated family moves by at most the largest mesh increment when its
index does, with the increment bound required only at time indices at most `N`. -/
theorem abs_sliceInterp_succ_sub_of_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ) (N : ℕ)
    (hK : ∀ k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    (a : ℕ) (ha : a + 1 ≤ N) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {t : Fin d → ℝ} (ht0 : ∀ i, 0 ≤ t i) (ht1 : ∀ i, t i ≤ 1) (b : Site d) (j : Fin d)
    (n : ℤ) :
    |sliceInterp d R ζ a s t b j (n + 1) - sliceInterp d R ζ a s t b j n| ≤ K := by
  classical
  rw [sliceInterp, sliceInterp, ← Finset.sum_sub_distrib]
  calc |∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
        ((∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
            cellValue d R ζ a s (fun i => if i = j then n + 1 else b i + (if c i then 1 else 0))
          - (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
            cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0)))|
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          |(∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s (fun i => if i = j then n + 1 else b i + (if c i then 1 else 0))
            - (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) *
              cellValue d R ζ a s (fun i => if i = j then n else b i + (if c i then 1 else 0))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin d → Bool => c j = false),
          (∏ i ∈ Finset.univ.erase j, (if c i then t i else 1 - t i)) * K := by
        refine Finset.sum_le_sum fun c _ => ?_
        have hw := prod_ite_erase_nonneg ht0 ht1 j c
        rw [← mul_sub, abs_mul, abs_of_nonneg hw]
        refine mul_le_mul_of_nonneg_left ?_ hw
        have hupd : (fun i => if i = j then n + 1 else b i + (if c i then (1:ℤ) else 0))
            = Function.update
                (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j
                ((fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j + 1) := by
          funext i
          by_cases h : i = j
          · subst h
            simp
          · rw [if_neg h, Function.update_of_ne h, if_neg h]
        rw [hupd]
        exact abs_cellValue_sub_le d R ζ K a hs0 hs1
          (hK a (by omega) (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j)
          (hK (a + 1) (by omega) (fun i => if i = j then n else b i + (if c i then (1:ℤ) else 0)) j)
    _ = K := by rw [← Finset.sum_mul, sum_filter_prod_ite_erase t j, one_mul]

/-- The interpolated field moves in one space coordinate by at most the largest
mesh increment times the displacement, with the increment bound required only at
time indices at most `N`. -/
theorem abs_linInterp_sub_coord_le_incr_of_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ) (N : ℕ)
    (hK : ∀ k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    {r : ℝ} (hr : 0 ≤ r) (hrN : ⌊R ^ 2 * r⌋₊ + 1 ≤ N)
    (w w' : Sandpile.Continuum.Space d) (j : Fin d)
    (hagree : ∀ i, i ≠ j → w i = w' i) :
    |linInterp d R ζ r w - linInterp d R ζ r w'| ≤ K * |R * w j - R * w' j| := by
  classical
  have hr2 : (0:ℝ) ≤ R ^ 2 * r := mul_nonneg (sq_nonneg R) hr
  have hs0 : (0:ℝ) ≤ R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) := by
    have := Nat.floor_le hr2
    linarith
  have hs1 : R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ) ≤ 1 := by
    have := Nat.lt_floor_add_one (R ^ 2 * r)
    linarith
  have hFeq : sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w' i - ((⌊R * w' i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w' i⌋) j
      = sliceInterp d R ζ ⌊R ^ 2 * r⌋₊
        (R ^ 2 * r - ((⌊R ^ 2 * r⌋₊ : ℕ) : ℝ))
        (fun i => R * w i - ((⌊R * w i⌋ : ℤ) : ℝ)) (fun i => ⌊R * w i⌋) j := by
    funext n
    refine sliceInterp_congr d R ζ _ _ j ?_ ?_ n
    · intro i hi
      rw [hagree i hi]
    · intro i hi
      rw [hagree i hi]
  rw [linInterp_eq_interp1_slice d R ζ r w j, linInterp_eq_interp1_slice d R ζ r w' j, hFeq]
  refine abs_interp1_sub_le_incr _ K ?_ (R * w j) (R * w' j)
  intro n
  exact abs_sliceInterp_succ_sub_of_le d R ζ K N hK _ hrN hs0 hs1
    (fun i => (fract_mem (R * w i)).1) (fun i => (fract_mem (R * w i)).2) _ j n

/-- **The sharp space modulus with the increment bound asked only below `N`.** -/
theorem abs_linInterp_sub_space_le_incr_of_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (K : ℝ) (N : ℕ)
    (hK : ∀ k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      |meshValue d R ζ k (Function.update z i (z i + 1)) - meshValue d R ζ k z| ≤ K)
    {r : ℝ} (hr : 0 ≤ r) (hrN : ⌊R ^ 2 * r⌋₊ + 1 ≤ N)
    (w w' : Sandpile.Continuum.Space d) :
    |linInterp d R ζ r w - linInterp d R ζ r w'|
      ≤ K * ∑ i : Fin d, |R * w i - R * w' i| :=
  abs_linInterp_sub_space_le_of_coord d R ζ
    (fun u v j h => abs_linInterp_sub_coord_le_incr_of_le d R ζ K N hK hr hrN u v j h) w w'

/-- The coefficient of `ζ(y)` vanishes when `y` lies outside every corner box of
the cell: both Green kernels in its definition do. -/
theorem interpCoeff_eq_zero_of_not_mem (R r : ℝ) (w : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    {y : Site d} (hy : y ∉ s) : interpCoeff d R r w y = 0 := by
  classical
  rw [interpCoeff]
  refine Finset.sum_eq_zero fun ε _ => ?_
  have h1 : Sandpile.greenTime d ⌊R ^ 2 * r⌋₊
      (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y = 0 := by
    by_contra hne
    exact hy (hs ε (Sandpile.mem_boxFinset
      (le_trans (Sandpile.greenTime_support _ _ hne) (Nat.le_succ _))))
  have h2 : Sandpile.greenTime d (⌊R ^ 2 * r⌋₊ + 1)
      (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) y = 0 := by
    by_contra hne
    exact hy (hs ε (Sandpile.mem_boxFinset (Sandpile.greenTime_support _ _ hne)))
  rw [h1, h2]
  ring

/-- **The `L²` mass of the heat kernel**, `∑_z p_n(x,z)^2 ≤ C n^{-d/2}`: every
term of the sum is at most the on-diagonal Gaussian bound and the terms sum to
one.  This is the time direction of the increment device below, since
`g_{k+1} - g_k = p_k`. -/
theorem exists_tsum_heatKernel_sq_le (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : Site d), 1 ≤ n →
      ∑' z : Site d, Sandpile.heatKernel d n x z ^ 2 ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := (hHK d hd).1
  refine ⟨C, hC, fun n x hn => ?_⟩
  have hsum : Summable (fun z : Site d => Sandpile.heatKernel d n x z) := by
    simpa using Sandpile.summable_heatKernel_mul n x (fun _ => (1 : ℝ))
  have hsq : Summable (fun z : Site d => Sandpile.heatKernel d n x z ^ 2) := by
    simpa [pow_two] using Sandpile.summable_heatKernel_mul n x (Sandpile.heatKernel d n x)
  have hptw : ∀ z : Site d, Sandpile.heatKernel d n x z ^ 2
      ≤ (C * (n : ℝ) ^ (-(d : ℝ) / 2)) * Sandpile.heatKernel d n x z := by
    intro z
    have h1 := hgauss n hn x z
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hexp : Real.exp (-c * Sandpile.External.latticeDist x z ^ 2 / (n : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hnum : -c * Sandpile.External.latticeDist x z ^ 2 ≤ 0 := by nlinarith [sq_nonneg (Sandpile.External.latticeDist x z)]
      exact div_nonpos_of_nonpos_of_nonneg hnum hn0.le
    have hpos : (0 : ℝ) ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    have hb : Sandpile.heatKernel d n x z ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
      refine le_trans h1 ?_
      nlinarith [hpos, hexp]
    nlinarith [Sandpile.heatKernel_nonneg n x z, hb]
  calc ∑' z : Site d, Sandpile.heatKernel d n x z ^ 2
      ≤ ∑' z : Site d, (C * (n : ℝ) ^ (-(d : ℝ) / 2)) * Sandpile.heatKernel d n x z :=
        hsq.tsum_le_tsum hptw (hsum.mul_left _)
    _ = C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
        rw [tsum_mul_left, Sandpile.tsum_heatKernel hd n x, mul_one]

/-- **The single-scenery identity.**  Applying the interpolated field to the
scenery `a = c_p - c_q` given by the increment of its own coefficient vector
returns the squared `ℓ²` norm of that increment. -/
theorem linInterp_coeffDiff_sub (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    (hq : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s) :
    linInterp d R (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) r w
        - linInterp d R (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) r' w'
      = ∑ z ∈ s, (interpCoeff d R r w z - interpCoeff d R r' w' z) ^ 2 := by
  rw [linInterp_eq_sum R r (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) w hp,
    linInterp_eq_sum R r' (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) w' hq,
    ← Finset.sum_sub_distrib,
    ← Sandpile.sum_siteEnum s fun z => (interpCoeff d R r w z - interpCoeff d R r' w' z) ^ 2]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Cauchy-Schwarz for the mesh increment.**  For a scenery supported in `s`,
the increment of the mesh value between two mesh points is at most the `ℓ²` increment of the Green kernels times the `ℓ²` norm of the scenery. -/
theorem abs_meshValue_sub_le_cauchy (R : ℝ) (a : Site d → ℝ) {s : Finset (Site d)}
    (ha : ∀ z ∉ s, a z = 0) (k k' : ℕ) (z z' : Site d) :
    |meshValue d R a k' z' - meshValue d R a k z|
      ≤ |R ^ ((d : ℝ) / 2 - 2)|
          * Real.sqrt (∑' y : Site d,
              (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2)
          * Real.sqrt (∑' y : Site d, a y ^ 2) := by
  classical
  have hsumz' : Summable (fun y : Site d => Sandpile.greenTime d k' z' y * a y) :=
    Sandpile.summable_greenTime_mul k' z' a
  have hsumz : Summable (fun y : Site d => Sandpile.greenTime d k z y * a y) :=
    Sandpile.summable_greenTime_mul k z a
  have hsq : Summable (fun y : Site d =>
      (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2) := by
    have s11 := Sandpile.summable_greenTime_mul_greenTime (d := d) k' k' z' z'
    have s22 := Sandpile.summable_greenTime_mul_greenTime (d := d) k k z z
    have s12 := Sandpile.summable_greenTime_mul_greenTime (d := d) k' k z' z
    have s21 := Sandpile.summable_greenTime_mul_greenTime (d := d) k k' z z'
    exact ((s11.add s22).sub (s12.add s21)).congr fun y => by ring
  have hsa : Summable (fun y : Site d => a y ^ 2) := by
    refine summable_of_ne_finset_zero (s := s) fun y hy => ?_
    rw [ha y hy]; ring
  have hstep : meshValue d R a k' z' - meshValue d R a k z
      = R ^ ((d : ℝ) / 2 - 2) * ∑ y ∈ s,
          (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) * a y := by
    simp only [Sandpile.Frozen.HeatPotentialInvariance.meshValue]
    rw [← mul_sub, ← Summable.tsum_sub hsumz' hsumz]
    congr 1
    rw [tsum_congr (fun y : Site d => (by ring :
      Sandpile.greenTime d k' z' y * a y - Sandpile.greenTime d k z y * a y
        = (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) * a y))]
    refine tsum_eq_sum fun y hy => ?_
    rw [ha y hy]; ring
  have hA : ∑ y ∈ s, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2
      ≤ ∑' y : Site d, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2 :=
    hsq.sum_le_tsum s fun y _ => sq_nonneg _
  have hB : ∑ y ∈ s, a y ^ 2 ≤ ∑' y : Site d, a y ^ 2 :=
    hsa.sum_le_tsum s fun y _ => sq_nonneg _
  have hA0 : (0:ℝ) ≤ ∑ y ∈ s, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2 :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  have hB0 : (0:ℝ) ≤ ∑ y ∈ s, a y ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hX2 : (∑ y ∈ s, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) * a y) ^ 2
      ≤ (∑' y : Site d, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2)
        * (∑' y : Site d, a y ^ 2) := by
    refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq s
      (fun y => Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) a) ?_
    exact mul_le_mul hA hB hB0 (le_trans hA0 hA)
  rw [hstep, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |∑ y ∈ s, (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) * a y|
      = Real.sqrt ((∑ y ∈ s,
          (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) * a y) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑' y : Site d,
          (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2)
        * (∑' y : Site d, a y ^ 2)) := Real.sqrt_le_sqrt hX2
    _ = Real.sqrt (∑' y : Site d,
          (Sandpile.greenTime d k' z' y - Sandpile.greenTime d k z y) ^ 2)
        * Real.sqrt (∑' y : Site d, a y ^ 2) :=
        Real.sqrt_mul (tsum_nonneg fun y => sq_nonneg _) _

/-- The `ℓ²` norm of the coefficient increment as a `tsum`: the coefficients
vanish outside the corner boxes of the two cells. -/
theorem tsum_coeffDiff_sq (R r r' : ℝ) (w w' : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    (hq : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r'⌋₊ + 1) ⊆ s) :
    ∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2
      = ∑ z ∈ s, (interpCoeff d R r w z - interpCoeff d R r' w' z) ^ 2 := by
  refine tsum_eq_sum fun y hy => ?_
  rw [interpCoeff_eq_zero_of_not_mem R r w hp hy, interpCoeff_eq_zero_of_not_mem R r' w' hq hy]
  ring

/-- One step of the time index of the Green kernel is the heat kernel. -/
theorem greenTime_succ_sub (k : ℕ) (z y : Site d) :
    Sandpile.greenTime d (k + 1) z y - Sandpile.greenTime d k z y
      = Sandpile.heatKernel d k z y := by
  simp [Sandpile.greenTime, LatticeProb.greenTime, Finset.sum_range_succ]

/-- The `L²` mass of the heat kernel is at most one at every time: its entries
lie in `[0,1]` and sum to one. -/
theorem tsum_heatKernel_sq_le_one (hd : 1 ≤ d) (k : ℕ) (z : Site d) :
    ∑' y : Site d, Sandpile.heatKernel d k z y ^ 2 ≤ 1 := by
  have hsum : Summable (fun y : Site d => Sandpile.heatKernel d k z y) := by
    simpa using Sandpile.summable_heatKernel_mul k z (fun _ => (1 : ℝ))
  have hsq : Summable (fun y : Site d => Sandpile.heatKernel d k z y ^ 2) := by
    simpa [pow_two] using Sandpile.summable_heatKernel_mul k z (Sandpile.heatKernel d k z)
  have hptw : ∀ y : Site d,
      Sandpile.heatKernel d k z y ^ 2 ≤ Sandpile.heatKernel d k z y := by
    intro y
    nlinarith [Sandpile.heatKernel_nonneg k z y, Sandpile.heatKernel_le_one hd k z y]
  calc ∑' y : Site d, Sandpile.heatKernel d k z y ^ 2
      ≤ ∑' y : Site d, Sandpile.heatKernel d k z y := hsq.tsum_le_tsum hptw hsum
    _ = 1 := Sandpile.tsum_heatKernel hd k z

/-- Raising one coordinate by one is the translate by the corresponding unit
vector. -/
theorem update_succ_eq_add_unit (z : Site d) (i : Fin d) :
    Function.update z i (z i + 1) = z + Sandpile.unit i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Sandpile.unit]
  · simp [Sandpile.unit, h]

/-- **The single-scenery device.**  A scenery supported in `s` whose own
interpolated field has the increment `‖a‖₂²` between two points has `ℓ²` norm at
most the modulus of continuity of the interpolation, with the mesh increments
priced by Cauchy-Schwarz: the time direction by the `L²` mass of the heat
kernel, at most one, and the space direction by `G`. -/
theorem sqrt_tsum_sq_le_of_selfScenery (hd : 1 ≤ d) (R : ℝ) (a : Site d → ℝ)
    {s : Finset (Site d)} (haz : ∀ z ∉ s, a z = 0)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w w' : Sandpile.Continuum.Space d)
    (hid : linInterp d R a r w - linInterp d R a r' w' = ∑' y : Site d, a y ^ 2)
    (N : ℕ) (hrN : ⌊R ^ 2 * r'⌋₊ + 1 ≤ N) (G : ℝ) (hG0 : 0 ≤ G)
    (hG : ∀ k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      ∑' y : Site d, (Sandpile.greenTime d k (Function.update z i (z i + 1)) y
          - Sandpile.greenTime d k z y) ^ 2 ≤ G ^ 2) :
    Real.sqrt (∑' y : Site d, a y ^ 2)
      ≤ |R ^ ((d : ℝ) / 2 - 2)|
          * (|R ^ 2 * r - R ^ 2 * r'| + G * ∑ i : Fin d, |R * w i - R * w' i|) := by
  classical
  have hA0 : (0:ℝ) ≤ ∑' y : Site d, a y ^ 2 := tsum_nonneg fun y => sq_nonneg _
  have hS0 : (0:ℝ) ≤ Real.sqrt (∑' y : Site d, a y ^ 2) := Real.sqrt_nonneg _
  have hSA : Real.sqrt (∑' y : Site d, a y ^ 2) ^ 2 = ∑' y : Site d, a y ^ 2 :=
    Real.sq_sqrt hA0
  have hR0 : (0:ℝ) ≤ |R ^ ((d : ℝ) / 2 - 2)| := abs_nonneg _
  have hsum0 : (0:ℝ) ≤ ∑ i : Fin d, |R * w i - R * w' i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hKt : ∀ (k : ℕ) (z : Site d),
      |meshValue d R a (k + 1) z - meshValue d R a k z|
        ≤ |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, a y ^ 2) := by
    intro k z
    have h0 := abs_meshValue_sub_le_cauchy R a haz k (k + 1) z z
    have hle : ∑' y : Site d,
        (Sandpile.greenTime d (k + 1) z y - Sandpile.greenTime d k z y) ^ 2 ≤ 1 := by
      rw [tsum_congr fun y : Site d => congrArg (· ^ 2) (greenTime_succ_sub k z y)]
      exact tsum_heatKernel_sq_le_one hd k z
    have h1 : Real.sqrt (∑' y : Site d,
        (Sandpile.greenTime d (k + 1) z y - Sandpile.greenTime d k z y) ^ 2) ≤ 1 := by
      have h2 := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_one] at h2
    refine le_trans h0 ?_
    calc |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d,
            (Sandpile.greenTime d (k + 1) z y - Sandpile.greenTime d k z y) ^ 2)
          * Real.sqrt (∑' y : Site d, a y ^ 2)
        ≤ (|R ^ ((d : ℝ) / 2 - 2)| * 1) * Real.sqrt (∑' y : Site d, a y ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hR0) hS0
      _ = |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, a y ^ 2) := by ring
  have hKs : ∀ k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      |meshValue d R a k (Function.update z i (z i + 1)) - meshValue d R a k z|
        ≤ |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := by
    intro k hk z i
    have h0 := abs_meshValue_sub_le_cauchy R a haz k k z (Function.update z i (z i + 1))
    have h1 : Real.sqrt (∑' y : Site d,
        (Sandpile.greenTime d k (Function.update z i (z i + 1)) y
          - Sandpile.greenTime d k z y) ^ 2) ≤ G := by
      have h2 := Real.sqrt_le_sqrt (hG k hk z i)
      rwa [Real.sqrt_sq hG0] at h2
    refine le_trans h0 ?_
    calc |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d,
            (Sandpile.greenTime d k (Function.update z i (z i + 1)) y
              - Sandpile.greenTime d k z y) ^ 2)
          * Real.sqrt (∑' y : Site d, a y ^ 2)
        ≤ (|R ^ ((d : ℝ) / 2 - 2)| * G) * Real.sqrt (∑' y : Site d, a y ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hR0) hS0
      _ = |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := by ring
  have htime := abs_linInterp_sub_time_le_incr d R a
    (|R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, a y ^ 2)) hKt hr hr' w
  have hspace := abs_linInterp_sub_space_le_incr_of_le d R a
    (|R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2)) N hKs hr' hrN w w'
  have hkey : ∑' y : Site d, a y ^ 2
      ≤ |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, a y ^ 2)
            * |R ^ 2 * r - R ^ 2 * r'|
          + |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2)
            * ∑ i : Fin d, |R * w i - R * w' i| := by
    calc ∑' y : Site d, a y ^ 2 = linInterp d R a r w - linInterp d R a r' w' := hid.symm
      _ ≤ |linInterp d R a r w - linInterp d R a r' w'| := le_abs_self _
      _ ≤ |linInterp d R a r w - linInterp d R a r' w|
            + |linInterp d R a r' w - linInterp d R a r' w'| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add htime hspace
  have hM0 : (0:ℝ) ≤ |R ^ ((d : ℝ) / 2 - 2)|
      * (|R ^ 2 * r - R ^ 2 * r'| + G * ∑ i : Fin d, |R * w i - R * w' i|) :=
    mul_nonneg hR0 (add_nonneg (abs_nonneg _) (mul_nonneg hG0 hsum0))
  rcases eq_or_lt_of_le hS0 with h | h
  · rw [← h]; exact hM0
  · refine le_of_mul_le_mul_left ?_ h
    calc Real.sqrt (∑' y : Site d, a y ^ 2) * Real.sqrt (∑' y : Site d, a y ^ 2)
        = Real.sqrt (∑' y : Site d, a y ^ 2) ^ 2 := by ring
      _ = ∑' y : Site d, a y ^ 2 := hSA
      _ ≤ |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, a y ^ 2)
            * |R ^ 2 * r - R ^ 2 * r'|
          + |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2)
            * ∑ i : Fin d, |R * w i - R * w' i| := hkey
      _ = Real.sqrt (∑' y : Site d, a y ^ 2) * (|R ^ ((d : ℝ) / 2 - 2)|
            * (|R ^ 2 * r - R ^ 2 * r'| + G * ∑ i : Fin d, |R * w i - R * w' i|)) := by ring

/-- **The `ℓ²` norm of the coefficient increment**, from the device: the corner
boxes of the two cells sit in one box about the origin, which is the finset the
scenery is supported in. -/
theorem sqrt_tsum_interpCoeff_sub_le (hd : 1 ≤ d) (R : ℝ) {r r' T : ℝ}
    (hr : 0 ≤ r) (hr' : 0 ≤ r') (hrT : r ≤ T) (hr'T : r' ≤ T)
    (w w' : Sandpile.Continuum.Space d) (G : ℝ) (hG0 : 0 ≤ G)
    (hG : ∀ k : ℕ, k ≤ ⌊R ^ 2 * T⌋₊ + 1 → ∀ (z : Site d) (i : Fin d),
      ∑' y : Site d, (Sandpile.greenTime d k (Function.update z i (z i + 1)) y
          - Sandpile.greenTime d k z y) ^ 2 ≤ G ^ 2) :
    Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
      ≤ |R ^ ((d : ℝ) / 2 - 2)|
          * (|R ^ 2 * r - R ^ 2 * r'| + G * ∑ i : Fin d, |R * w i - R * w' i|) := by
  classical
  have hR2 : (0:ℝ) ≤ R ^ 2 := sq_nonneg R
  have hfl : ⌊R ^ 2 * r⌋₊ ≤ ⌊R ^ 2 * T⌋₊ :=
    Nat.floor_le_floor (by nlinarith [hR2])
  have hfl' : ⌊R ^ 2 * r'⌋₊ ≤ ⌊R ^ 2 * T⌋₊ :=
    Nat.floor_le_floor (by nlinarith [hR2])
  have hmono : ∀ (x : Site d) (p q : ℕ), p ≤ q →
      Sandpile.boxFinset x p ⊆ Sandpile.boxFinset x q :=
    fun x p q h y hy => Sandpile.mem_boxFinset (le_trans (Sandpile.mem_boxFinset_iff.mp hy) h)
  have hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1)
        ⊆ Sandpile.boxFinset (0 : Site d)
            (⌈|R| * max ‖w‖ ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1)) := fun ε =>
    subset_trans (interp_box_subset R (max ‖w‖ ‖w'‖) r w (le_max_left _ _) ε)
      (hmono _ _ _ (by omega))
  have hq : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w' i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r'⌋₊ + 1)
        ⊆ Sandpile.boxFinset (0 : Site d)
            (⌈|R| * max ‖w‖ ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1)) := fun ε =>
    subset_trans (interp_box_subset R (max ‖w‖ ‖w'‖) r' w' (le_max_right _ _) ε)
      (hmono _ _ _ (by omega))
  have haz : ∀ z ∉ Sandpile.boxFinset (0 : Site d)
      (⌈|R| * max ‖w‖ ‖w'‖⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1)),
      (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) z = 0 := by
    intro z hz
    simp only
    rw [interpCoeff_eq_zero_of_not_mem R r w hp hz,
      interpCoeff_eq_zero_of_not_mem R r' w' hq hz]
    ring
  have hid : linInterp d R (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) r w
        - linInterp d R (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) r' w'
      = ∑' y : Site d, (fun y => interpCoeff d R r w y - interpCoeff d R r' w' y) y ^ 2 := by
    rw [linInterp_coeffDiff_sub R r r' w w' hp hq]
    exact (tsum_coeffDiff_sq R r r' w w' hp hq).symm
  exact sqrt_tsum_sq_le_of_selfScenery hd R _ haz hr hr' w w' hid (⌊R ^ 2 * T⌋₊ + 1)
    (by omega) G hG0 hG

/-- **The `L²` increment of the Green kernel over one unit step**, uniformly
over time indices at most `N`: the `L²` increment bound of
`ContGreenIncrementSum` at separation one, and its time factor is increasing. -/
theorem exists_green_unit_increment_bound
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N k : ℕ, k ≤ N → ∀ (z : Site d) (i : Fin d),
      ∑' y : Site d, (Sandpile.greenTime d k (Function.update z i (z i + 1)) y
          - Sandpile.greenTime d k z y) ^ 2
        ≤ C * (1 + (N : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) := by
  obtain ⟨C₁, hC₁, hbound⟩ := exists_tsum_greenTime_sub_sq_bound hHK hd hd3 hθ0 hθ1
  have hdreal : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (0:ℝ) ≤ (3 - (d : ℝ) + θ) / 2 := by linarith
  refine ⟨C₁ * (2 : ℝ) ^ (1 - θ), by positivity, ?_⟩
  intro N k hk z i
  have hdist : Sandpile.External.latticeDist (Function.update z i (z i + 1)) z = 1 := by
    rw [update_succ_eq_add_unit, latticeDist_comm, latticeDist_add_unit]
  have h1 := hbound k (Function.update z i (z i + 1)) z
  rw [hdist] at h1
  have hnum : ((1 : ℝ) + 1) = 2 := by norm_num
  rw [hnum] at h1
  have hmono : (1 + (k : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)
      ≤ (1 + (N : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) := by
    refine Real.rpow_le_rpow (by positivity) ?_ he
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    linarith
  refine le_trans h1 ?_
  have hC0 : (0:ℝ) ≤ C₁ * (2 : ℝ) ^ (1 - θ) := by positivity
  calc C₁ * (2 : ℝ) ^ (1 - θ) * (1 + (k : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)
      ≤ C₁ * (2 : ℝ) ^ (1 - θ) * (1 + (N : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) :=
        mul_le_mul_of_nonneg_left hmono hC0
    _ = C₁ * (2 : ℝ) ^ (1 - θ) * (1 + (N : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2) := rfl

/-- **(α) The `ℓ²` norm of the coefficient increment of the interpolated field,
at two arbitrary points of `[0,T] × ℝ^d`, with a constant free of `R`.**  The
time direction is priced by the `L²` mass of the heat kernel and the space
direction by the `L²` increment of the Green kernel over one unit step.  This is
the modulus below the mesh spacing: at a separation of one mesh cell the two
terms are `R^{d/2-2}` and `R^{d/2-2}(R^2T)^{(3-d+θ)/4}`, which is the size of the
`L²` increment of the field itself. -/
theorem exists_sqrt_tsum_interpCoeff_sub_le
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R T r r' : ℝ) (w w' : Sandpile.Continuum.Space d),
      0 ≤ r → 0 ≤ r' → r ≤ T → r' ≤ T →
      Real.sqrt (∑' y : Site d, (interpCoeff d R r w y - interpCoeff d R r' w' y) ^ 2)
        ≤ |R ^ ((d : ℝ) / 2 - 2)|
            * (|R ^ 2 * r - R ^ 2 * r'|
              + Real.sqrt (C * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))
                * ∑ i : Fin d, |R * w i - R * w' i|) := by
  obtain ⟨C, hC, hbound⟩ := exists_green_unit_increment_bound hHK hd hd3 hθ0 hθ1
  have hdreal : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (0:ℝ) ≤ (3 - (d : ℝ) + θ) / 2 := by linarith
  refine ⟨C, hC, ?_⟩
  intro R T r r' w w' hr hr' hrT hr'T
  have hT0 : (0:ℝ) ≤ T := le_trans hr hrT
  have hRT : (0:ℝ) ≤ R ^ 2 * T := mul_nonneg (sq_nonneg R) hT0
  have hbase : (0:ℝ) < 2 + R ^ 2 * T := by linarith
  have hpos : (0:ℝ) ≤ C * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hbase.le _)
  have hNle : (1 + ((⌊R ^ 2 * T⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 + R ^ 2 * T := by
    have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT
    push_cast
    linarith
  have hGle : C * (1 + ((⌊R ^ 2 * T⌋₊ + 1 : ℕ) : ℝ)) ^ ((3 - (d : ℝ) + θ) / 2)
      ≤ C * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hNle he) hC.le
  refine sqrt_tsum_interpCoeff_sub_le hd R hr hr' hrT hr'T w w'
    (Real.sqrt (C * (2 + R ^ 2 * T) ^ ((3 - (d : ℝ) + θ) / 2))) (Real.sqrt_nonneg _) ?_
  intro k hk z i
  rw [Real.sq_sqrt hpos]
  exact le_trans (hbound (⌊R ^ 2 * T⌋₊ + 1) k hk z i) hGle

/-- **The interpolated field is bounded by the mesh values it interpolates**,
with the bound asked only at time indices at most `N`. -/
theorem abs_linInterp_le_of_le (d : ℕ) (R : ℝ) (ζ : Site d → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (w : Sandpile.Continuum.Space d) (M : ℝ) (N : ℕ) (hrN : ⌊R ^ 2 * r⌋₊ + 1 ≤ N)
    (hM : ∀ k : ℕ, k ≤ N → ∀ z : Site d, |meshValue d R ζ k z| ≤ M) :
    |linInterp d R ζ r w| ≤ M := by
  classical
  set a : ℕ := ⌊R ^ 2 * r⌋₊ with ha
  set s : ℝ := R ^ 2 * r - (a : ℝ) with hs
  set b : Site d := fun i => ⌊R * w i⌋ with hb
  set t : Fin d → ℝ := fun i => R * w i - (b i : ℝ) with ht
  have hrR : 0 ≤ R ^ 2 * r := mul_nonneg (sq_nonneg R) hr
  have hs0 : 0 ≤ s := by
    have hle := Nat.floor_le hrR
    rw [← ha] at hle
    rw [hs]
    linarith
  have hs1 : s ≤ 1 := by
    have hlt := Nat.lt_floor_add_one (R ^ 2 * r)
    rw [← ha] at hlt
    rw [hs]
    linarith
  have ht0 : ∀ i, 0 ≤ t i := fun i => (fract_mem (R * w i)).1
  have ht1 : ∀ i, t i ≤ 1 := fun i => (fract_mem (R * w i)).2
  have hval : ∀ ε : Fin d → Bool,
      |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0) +
        s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| ≤ M := by
    intro ε
    have h1 := hM a (by omega) (fun i => b i + if ε i then 1 else 0)
    have h2 := hM (a + 1) (by omega) (fun i => b i + if ε i then 1 else 0)
    calc |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0) +
          s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)|
        ≤ |(1 - s) * meshValue d R ζ a (fun i => b i + if ε i then 1 else 0)| +
            |s * meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| :=
          abs_add_le _ _
      _ = (1 - s) * |meshValue d R ζ a (fun i => b i + if ε i then 1 else 0)| +
            s * |meshValue d R ζ (a + 1) (fun i => b i + if ε i then 1 else 0)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s),
            abs_of_nonneg hs0]
      _ ≤ (1 - s) * M + s * M := by
          have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - s)
          have := mul_le_mul_of_nonneg_left h2 hs0
          linarith
      _ = M := by ring
  exact abs_sum_weight_mul_le _ _ (fun ε => prod_ite_nonneg t ht0 ht1 ε)
    (sum_prod_ite d t) M hval

/-- **Cauchy-Schwarz for the mesh value itself**: the Green kernel vanishes at
time index zero, so the mesh value at a time index is its own increment from
time zero. -/
theorem abs_meshValue_le_cauchy (R : ℝ) (a : Site d → ℝ) {s : Finset (Site d)}
    (ha : ∀ z ∉ s, a z = 0) (k : ℕ) (z : Site d) :
    |meshValue d R a k z|
      ≤ |R ^ ((d : ℝ) / 2 - 2)|
          * Real.sqrt (∑' y : Site d, Sandpile.greenTime d k z y ^ 2)
          * Real.sqrt (∑' y : Site d, a y ^ 2) := by
  have hg0 : ∀ y : Site d, Sandpile.greenTime d 0 z y = 0 := by
    intro y
    simp [Sandpile.greenTime, LatticeProb.greenTime]
  have hm0 : meshValue d R a 0 z = 0 := by
    simp only [Sandpile.Frozen.HeatPotentialInvariance.meshValue]
    rw [tsum_congr fun y : Site d => (by rw [hg0 y]; ring :
      Sandpile.greenTime d 0 z y * a y = (0:ℝ))]
    simp
  have heq : (∑' y : Site d, (Sandpile.greenTime d k z y - Sandpile.greenTime d 0 z y) ^ 2)
      = ∑' y : Site d, Sandpile.greenTime d k z y ^ 2 :=
    tsum_congr fun y => by rw [hg0 y, sub_zero]
  have h := abs_meshValue_sub_le_cauchy R a ha 0 k z z
  rw [hm0, sub_zero, heq] at h
  exact h

/-- **The on-diagonal heat kernel at a doubled time**, in the shell form the
double time sum needs: at time `a + b` it is at most a constant times
`(1 + max(a,b))^{-d/2}`. -/
theorem exists_heatKernel_diag_le (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d)
    (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℕ) (z : Site d),
      Sandpile.heatKernel d (a + b) z z
        ≤ C * (1 + ((max a b : ℕ) : ℝ)) ^ (-(d : ℝ) / 2) := by
  obtain ⟨⟨C₁, c₁, hC₁, hc₁, hgauss⟩, -, -⟩ := hHK d hd
  have hdr : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdr3 : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (-(d:ℝ)/2) ≤ 0 := by linarith
  have he2 : (-2:ℝ) ≤ (-(d:ℝ)/2) := by linarith
  refine ⟨max (4 * C₁) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro a b z
  rcases Nat.eq_zero_or_pos (max a b) with hmax | hmax
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha
    subst hb
    have h1 : Sandpile.heatKernel d (0 + 0) z z = 1 := by
      simp [Sandpile.heatKernel, LatticeProb.LocalCLT.heatKernel]
    rw [h1, hmax]
    simp only [Nat.cast_zero, add_zero, Real.one_rpow, mul_one]
    exact le_max_right _ _
  · have hs1 : 1 ≤ a + b := by omega
    have hab : (0:ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast hs1
    have hg := hgauss (a + b) hs1 z z
    have hexp : Real.exp (-c₁ * Sandpile.External.latticeDist z z ^ 2
        / ((a + b : ℕ) : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hnn : 0 ≤ c₁ * Sandpile.External.latticeDist z z ^ 2 := by positivity
      rw [div_nonpos_iff]
      exact Or.inr ⟨by linarith, hab.le⟩
    have hfac : (0:ℝ) ≤ C₁ * ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2) := by positivity
    have hb1 : Sandpile.heatKernel d (a + b) z z
        ≤ C₁ * ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2) := by
      calc Sandpile.heatKernel d (a + b) z z
          ≤ C₁ * ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2)
              * Real.exp (-c₁ * Sandpile.External.latticeDist z z ^ 2
                / ((a + b : ℕ) : ℝ)) := hg
        _ ≤ C₁ * ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2) * 1 := mul_le_mul_of_nonneg_left hexp hfac
        _ = C₁ * ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2) := by rw [mul_one]
    have hmaxle : ((max a b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
      have h : max a b ≤ a + b := by omega
      exact_mod_cast h
    have hmpos : (0:ℝ) < ((max a b : ℕ) : ℝ) := by exact_mod_cast hmax
    have h2 : ((a + b : ℕ) : ℝ) ^ (-(d:ℝ)/2) ≤ ((max a b : ℕ) : ℝ) ^ (-(d:ℝ)/2) :=
      Real.rpow_le_rpow_of_nonpos hmpos hmaxle he
    have h3 : ((max a b : ℕ) : ℝ) ^ (-(d:ℝ)/2)
        ≤ 4 * (1 + ((max a b : ℕ) : ℝ)) ^ (-(d:ℝ)/2) := rpow_shift_le he he2 hmax
    have h4 : (0:ℝ) ≤ (1 + ((max a b : ℕ) : ℝ)) ^ (-(d:ℝ)/2) :=
      Real.rpow_nonneg (by positivity) _
    have h5 : 4 * C₁ ≤ max (4 * C₁) 1 := le_max_left _ _
    nlinarith [hb1, h2, h3, h4, h5, hC₁]

/-- **The `L²` mass of the Green kernel**, `∑_y g_k(z,y)^2 ≤ C (1+k)^{2-d/2}`:
the doubled Fubini identity turns it into a double time sum of the on-diagonal
heat kernel, which the shell count and the power sum bound. -/
theorem exists_tsum_greenTime_sq_le (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d)
    (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (z : Site d),
      ∑' y : Site d, Sandpile.greenTime d k z y ^ 2
        ≤ C * (1 + (k : ℝ)) ^ (2 - (d : ℝ) / 2) := by
  obtain ⟨C₂, hC₂, hdiag⟩ := exists_heatKernel_diag_le hHK hd hd3
  have hdr : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hdr3 : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (-(d:ℝ)/2) ≤ 0 := by linarith
  have he2 : (-2:ℝ) < (-(d:ℝ)/2) := by linarith
  have hexp : (-(d:ℝ)/2) + 2 = 2 - (d:ℝ)/2 := by ring
  have hden : (0:ℝ) < (-(d:ℝ)/2) + 2 := by linarith
  have hinv : (0:ℝ) < 1 / ((-(d:ℝ)/2) + 2) := div_pos one_pos hden
  refine ⟨C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2)), by nlinarith [hC₂, hinv], ?_⟩
  intro k z
  have hid : ∑' y : Site d, Sandpile.greenTime d k z y ^ 2
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, Sandpile.heatKernel d (a + b) z z := by
    rw [tsum_congr fun y : Site d => pow_two (Sandpile.greenTime d k z y)]
    exact Sandpile.tsum_greenTime_mul_greenTime k z z
  rw [hid]
  calc ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, Sandpile.heatKernel d (a + b) z z
      ≤ ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
          C₂ * (1 + ((max a b : ℕ) : ℝ)) ^ (-(d:ℝ)/2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hdiag a b z
    _ = C₂ * ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
          (1 + ((max a b : ℕ) : ℝ)) ^ (-(d:ℝ)/2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ ≤ C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2) * (1 + (k:ℝ)) ^ ((-(d:ℝ)/2) + 2)) :=
        mul_le_mul_of_nonneg_left (sum_sum_max_rpow_le he2 k) hC₂.le
    _ = C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2)) * (1 + (k:ℝ)) ^ (2 - (d:ℝ)/2) := by
        rw [hexp]; ring

/-- **The single-scenery device at one point.**  A scenery supported in `s` whose
own interpolated field equals `‖a‖₂²` at a point has `ℓ²` norm at most the bound
on the mesh values there, priced by Cauchy-Schwarz against the `L²` mass of the
Green kernel. -/
theorem sqrt_tsum_sq_le_of_selfScenery_point (R : ℝ) (a : Site d → ℝ)
    {s : Finset (Site d)} (haz : ∀ z ∉ s, a z = 0)
    {r : ℝ} (hr : 0 ≤ r) (w : Sandpile.Continuum.Space d)
    (hid : linInterp d R a r w = ∑' y : Site d, a y ^ 2)
    (N : ℕ) (hrN : ⌊R ^ 2 * r⌋₊ + 1 ≤ N) (G : ℝ) (hG0 : 0 ≤ G)
    (hG : ∀ k : ℕ, k ≤ N → ∀ z : Site d,
      ∑' y : Site d, Sandpile.greenTime d k z y ^ 2 ≤ G ^ 2) :
    Real.sqrt (∑' y : Site d, a y ^ 2) ≤ |R ^ ((d : ℝ) / 2 - 2)| * G := by
  have hA0 : (0:ℝ) ≤ ∑' y : Site d, a y ^ 2 := tsum_nonneg fun y => sq_nonneg _
  have hS0 : (0:ℝ) ≤ Real.sqrt (∑' y : Site d, a y ^ 2) := Real.sqrt_nonneg _
  have hSA : Real.sqrt (∑' y : Site d, a y ^ 2) ^ 2 = ∑' y : Site d, a y ^ 2 :=
    Real.sq_sqrt hA0
  have hR0 : (0:ℝ) ≤ |R ^ ((d : ℝ) / 2 - 2)| := abs_nonneg _
  have hM : ∀ k : ℕ, k ≤ N → ∀ z : Site d,
      |meshValue d R a k z|
        ≤ |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := by
    intro k hk z
    have h0 := abs_meshValue_le_cauchy R a haz k z
    have h1 : Real.sqrt (∑' y : Site d, Sandpile.greenTime d k z y ^ 2) ≤ G := by
      have h2 := Real.sqrt_le_sqrt (hG k hk z)
      rwa [Real.sqrt_sq hG0] at h2
    refine le_trans h0 ?_
    calc |R ^ ((d : ℝ) / 2 - 2)| * Real.sqrt (∑' y : Site d, Sandpile.greenTime d k z y ^ 2)
          * Real.sqrt (∑' y : Site d, a y ^ 2)
        ≤ (|R ^ ((d : ℝ) / 2 - 2)| * G) * Real.sqrt (∑' y : Site d, a y ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hR0) hS0
      _ = |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := by ring
  have hbnd := abs_linInterp_le_of_le d R a r hr w
    (|R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2)) N hrN hM
  have hkey : ∑' y : Site d, a y ^ 2
      ≤ |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := by
    calc ∑' y : Site d, a y ^ 2 = linInterp d R a r w := hid.symm
      _ ≤ |linInterp d R a r w| := le_abs_self _
      _ ≤ _ := hbnd
  rcases eq_or_lt_of_le hS0 with h | h
  · rw [← h]
    exact mul_nonneg hR0 hG0
  · refine le_of_mul_le_mul_left ?_ h
    calc Real.sqrt (∑' y : Site d, a y ^ 2) * Real.sqrt (∑' y : Site d, a y ^ 2)
        = Real.sqrt (∑' y : Site d, a y ^ 2) ^ 2 := by ring
      _ = ∑' y : Site d, a y ^ 2 := hSA
      _ ≤ |R ^ ((d : ℝ) / 2 - 2)| * G * Real.sqrt (∑' y : Site d, a y ^ 2) := hkey
      _ = Real.sqrt (∑' y : Site d, a y ^ 2) * (|R ^ ((d : ℝ) / 2 - 2)| * G) := by ring

/-- The `ℓ²` norm of the coefficient vector at one point, as a finset sum. -/
theorem tsum_interpCoeff_sq (R r : ℝ) (w : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) :
    ∑' y : Site d, interpCoeff d R r w y ^ 2
      = ∑ z ∈ s, interpCoeff d R r w z ^ 2 := by
  refine tsum_eq_sum fun y hy => ?_
  rw [interpCoeff_eq_zero_of_not_mem R r w hp hy]
  ring

/-- **The single-scenery identity at one point.** -/
theorem linInterp_interpCoeff_self (R r : ℝ) (w : Sandpile.Continuum.Space d)
    {s : Finset (Site d)}
    (hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) :
    linInterp d R (fun y => interpCoeff d R r w y) r w
      = ∑' y : Site d, interpCoeff d R r w y ^ 2 := by
  rw [linInterp_eq_sum R r (fun y => interpCoeff d R r w y) w hp,
    tsum_interpCoeff_sq R r w hp,
    ← Sandpile.sum_siteEnum s fun z => interpCoeff d R r w z ^ 2]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **(γ) The `ℓ²` norm of the coefficient vector of the interpolated field at
one point, with a constant free of `R`.**  At a time `r ≤ T` it is at most
`|R^{d/2-2}| (C(2+R^2T))^{(2-d/2)/2}`, which for `R^2 T` large is of order
`T^{1-d/4}`, the size of the field itself.  With the moment bound this is the
uniform-norm input of the tightness clause. -/
theorem exists_sqrt_tsum_interpCoeff_sq_le
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R T r : ℝ) (w : Sandpile.Continuum.Space d),
      0 ≤ r → r ≤ T →
      Real.sqrt (∑' y : Site d, interpCoeff d R r w y ^ 2)
        ≤ |R ^ ((d : ℝ) / 2 - 2)|
            * Real.sqrt (C * (2 + R ^ 2 * T) ^ (2 - (d : ℝ) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_tsum_greenTime_sq_le hHK hd hd3
  have hdr3 : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (0:ℝ) ≤ 2 - (d:ℝ)/2 := by linarith
  refine ⟨C, hC, ?_⟩
  intro R T r w hr hrT
  have hT0 : (0:ℝ) ≤ T := le_trans hr hrT
  have hRT : (0:ℝ) ≤ R ^ 2 * T := mul_nonneg (sq_nonneg R) hT0
  have hbase : (0:ℝ) < 2 + R ^ 2 * T := by linarith
  have hpos : (0:ℝ) ≤ C * (2 + R ^ 2 * T) ^ (2 - (d:ℝ)/2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hbase.le _)
  have hfl : ⌊R ^ 2 * r⌋₊ ≤ ⌊R ^ 2 * T⌋₊ :=
    Nat.floor_le_floor (by nlinarith [sq_nonneg R])
  have hNle : (1 + ((⌊R ^ 2 * T⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 + R ^ 2 * T := by
    have hf : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT
    push_cast
    linarith
  have hmono : ∀ (x : Site d) (m n : ℕ), m ≤ n →
      Sandpile.boxFinset x m ⊆ Sandpile.boxFinset x n :=
    fun x m n h y hy => Sandpile.mem_boxFinset (le_trans (Sandpile.mem_boxFinset_iff.mp hy) h)
  have hp : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (fun i => ⌊R * w i⌋ + if ε i then 1 else 0) (⌊R ^ 2 * r⌋₊ + 1)
        ⊆ Sandpile.boxFinset (0 : Site d)
            (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1)) := fun ε =>
    subset_trans (interp_box_subset R ‖w‖ r w le_rfl ε) (hmono _ _ _ (by omega))
  have haz : ∀ z ∉ Sandpile.boxFinset (0 : Site d)
      (⌈|R| * ‖w‖⌉₊ + 1 + 1 + (⌊R ^ 2 * T⌋₊ + 1)),
      (fun y => interpCoeff d R r w y) z = 0 := fun z hz =>
    interpCoeff_eq_zero_of_not_mem R r w hp hz
  refine sqrt_tsum_sq_le_of_selfScenery_point R (fun y => interpCoeff d R r w y) haz hr w
    (linInterp_interpCoeff_self R r w hp) (⌊R ^ 2 * T⌋₊ + 1) (by omega)
    (Real.sqrt (C * (2 + R ^ 2 * T) ^ (2 - (d:ℝ)/2))) (Real.sqrt_nonneg _) ?_
  intro k hk z
  rw [Real.sq_sqrt hpos]
  refine le_trans (hbound k z) ?_
  refine mul_le_mul_of_nonneg_left ?_ hC.le
  refine Real.rpow_le_rpow (by positivity) ?_ he
  have hkN : (k : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk
  linarith [hNle]

/-- The `L²` increment of the Green kernel in the time index at a fixed site, as
a double time sum of the on-diagonal heat kernel over the interval between the
two times. -/
theorem tsum_greenTime_time_sub_sq {k' k : ℕ} (hk : k' ≤ k) (x : Site d) :
    ∑' y : Site d, (Sandpile.greenTime d k x y - Sandpile.greenTime d k' x y) ^ 2
      = ∑ a ∈ Finset.Ico k' k, ∑ b ∈ Finset.Ico k' k,
          Sandpile.heatKernel d (a + b) x x := by
  have hdiff : ∀ y : Site d, Sandpile.greenTime d k x y - Sandpile.greenTime d k' x y
      = ∑ j ∈ Finset.Ico k' k, Sandpile.heatKernel d j x y := by
    intro y
    rw [Finset.sum_Ico_eq_sub _ hk]
    rfl
  have hexp : ∀ y : Site d,
      (Sandpile.greenTime d k x y - Sandpile.greenTime d k' x y) ^ 2
        = ∑ a ∈ Finset.Ico k' k, ∑ b ∈ Finset.Ico k' k,
            Sandpile.heatKernel d a x y * Sandpile.heatKernel d b y x := by
    intro y
    rw [hdiff y, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Sandpile.heatKernel_symm b x y]
  have hsum1 : ∀ a ∈ Finset.Ico k' k, ∀ b ∈ Finset.Ico k' k,
      Summable (fun y : Site d => Sandpile.heatKernel d a x y * Sandpile.heatKernel d b y x) :=
    fun a _ b _ => Sandpile.summable_heatKernel_mul a x (fun y => Sandpile.heatKernel d b y x)
  have hsum2 : ∀ a ∈ Finset.Ico k' k,
      Summable (fun y : Site d => ∑ b ∈ Finset.Ico k' k,
        Sandpile.heatKernel d a x y * Sandpile.heatKernel d b y x) :=
    fun a ha => summable_sum fun b hb => hsum1 a ha b hb
  rw [tsum_congr hexp, Summable.tsum_finsetSum hsum2]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Summable.tsum_finsetSum fun b hb => hsum1 a ha b hb]
  exact Finset.sum_congr rfl fun b _ => Sandpile.tsum_heatKernel_mul_heatKernel a b x x

/-- **The `L²` increment of the Green kernel in time**, `∑_y (g_k(x,y) -
g_{k'}(x,y))^2 ≤ C (1 + (k-k'))^{2-d/2}`.  The double time sum runs over the
interval between the two times, and its shells are counted exactly as for the
`L²` mass itself. -/
theorem exists_tsum_greenTime_time_sub_sq_le (hHK : Sandpile.External.HeatKernelBounds)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ k' k : ℕ, k' ≤ k → ∀ x : Site d,
      ∑' y : Site d, (Sandpile.greenTime d k x y - Sandpile.greenTime d k' x y) ^ 2
        ≤ C * (1 + ((k - k' : ℕ) : ℝ)) ^ (2 - (d : ℝ) / 2) := by
  obtain ⟨C₂, hC₂, hdiag⟩ := exists_heatKernel_diag_le hHK hd hd3
  have hdr3 : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
  have he : (-(d:ℝ)/2) ≤ 0 := by linarith
  have he2 : (-2:ℝ) < (-(d:ℝ)/2) := by linarith
  have hexp : (-(d:ℝ)/2) + 2 = 2 - (d:ℝ)/2 := by ring
  have hden : (0:ℝ) < (-(d:ℝ)/2) + 2 := by linarith
  have hinv : (0:ℝ) < 1 / ((-(d:ℝ)/2) + 2) := div_pos one_pos hden
  refine ⟨C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2)), by nlinarith [hC₂, hinv], ?_⟩
  intro k' k hk x
  have hterm : ∀ i j : ℕ, Sandpile.heatKernel d ((k' + i) + (k' + j)) x x
      ≤ C₂ * (1 + ((max i j : ℕ) : ℝ)) ^ (-(d:ℝ)/2) := by
    intro i j
    have h1 := hdiag (k' + i) (k' + j) x
    have hmaxeq : max (k' + i) (k' + j) = k' + max i j := by omega
    rw [hmaxeq] at h1
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂.le
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ he
    have hcast : ((max i j : ℕ) : ℝ) ≤ ((k' + max i j : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left (max i j) k'
    linarith
  rw [tsum_greenTime_time_sub_sq hk x]
  simp only [Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ Finset.range (k - k'), ∑ j ∈ Finset.range (k - k'),
        Sandpile.heatKernel d ((k' + i) + (k' + j)) x x
      ≤ ∑ i ∈ Finset.range (k - k'), ∑ j ∈ Finset.range (k - k'),
          C₂ * (1 + ((max i j : ℕ) : ℝ)) ^ (-(d:ℝ)/2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = C₂ * ∑ i ∈ Finset.range (k - k'), ∑ j ∈ Finset.range (k - k'),
          (1 + ((max i j : ℕ) : ℝ)) ^ (-(d:ℝ)/2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2)
          * (1 + ((k - k' : ℕ) : ℝ)) ^ ((-(d:ℝ)/2) + 2)) :=
        mul_le_mul_of_nonneg_left (sum_sum_max_rpow_le he2 (k - k')) hC₂.le
    _ = C₂ * (3 * (1 / ((-(d:ℝ)/2) + 2) + 2))
          * (1 + ((k - k' : ℕ) : ℝ)) ^ (2 - (d:ℝ)/2) := by rw [hexp]; ring

end Sandpile.Support
