/-
The first display of Step 2 of `prop:d4-superdiffusive-limit`
(`sandpile.tex:3374-3380`), over the cells of the mesh.

Step 2 compares the smoothed error `F_R = P^{n_R}E_{t_R-n_R}` with the constant
`C_R` of its own parity class: `C_R` agrees with `F_R(0)` on the parity class of
the origin and with `F_R(e_1)` on the other.  The comparison at a site is the
smoothed increment between two sites of EQUAL parity, so the gradient bound
`eq:rw-tv-gradient` applies and gives `C|x-b|^2V/n` with `V` the uniform second
moment of the error field.  Summed over the `O((RL)^4)` cells that the domain
meets, each at distance `O(R)` from its base point, the mesh sum
`R^{-4}∑_x(F_R-C_R)(x)^2` has expectation `O(R^2V/n_R)`, which is the paper's
`C_D(1+\log\log t_R)R^2/n_R`.
-/
import Sandpile.Support.D4SmoothL2
import Sandpile.Support.D4SNegSobolev

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

open Sandpile.Support Sandpile.Continuum

open Classical in
/-- The base point of the parity class of `x`: the origin on the parity class of
the origin, `e_1` on the other.  The field `x ↦ F(parityBase x)` is the paper's
`C_R` (`sandpile.tex:3374-3376`). -/
noncomputable def parityBase (x : Site 4) : Site 4 :=
  if Sandpile.External.SameParity x 0 then (0 : Site 4) else (0 : Site 4) + unit (0 : Fin 4)

theorem sameParity_parityBase (x : Site 4) :
    Sandpile.External.SameParity x (parityBase x) := by
  classical
  unfold parityBase
  by_cases h : Sandpile.External.SameParity x (0 : Site 4)
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact sameParity_add_unit_of_not h (0 : Fin 4)

theorem abs_parityBase_le (x : Site 4) (i : Fin 4) : |(parityBase x i : ℤ)| ≤ 1 := by
  classical
  unfold parityBase
  by_cases h : Sandpile.External.SameParity x (0 : Site 4)
  · rw [if_pos h]; simp
  · rw [if_neg h]
    have : ((0 : Site 4) + unit (0 : Fin 4)) i = (if i = 0 then (1:ℤ) else 0) := by
      simp [unit, Pi.single_apply]
    rw [this]
    split <;> simp

/-- Every site of the box of radius `N` is within `2(N+1)` of the base point of
its parity class. -/
theorem latticeDist_parityBase_le {N : ℕ} {x : Site 4}
    (hx : x ∈ Sandpile.boxFinset (0 : Site 4) N) :
    Sandpile.External.latticeDist x (parityBase x) ≤ 2 * ((N : ℝ) + 1) := by
  have hb : Sandpile.boxDist (0 : Site 4) x ≤ N := Sandpile.mem_boxFinset_iff.mp hx
  have hcoord : ∀ i : Fin 4, ((x i - parityBase x i : ℤ) : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    intro i
    have h : ((0 : Site 4) i - x i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => ((0 : Site 4) i - x i).natAbs)
        (Finset.mem_univ i)) hb
    simp only [Pi.zero_apply] at h
    have hxi : -(N : ℤ) ≤ x i ∧ x i ≤ (N : ℤ) := by omega
    have hbi := abs_le.mp (abs_parityBase_le x i)
    have h1 : -((N : ℤ) + 1) ≤ x i - parityBase x i := by omega
    have h2 : x i - parityBase x i ≤ (N : ℤ) + 1 := by omega
    have h1' : -((N : ℝ) + 1) ≤ ((x i - parityBase x i : ℤ) : ℝ) := by exact_mod_cast h1
    have h2' : ((x i - parityBase x i : ℤ) : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast h2
    nlinarith
  have hsum : ∑ i : Fin 4, ((x i - parityBase x i : ℤ) : ℝ) ^ 2 ≤ 4 * ((N : ℝ) + 1) ^ 2 := by
    calc ∑ i : Fin 4, ((x i - parityBase x i : ℤ) : ℝ) ^ 2
        ≤ ∑ _i : Fin 4, ((N : ℝ) + 1) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = 4 * ((N : ℝ) + 1) ^ 2 := by simp [Finset.sum_const]
  show Real.sqrt (∑ i : Fin 4, ((x i - parityBase x i : ℤ) : ℝ) ^ 2) ≤ 2 * ((N : ℝ) + 1)
  refine le_trans (Real.sqrt_le_sqrt hsum) (le_of_eq ?_)
  have hN : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
  rw [show (4 : ℝ) * ((N : ℝ) + 1) ^ 2 = (2 * ((N : ℝ) + 1)) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

/-- **The first display of Step 2, over the cells of the mesh**
(`sandpile.tex:3374-3380`).  If every value of the error field has second moment
at most `V`, then the mesh sum of the squares of `F_R-C_R` has expectation at
most `C(L+3)^6R^2V/n`, which at `V = C(1+\log\log t_R)` and `n = n_R` is the
paper's `C_D(1+\log\log t_R)R^2/n_R`. -/
theorem exists_integral_mesh_sum_parity_le (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Site 4 → ℝ)
      (V : ℝ), (∀ z : Site 4, AEStronglyMeasurable (fun ω => X ω z) P) →
      (∀ z : Site 4, Integrable (fun ω => (X ω z) ^ 2) P) →
      (∀ z : Site 4, ∫ ω, (X ω z) ^ 2 ∂P ≤ V) →
      ∀ n : ℕ, 1 ≤ n → ∀ R L : ℝ, 1 ≤ R → 0 ≤ L →
        ∫ ω, (R⁻¹ ^ 4 * ∑ x ∈ Sandpile.boxFinset (0 : Site 4) (⌈|R| * L⌉₊ + 1),
            ((avg^[n] (X ω)) x - (avg^[n] (X ω)) (parityBase x)) ^ 2) ∂P
          ≤ C * (L + 3) ^ 6 * (R ^ 2 * V / (n : ℝ)) := by
  classical
  obtain ⟨C0, hC0, hincr⟩ := exists_integral_sq_smoothing_increment_four hHK
  refine ⟨64 * C0, by positivity, ?_⟩
  intro Ω _ P X V hmeas hint hV n hn R L hR hL
  set N : ℕ := ⌈|R| * L⌉₊ + 1 with hN
  set s : Finset (Site 4) := Sandpile.boxFinset (0 : Site 4) N with hs
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hV0 : (0:ℝ) ≤ V := le_trans (integral_nonneg fun ω => sq_nonneg _) (hV 0)
  have hNle : ((N : ℝ)) ≤ R * L + 2 := by
    have habs : |R| = R := abs_of_pos hR0
    have hceil : (⌈R * L⌉₊ : ℝ) ≤ R * L + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    rw [hN]
    push_cast
    rw [habs]
    linarith
  -- the per-site bound
  have hterm : ∀ x ∈ s, ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) (parityBase x)) ^ 2 ∂P ≤
      C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V := by
    intro x hx
    refine le_trans (hincr P X V hint hV n hn x (parityBase x) (sameParity_parityBase x)) ?_
    have hd := latticeDist_parityBase_le (N := N) (x := x) hx
    have hd0 : (0:ℝ) ≤ Sandpile.External.latticeDist x (parityBase x) := Real.sqrt_nonneg _
    have hsq : Sandpile.External.latticeDist x (parityBase x) ^ 2 ≤ (2 * ((N : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ hd0 hd 2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn0]
    have hdiff : (0:ℝ) ≤ (2 * ((N : ℝ) + 1)) ^ 2 -
        Sandpile.External.latticeDist x (parityBase x) ^ 2 := by linarith
    linarith [mul_nonneg (mul_nonneg hC0.le hdiff) hV0]
  -- integrate the finite sum termwise
  have hintterm : ∀ x ∈ s, Integrable
      (fun ω => ((avg^[n] (X ω)) x - (avg^[n] (X ω)) (parityBase x)) ^ 2) P :=
    fun x _ => integrable_sq_smoothing_increment P X n x (parityBase x) hmeas hint
  have hcard : (s.card : ℝ) = (2 * (N : ℝ) + 1) ^ 4 := by
    rw [hs, Sandpile.card_boxFinset]
    push_cast
    ring
  have hsum : ∫ ω, (∑ x ∈ s, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) (parityBase x)) ^ 2) ∂P ≤
      (2 * (N : ℝ) + 1) ^ 4 * (C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V) := by
    rw [integral_finsetSum s hintterm]
    calc ∑ x ∈ s, ∫ ω, ((avg^[n] (X ω)) x - (avg^[n] (X ω)) (parityBase x)) ^ 2 ∂P
        ≤ ∑ _x ∈ s, C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (N : ℝ) + 1) ^ 4 * (C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V) := by rw [hcard]
  -- the constant comes out of the integral
  rw [integral_const_mul]
  have hRinv : (0:ℝ) ≤ R⁻¹ ^ 4 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left hsum hRinv) ?_
  -- arithmetic on the mesh count and the mesh radius
  have hb1 : 2 * (N : ℝ) + 1 ≤ 2 * (L + 3) * R := by nlinarith [hNle, hR, hL]
  have hb2 : 2 * ((N : ℝ) + 1) ≤ 2 * (L + 3) * R := by nlinarith [hNle, hR, hL]
  have hb1' : (0:ℝ) ≤ 2 * (N : ℝ) + 1 := by positivity
  have hb2' : (0:ℝ) ≤ 2 * ((N : ℝ) + 1) := by positivity
  have hp1 : (2 * (N : ℝ) + 1) ^ 4 ≤ (2 * (L + 3) * R) ^ 4 := pow_le_pow_left₀ hb1' hb1 4
  have hp2 : (2 * ((N : ℝ) + 1)) ^ 2 ≤ (2 * (L + 3) * R) ^ 2 := pow_le_pow_left₀ hb2' hb2 2
  have hCV : (0:ℝ) ≤ C0 / (n : ℝ) * V := by positivity
  have hstep : (2 * (N : ℝ) + 1) ^ 4 * (C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V) ≤
      (2 * (L + 3) * R) ^ 4 * (C0 * (2 * (L + 3) * R) ^ 2 / (n : ℝ) * V) := by
    have h1 : C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V ≤
        C0 * (2 * (L + 3) * R) ^ 2 / (n : ℝ) * V := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn0]
      have hdiff : (0:ℝ) ≤ (2 * (L + 3) * R) ^ 2 - (2 * ((N : ℝ) + 1)) ^ 2 := by linarith
      linarith [mul_nonneg (mul_nonneg hC0.le hdiff) hV0]
    have h2 : (0:ℝ) ≤ C0 * (2 * (L + 3) * R) ^ 2 / (n : ℝ) * V := by positivity
    calc (2 * (N : ℝ) + 1) ^ 4 * (C0 * (2 * ((N : ℝ) + 1)) ^ 2 / (n : ℝ) * V)
        ≤ (2 * (N : ℝ) + 1) ^ 4 * (C0 * (2 * (L + 3) * R) ^ 2 / (n : ℝ) * V) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (2 * (L + 3) * R) ^ 4 * (C0 * (2 * (L + 3) * R) ^ 2 / (n : ℝ) * V) :=
          mul_le_mul_of_nonneg_right hp1 h2
  refine le_trans (mul_le_mul_of_nonneg_left hstep hRinv) (le_of_eq ?_)
  field_simp
  ring

end Sandpile
