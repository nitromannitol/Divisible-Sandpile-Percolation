import Sandpile.External.BallGreenBounds
import Sandpile.External.GreenBoundsHighProved
import Sandpile.Support.ExitGreen
import Sandpile.Support.NearKernel

open MeasureTheory

open Sandpile

namespace Sandpile.External

theorem aux_ballgreen_clause1 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ u : Sandpile.Site 4,
        0 ≤ Sandpile.killedGreen (BallGreen.box r) 0 u ∧
          Sandpile.killedGreen (BallGreen.box r) 0 u ≤ Sandpile.green 4 0 u ∧
          Sandpile.green 4 0 u ≤ C / (1 + BallGreen.latticeNorm u) ^ 2 := by
  obtain ⟨C, hC, hfree⟩ := LatticeProb.exists_srwGreenInf_euclid_le 0
  refine ⟨C, hC, fun r hr u => ?_⟩
  have hsumFree : Summable (fun k : ℕ => Sandpile.heatKernel 4 k 0 u) :=
    Sandpile.summable_heatKernel_transient (by norm_num) 0 u
  have hsumKilled : Summable
      (fun k : ℕ => Sandpile.killedKernel (BallGreen.box r) k 0 u) :=
    Summable.of_nonneg_of_le
      (fun k => Sandpile.killedKernel_nonneg (BallGreen.box r) k 0 u)
      (fun k => Sandpile.killedKernel_le_heatKernel (BallGreen.box r) k 0 u)
      hsumFree
  have hnonneg : 0 ≤ Sandpile.killedGreen (BallGreen.box r) 0 u := by
    rw [Sandpile.killedGreen]
    exact tsum_nonneg fun k => Sandpile.killedKernel_nonneg (BallGreen.box r) k 0 u
  have hdom : Sandpile.killedGreen (BallGreen.box r) 0 u ≤ Sandpile.green 4 0 u := by
    rw [Sandpile.killedGreen, Sandpile.green]
    exact hsumKilled.tsum_le_tsum
      (fun k => Sandpile.killedKernel_le_heatKernel (BallGreen.box r) k 0 u) hsumFree
  have hpoint : Sandpile.green 4 0 u ≤ C / (1 + BallGreen.latticeNorm u) ^ 2 := by
    rw [Sandpile.External.green_eq_srwGreenInf 4 0 u, sub_zero]
    simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using hfree u
  exact ⟨hnonneg, hdom, hpoint⟩

theorem aux_ballgreen_clause2 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      (∑' u : Sandpile.Site 4,
        Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) ≤ C * Real.log (r : ℝ) := by
  obtain ⟨C₀, hC₀, hclause1⟩ := aux_ballgreen_clause1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := C₀ ^ 2 * (65 + 129 / Real.log 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hlogr : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hr1)
  have hlog2r : Real.log (2 : ℝ) ≤ Real.log (r : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hr
  have hzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.boxFinset 0 r →
      Sandpile.killedGreen (BallGreen.box r) 0 u = 0 := by
    intro u hu
    have hu' : u ∉ BallGreen.box r := by
      intro hmem
      apply hu
      rw [LatticeProb.mem_boxFinset_zero_iff]
      apply LatticeProb.supNorm_le_iff.mpr
      intro i
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hmem i
    rw [Sandpile.killedGreen]
    have hfun : (fun k : ℕ => Sandpile.killedKernel (BallGreen.box r) k 0 u) =
        fun _ => (0 : ℝ) := by
      funext k
      exact Sandpile.killedKernel_eq_zero_of_target_notMem (BallGreen.box r) hu' k 0
    rw [hfun, tsum_zero]
  have hfinite :
      (∑' u : Sandpile.Site 4,
        Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) =
        ∑ u ∈ LatticeProb.boxFinset 0 r,
          Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2 :=
    tsum_eq_sum (fun u hu => by rw [hzero u hu, zero_pow (by norm_num)])
  have hterm : ∀ u ∈ LatticeProb.boxFinset 0 r,
      Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2 ≤
        (C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2) ^ 2 := by
    intro u hu
    have h := (hclause1 r hr u)
    have hnorm : (1 + (LatticeProb.supNorm u : ℝ)) ≤ 1 + BallGreen.latticeNorm u := by
      have hnorm' := LatticeProb.supNorm_le_euclidNorm u
      simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using add_le_add_right hnorm' 1
    have hbound : Sandpile.killedGreen (BallGreen.box r) 0 u ≤
        C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2 := by
      exact h.2.1.trans (h.2.2.trans (div_le_div_of_nonneg_left hC₀.le (by positivity)
        (pow_le_pow_left₀ (by positivity) hnorm 2))
        )
    exact (sq_le_sq₀ h.1 (by positivity)).2 hbound
  have hsumterm :
      (∑ u ∈ LatticeProb.boxFinset 0 r,
        Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) ≤
        ∑ u ∈ LatticeProb.boxFinset 0 r,
          (C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2) ^ 2 :=
    Finset.sum_le_sum fun u hu => hterm u hu
  let f : ℕ → ℝ := fun k => (C₀ / (1 + (k : ℝ)) ^ 2) ^ 2
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hradial := LatticeProb.sum_box_radial_le (d := 4) f hf r
  have hradial' :
      ∑ u ∈ (LatticeProb.boxFinset (d := 4) 0 r),
        (C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2) ^ 2 ≤
        f 0 + ∑ k ∈ Finset.Icc 1 r,
          8 * (2 * (k : ℝ) + 1) ^ 3 * f k := by
    norm_num [f] at hradial ⊢
    exact hradial
  have hradial'' :
      (∑ u ∈ (LatticeProb.boxFinset (d := 4) 0 r),
        (C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2) ^ 2) ≤
        C₀ ^ 2 + ∑ k ∈ Finset.Icc 1 r,
          8 * (2 * (k : ℝ) + 1) ^ 3 * f k := by
    simpa [f] using hradial'
  have hfinbound :
      (∑ u ∈ LatticeProb.boxFinset 0 r,
        Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) ≤ C * Real.log (r : ℝ) := by
    refine hsumterm.trans (hradial''.trans ?_)
    have hshell : ∀ k ∈ Finset.Icc 1 r,
      8 * (2 * (k : ℝ) + 1) ^ 3 * f k ≤ 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      dsimp [f]
      have hkp : (2 * (k : ℝ) + 1) ≤ 2 * (1 + (k : ℝ)) := by linarith
      have hpow := pow_le_pow_left₀ (by positivity) hkp 3
      rw [div_pow]
      rw [show ((1 + (k : ℝ)) ^ 2) ^ 2 = (1 + (k : ℝ)) ^ 4 by ring]
      have hden : (0 : ℝ) < 1 + (k : ℝ) := by positivity
      have hpow' : (2 * (k : ℝ) + 1) ^ 3 ≤ 8 * (1 + (k : ℝ)) ^ 3 := by
        nlinarith [hpow]
      calc
        8 * (2 * (k : ℝ) + 1) ^ 3 * (C₀ ^ 2 / (1 + (k : ℝ)) ^ 4)
            ≤ (8 * (8 * (1 + (k : ℝ)) ^ 3)) *
                (C₀ ^ 2 / (1 + (k : ℝ)) ^ 4) := by
              gcongr
        _ = 64 * C₀ ^ 2 * (1 + (k : ℝ))⁻¹ := by
              field_simp
              ring
        _ ≤ 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ := by
              have hinv : (1 + (k : ℝ))⁻¹ ≤ ((k : ℝ))⁻¹ := by
                exact inv_anti₀ (by positivity) (by linarith)
              exact mul_le_mul_of_nonneg_left hinv (by positivity)
    have hharm : ∑ k ∈ Finset.Icc 1 r, ((k : ℝ))⁻¹ ≤ 2 + Real.log (r : ℝ) := by
      have hsum := LatticeProb.sum_inv_le_one_add_log r
      have hlast : ((r : ℝ))⁻¹ ≤ 1 := by
        exact inv_le_one_of_one_le₀ (by exact_mod_cast hr1)
      have hi : Finset.Ico 1 r ∪ {r} = Finset.Icc 1 r := by
        ext k
        simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton, Finset.mem_Icc]
        omega
      rw [← hi, Finset.sum_union]
      · simp only [Finset.sum_singleton]
        linarith
      · simp only [Finset.disjoint_singleton_right]
        intro hk
        exact (Nat.not_lt_of_ge le_rfl (Finset.mem_Ico.mp hk).2)
    have hsumShell :
        ∑ k ∈ Finset.Icc 1 r, 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ ≤
          64 * C₀ ^ 2 * (2 + Real.log (r : ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hharm (by positivity)
    have hshellsum :
        (∑ k ∈ Finset.Icc 1 r, 8 * (2 * (k : ℝ) + 1) ^ 3 * f k) ≤
          ∑ k ∈ Finset.Icc 1 r, 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ :=
      Finset.sum_le_sum hshell
    have hratio129 : 129 ≤ (129 / Real.log 2) * Real.log (r : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hlog2).2
      nlinarith
    have hmain : C₀ ^ 2 + 64 * C₀ ^ 2 * (2 + Real.log (r : ℝ)) ≤ C * Real.log (r : ℝ) := by
      dsimp [C]
      calc
        C₀ ^ 2 + 64 * C₀ ^ 2 * (2 + Real.log (r : ℝ)) =
            C₀ ^ 2 * (129 + 64 * Real.log (r : ℝ)) := by ring
        _ ≤ C₀ ^ 2 * ((65 + 129 / Real.log 2) * Real.log (r : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C₀)
          nlinarith [hlogr, hratio129]
        _ = C₀ ^ 2 * (65 + 129 / Real.log 2) * Real.log (r : ℝ) := by ring
    calc
      C₀ ^ 2 + ∑ k ∈ Finset.Icc 1 r, 8 * (2 * (k : ℝ) + 1) ^ 3 * f k
          ≤ C₀ ^ 2 + ∑ k ∈ Finset.Icc 1 r, 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ := by
            exact add_le_add_right hshellsum (C₀ ^ 2)
      _ ≤ C₀ ^ 2 + 64 * C₀ ^ 2 * (2 + Real.log (r : ℝ)) := by
            exact add_le_add_right hsumShell (C₀ ^ 2)
      _ ≤ C * Real.log (r : ℝ) := hmain
  exact hfinite ▸ hfinbound

theorem aux_ballgreen_clause3 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      (∑' u : {u : Sandpile.Site 4 //
          BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
        Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4) ^ 2) ≤
        C * Real.log (2 * (L : ℝ) + 2) := by
  obtain ⟨C₀, hC₀, hclause1⟩ := aux_ballgreen_clause1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := C₀ ^ 2 * (65 + 129 / Real.log 2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun r hr L hL => ?_⟩
  let S : Set (Sandpile.Site 4) :=
    {u | BallGreen.latticeNorm u ≤ 2 * (L : ℝ)}
  change (∑' u : S,
      Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4) ^ 2) ≤
    C * Real.log (2 * (L : ℝ) + 2)
  rw [tsum_subtype S (fun u : Sandpile.Site 4 =>
    Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2)]
  let n : ℕ := 2 * L
  have hn : 2 ≤ n := by
    dsimp [n]
    omega
  have hSbox : ∀ u : Sandpile.Site 4, u ∈ S →
      u ∈ LatticeProb.boxFinset 0 n := by
    intro u hu
    rw [LatticeProb.mem_boxFinset_zero_iff]
    apply LatticeProb.supNorm_le_iff.mpr
    have hnorm : (LatticeProb.supNorm u : ℝ) ≤ BallGreen.latticeNorm u := by
      simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using
        LatticeProb.supNorm_le_euclidNorm u
    have hu' : BallGreen.latticeNorm u ≤ 2 * (L : ℝ) := hu
    have hsup : (LatticeProb.supNorm u : ℝ) ≤ (n : ℝ) := by
      dsimp [n]
      exact hnorm.trans (by simpa using hu')
    have hsup' : LatticeProb.supNorm u ≤ n := by exact_mod_cast hsup
    exact LatticeProb.supNorm_le_iff.mp hsup'
  have hzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.boxFinset 0 n →
      S.indicator
          (fun u : Sandpile.Site 4 =>
            Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) u = 0 := by
    intro u hu
    have huS : u ∉ S := by
      intro huS
      exact hu (hSbox u huS)
    rw [Set.indicator_of_notMem huS]
  rw [tsum_eq_sum hzero]
  let f : ℕ → ℝ := fun k => (C₀ / (1 + (k : ℝ)) ^ 2) ^ 2
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hterm : ∀ u : Sandpile.Site 4,
      S.indicator
          (fun u : Sandpile.Site 4 =>
            Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) u ≤ f (LatticeProb.supNorm u) := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      have h := hclause1 r hr u
      have hnorm : (1 + (LatticeProb.supNorm u : ℝ)) ≤ 1 + BallGreen.latticeNorm u := by
        have hnorm' := LatticeProb.supNorm_le_euclidNorm u
        simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using add_le_add_right hnorm' 1
      have hbound : Sandpile.killedGreen (BallGreen.box r) 0 u ≤
          C₀ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2 := by
        exact h.2.1.trans (h.2.2.trans (div_le_div_of_nonneg_left hC₀.le (by positivity)
          (pow_le_pow_left₀ (by positivity) hnorm 2)))
      exact (sq_le_sq₀ h.1 (by positivity)).2 hbound
    · rw [Set.indicator_of_notMem hu]
      exact hf _
  have hsumterm :
      (∑ u ∈ LatticeProb.boxFinset 0 n,
        S.indicator
          (fun u : Sandpile.Site 4 =>
            Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) u) ≤
        ∑ u ∈ LatticeProb.boxFinset 0 n, f (LatticeProb.supNorm u) :=
    Finset.sum_le_sum fun u hu => hterm u
  have hradial := LatticeProb.sum_box_radial_le (d := 4) f hf n
  have hradial' :
      ∑ u ∈ (LatticeProb.boxFinset (d := 4) 0 n), f (LatticeProb.supNorm u) ≤
        C₀ ^ 2 + ∑ k ∈ Finset.Icc 1 n,
          8 * (2 * (k : ℝ) + 1) ^ 3 * f k := by
    norm_num [f] at hradial ⊢
    exact hradial
  have hshell : ∀ k ∈ Finset.Icc 1 n,
      8 * (2 * (k : ℝ) + 1) ^ 3 * f k ≤ 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    dsimp [f]
    have hkp : (2 * (k : ℝ) + 1) ≤ 2 * (1 + (k : ℝ)) := by linarith
    have hpow := pow_le_pow_left₀ (by positivity) hkp 3
    rw [div_pow]
    rw [show ((1 + (k : ℝ)) ^ 2) ^ 2 = (1 + (k : ℝ)) ^ 4 by ring]
    have hden : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have hpow' : (2 * (k : ℝ) + 1) ^ 3 ≤ 8 * (1 + (k : ℝ)) ^ 3 := by
      nlinarith [hpow]
    calc
      8 * (2 * (k : ℝ) + 1) ^ 3 * (C₀ ^ 2 / (1 + (k : ℝ)) ^ 4)
          ≤ (8 * (8 * (1 + (k : ℝ)) ^ 3)) *
              (C₀ ^ 2 / (1 + (k : ℝ)) ^ 4) := by
            gcongr
      _ = 64 * C₀ ^ 2 * (1 + (k : ℝ))⁻¹ := by
            field_simp
            ring
      _ ≤ 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ := by
            have hinv : (1 + (k : ℝ))⁻¹ ≤ ((k : ℝ))⁻¹ := by
              exact inv_anti₀ (by positivity) (by linarith)
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hharm : ∑ k ∈ Finset.Icc 1 n, ((k : ℝ))⁻¹ ≤ 2 + Real.log (n : ℝ) := by
    have hsum := LatticeProb.sum_inv_le_one_add_log n
    have hn1 : 1 ≤ n := by omega
    have hlast : ((n : ℝ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
    have hi : Finset.Ico 1 n ∪ {n} = Finset.Icc 1 n := by
      ext k
      simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton, Finset.mem_Icc]
      omega
    rw [← hi, Finset.sum_union]
    · simp only [Finset.sum_singleton]
      linarith
    · simp only [Finset.disjoint_singleton_right]
      intro hk
      exact (Nat.not_lt_of_ge le_rfl (Finset.mem_Ico.mp hk).2)
  have hsumShell :
      ∑ k ∈ Finset.Icc 1 n, 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ ≤
        64 * C₀ ^ 2 * (2 + Real.log (n : ℝ)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hharm (by positivity)
  have hshellsum :
      (∑ k ∈ Finset.Icc 1 n, 8 * (2 * (k : ℝ) + 1) ^ 3 * f k) ≤
        ∑ k ∈ Finset.Icc 1 n, 64 * C₀ ^ 2 * ((k : ℝ))⁻¹ :=
    Finset.sum_le_sum hshell
  have hlog2n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hn
  have hratio129 : 129 ≤ (129 / Real.log 2) * Real.log (n : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlog2).2
    nlinarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hmain : C₀ ^ 2 + 64 * C₀ ^ 2 * (2 + Real.log (n : ℝ)) ≤
      C * Real.log (n : ℝ) := by
    dsimp [C]
    calc
      C₀ ^ 2 + 64 * C₀ ^ 2 * (2 + Real.log (n : ℝ)) =
          C₀ ^ 2 * (129 + 64 * Real.log (n : ℝ)) := by ring
      _ ≤ C₀ ^ 2 * ((65 + 129 / Real.log 2) * Real.log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C₀)
        nlinarith [hlogn, hratio129]
      _ = C₀ ^ 2 * (65 + 129 / Real.log 2) * Real.log (n : ℝ) := by ring
  have hbox :
      (∑ u ∈ LatticeProb.boxFinset 0 n,
        S.indicator
          (fun u : Sandpile.Site 4 =>
            Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) u) ≤
        C * Real.log (n : ℝ) := by
    exact hsumterm.trans (hradial'.trans
      ((add_le_add_right hshellsum (C₀ ^ 2)).trans
        ((add_le_add_right hsumShell (C₀ ^ 2)).trans hmain)))
  have hlogfinal : Real.log (n : ℝ) ≤ Real.log (2 * (L : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    dsimp [n]
    norm_num
  exact hbox.trans (mul_le_mul_of_nonneg_left hlogfinal hC.le)

theorem aux_ballgreen_clause5 :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      ∀ φ : ℝ → ℝ, BallGreen.IsCutoff φ →
        (∀ u : Sandpile.Site 4,
            |BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
          (∑' u : Sandpile.Site 4, BallGreen.cutField r L φ u ^ 3) ≤
            C / (L : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀, hclause1⟩ := aux_ballgreen_clause1
  let C₁ : ℝ := max C₀ 1
  have hC₁ : 0 < C₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  let C : ℝ := C₁ ^ 3 * 512
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, fun r hr L hL φ hφ => ?_⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hC₀le : C₀ ≤ C₁ := le_max_left _ _
  have hC₁one : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hsup : ∀ u : Sandpile.Site 4,
      |BallGreen.cutField r L φ u| ≤ C₁ / (L : ℝ) ^ 2 := by
    intro u
    have hg := hclause1 r hr u
    have hphi := hφ.1 (BallGreen.latticeNorm u / (L : ℝ))
      (div_nonneg (Real.sqrt_nonneg _) hLpos.le)
    have hcut : 0 ≤ BallGreen.cutField r L φ u :=
      Sandpile.cutField_nonneg r L hφ u
    rw [abs_of_nonneg hcut]
    by_cases hu : BallGreen.latticeNorm u ≤ (L : ℝ)
    · have hzero : φ (BallGreen.latticeNorm u / (L : ℝ)) = 0 := by
        apply hφ.2.2.1
        · exact div_nonneg (Real.sqrt_nonneg _) hLpos.le
        · have hu' : BallGreen.latticeNorm u ≤ 1 * (L : ℝ) := by simpa using hu
          exact (div_le_iff₀ hLpos).2 hu'
      simp [BallGreen.cutField, hzero]
      positivity
    · have hden : (L : ℝ) ≤ 1 + BallGreen.latticeNorm u := by linarith
      have hpoint : BallGreen.cutField r L φ u ≤
          C₀ / (1 + BallGreen.latticeNorm u) ^ 2 := by
        calc
          BallGreen.cutField r L φ u =
              Sandpile.killedGreen (BallGreen.box r) 0 u *
                φ (BallGreen.latticeNorm u / (L : ℝ)) := rfl
          _ ≤ Sandpile.green 4 0 u * 1 := by
            exact mul_le_mul hg.2.1 hphi.2 hphi.1 (Sandpile.green_nonneg 0 u)
          _ = Sandpile.green 4 0 u := by ring
          _ ≤ C₀ / (1 + BallGreen.latticeNorm u) ^ 2 := hg.2.2
      have hdenpow : (L : ℝ) ^ 2 ≤ (1 + BallGreen.latticeNorm u) ^ 2 :=
        pow_le_pow_left₀ hLpos.le hden 2
      have hquot : C₀ / (1 + BallGreen.latticeNorm u) ^ 2 ≤
          C₁ / (L : ℝ) ^ 2 := by
        exact (div_le_div_of_nonneg_left hC₀.le (by positivity) hdenpow).trans
          (by gcongr)
      exact hpoint.trans hquot
  have hzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.boxFinset 0 r →
      BallGreen.cutField r L φ u = 0 := by
    intro u hu
    exact Sandpile.cutField_eq_zero_of_notMem_boxFinset r L φ hu
  have hcube_support :
      (∑' u : Sandpile.Site 4, BallGreen.cutField r L φ u ^ 3) =
        ∑ u ∈ LatticeProb.boxFinset 0 r, BallGreen.cutField r L φ u ^ 3 := by
    exact tsum_eq_sum (fun u hu => by rw [hzero u hu, zero_pow (by norm_num)])
  have hM : 1 ≤ (L + 1) / 2 := by omega
  let M : ℕ := (L + 1) / 2
  have hMle : ∀ u : Sandpile.Site 4,
      BallGreen.cutField r L φ u ≠ 0 → M ≤ LatticeProb.supNorm u := by
    intro u hu
    have hcutpos : 0 < BallGreen.cutField r L φ u :=
      lt_of_le_of_ne (Sandpile.cutField_nonneg r L hφ u) (Ne.symm hu)
    have hnot : ¬ BallGreen.latticeNorm u ≤ (L : ℝ) := by
      intro hnorm
      have hz : φ (BallGreen.latticeNorm u / (L : ℝ)) = 0 := by
        apply hφ.2.2.1
        · exact div_nonneg (Real.sqrt_nonneg _) hLpos.le
        · have hnorm' : BallGreen.latticeNorm u ≤ 1 * (L : ℝ) := by simpa using hnorm
          exact (div_le_iff₀ hLpos).2 hnorm'
      apply hu
      simp [BallGreen.cutField, hz]
    have heuclid : BallGreen.latticeNorm u ≤ 2 * (LatticeProb.supNorm u : ℝ) := by
      have hsqrt : Real.sqrt (4 : ℝ) = 2 := by norm_num
      simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm, hsqrt] using
        (LatticeProb.euclidNorm_le_sqrt_mul_supNorm u)
    have hstrict : (L : ℝ) < 2 * (LatticeProb.supNorm u : ℝ) :=
      lt_of_lt_of_le (lt_of_not_ge hnot) heuclid
    have hnat : L < 2 * LatticeProb.supNorm u := by exact_mod_cast hstrict
    dsimp [M]
    omega
  let f : ℕ → ℝ := fun k => C₁ ^ 3 / (1 + (k : ℝ)) ^ 6
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    positivity
  have hterm : ∀ u : Sandpile.Site 4,
      BallGreen.cutField r L φ u ^ 3 ≤ f (LatticeProb.supNorm u) := by
    intro u
    have hcut := Sandpile.cutField_nonneg r L hφ u
    have hbound : BallGreen.cutField r L φ u ≤
        C₁ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2 := by
      by_cases hz : BallGreen.cutField r L φ u = 0
      · rw [hz]
        positivity
      · have hnot : ¬ BallGreen.latticeNorm u ≤ (L : ℝ) := by
          intro hnorm
          have hφ0 : φ (BallGreen.latticeNorm u / (L : ℝ)) = 0 := by
            apply hφ.2.2.1
            · exact div_nonneg (Real.sqrt_nonneg _) hLpos.le
            · have hnorm' : BallGreen.latticeNorm u ≤ 1 * (L : ℝ) := by simpa using hnorm
              exact (div_le_iff₀ hLpos).2 hnorm'
          exact hz (by simp [BallGreen.cutField, hφ0])
        have hg := hclause1 r hr u
        have hphi := hφ.1 (BallGreen.latticeNorm u / (L : ℝ))
          (div_nonneg (Real.sqrt_nonneg _) hLpos.le)
        have hpoint : BallGreen.cutField r L φ u ≤
            C₀ / (1 + BallGreen.latticeNorm u) ^ 2 := by
          calc
            BallGreen.cutField r L φ u =
                Sandpile.killedGreen (BallGreen.box r) 0 u *
                  φ (BallGreen.latticeNorm u / (L : ℝ)) := rfl
            _ ≤ Sandpile.green 4 0 u * 1 := by
              exact mul_le_mul hg.2.1 hphi.2 hphi.1 (Sandpile.green_nonneg 0 u)
            _ = Sandpile.green 4 0 u := by ring
            _ ≤ C₀ / (1 + BallGreen.latticeNorm u) ^ 2 := hg.2.2
        have hnorm : (1 + (LatticeProb.supNorm u : ℝ)) ≤
            1 + BallGreen.latticeNorm u := by
          simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using
            add_le_add_right (LatticeProb.supNorm_le_euclidNorm u) 1
        have hpow := pow_le_pow_left₀ (by positivity) hnorm 2
        exact hpoint.trans ((div_le_div_of_nonneg_left hC₀.le (by positivity) hpow).trans
          (by gcongr))
    dsimp [f]
    calc
      BallGreen.cutField r L φ u ^ 3 ≤
          (C₁ / (1 + (LatticeProb.supNorm u : ℝ)) ^ 2) ^ 3 :=
        pow_le_pow_left₀ hcut hbound 3
      _ = f (LatticeProb.supNorm u) := by
        dsimp [f]
        rw [div_pow]
        ring
  let F : Finset (Sandpile.Site 4) :=
    (LatticeProb.boxFinset 0 r).filter (fun u => BallGreen.cutField r L φ u ≠ 0)
  have hF : ∀ u ∈ F, M ≤ LatticeProb.supNorm u := by
    intro u hu
    exact hMle u (Finset.mem_filter.mp hu).2
  have hcubeF :
      (∑ u ∈ LatticeProb.boxFinset 0 r, BallGreen.cutField r L φ u ^ 3) =
        ∑ u ∈ F, BallGreen.cutField r L φ u ^ 3 := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _)
      (fun u hu huf => by
        have hz : BallGreen.cutField r L φ u = 0 := by
          by_contra hz
          exact huf (Finset.mem_filter.mpr ⟨hu, hz⟩)
        simp [hz])
  have hsumF :
      (∑ u ∈ F, BallGreen.cutField r L φ u ^ 3) ≤
        ∑ u ∈ F, f (LatticeProb.supNorm u) :=
    Finset.sum_le_sum fun u hu => hterm u
  have hradial := LatticeProb.sum_finset_radial_tail_le f hf hM F hF
  have hshell : ∀ j ∈ Finset.Icc M (F.sup LatticeProb.supNorm),
      (LatticeProb.shellCard 4 j : ℝ) * f j ≤
        64 * C₁ ^ 3 * ((j : ℝ))⁻¹ ^ 3 := by
    intro j hj
    have hj1 : 1 ≤ j := le_trans hM (Finset.mem_Icc.mp hj).1
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hsc := LatticeProb.shellCard_le 4 hj1
    dsimp [f]
    have hpow : (2 * (j : ℝ) + 1) ^ 3 ≤ 8 * (1 + (j : ℝ)) ^ 3 := by
      calc
        (2 * (j : ℝ) + 1) ^ 3 ≤ (2 * (1 + (j : ℝ))) ^ 3 := by
          exact pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = 8 * (1 + (j : ℝ)) ^ 3 := by ring
    have hbase : (0 : ℝ) ≤ C₁ ^ 3 := by positivity
    calc
      (LatticeProb.shellCard 4 j : ℝ) * (C₁ ^ 3 / (1 + (j : ℝ)) ^ 6)
          ≤ (8 * (2 * (j : ℝ) + 1) ^ 3) *
              (C₁ ^ 3 / (1 + (j : ℝ)) ^ 6) := by
            have hsc' : (LatticeProb.shellCard 4 j : ℝ) ≤
                8 * (2 * (j : ℝ) + 1) ^ 3 := by
              norm_num at hsc ⊢
              exact hsc
            exact mul_le_mul_of_nonneg_right hsc' (by positivity)
      _ ≤ 64 * C₁ ^ 3 / (1 + (j : ℝ)) ^ 3 := by
            have hden : (0 : ℝ) < 1 + (j : ℝ) := by positivity
            calc
              8 * (2 * (j : ℝ) + 1) ^ 3 *
                    (C₁ ^ 3 / (1 + (j : ℝ)) ^ 6) ≤
                  (8 * (8 * (1 + (j : ℝ)) ^ 3)) *
                    (C₁ ^ 3 / (1 + (j : ℝ)) ^ 6) := by gcongr
              _ = 64 * C₁ ^ 3 / (1 + (j : ℝ)) ^ 3 := by
                field_simp
                ring
      _ ≤ 64 * C₁ ^ 3 * ((j : ℝ))⁻¹ ^ 3 := by
            have hi : (1 + (j : ℝ))⁻¹ ≤ ((j : ℝ))⁻¹ :=
              inv_anti₀ hjpos (by linarith)
            have hle : ((1 + (j : ℝ))⁻¹) ^ 3 ≤ ((j : ℝ))⁻¹ ^ 3 :=
              pow_le_pow_left₀ (by positivity) hi 3
            rw [show 64 * C₁ ^ 3 / (1 + (j : ℝ)) ^ 3 =
              64 * C₁ ^ 3 * ((1 + (j : ℝ))⁻¹) ^ 3 by field_simp]
            exact mul_le_mul_of_nonneg_left hle (by positivity)
  have hsum_inv3 :
      (∑ j ∈ Finset.Icc M (F.sup LatticeProb.supNorm), ((j : ℝ))⁻¹ ^ 3) ≤
        2 / (M : ℝ) ^ 2 := by
    have hI : Finset.Icc M (F.sup LatticeProb.supNorm) =
        Finset.Ico M (F.sup LatticeProb.supNorm + 1) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hI]
    have hsq := LatticeProb.sum_Ico_inv_sq_le hM (F.sup LatticeProb.supNorm + 1)
    have hsq' :
        (∑ j ∈ Finset.Ico M (F.sup LatticeProb.supNorm + 1),
          ((j : ℝ))⁻¹ ^ 2) ≤ 2 / (M : ℝ) := by
      simpa [inv_pow] using hsq
    have hterm' : ∀ j ∈ Finset.Ico M (F.sup LatticeProb.supNorm + 1),
        ((j : ℝ))⁻¹ ^ 3 ≤ (M : ℝ)⁻¹ * ((j : ℝ))⁻¹ ^ 2 := by
      intro j hj
      have hMjNat : M ≤ j := (Finset.mem_Ico.mp hj).1
      have hj1 : 1 ≤ j := le_trans hM hMjNat
      have hjpos : (0 : ℝ) < (j : ℝ) := by
        exact_mod_cast (show 0 < j by omega)
      have hMj : (M : ℝ) ≤ (j : ℝ) := by exact_mod_cast hMjNat
      have hi : ((j : ℝ))⁻¹ ≤ (M : ℝ)⁻¹ := by
        exact inv_anti₀ (by exact_mod_cast hM) (by linarith)
      rw [show ((j : ℝ))⁻¹ ^ 3 = ((j : ℝ))⁻¹ * ((j : ℝ))⁻¹ ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    calc
      _ ≤ ∑ j ∈ Finset.Ico M (F.sup LatticeProb.supNorm + 1),
          (M : ℝ)⁻¹ * ((j : ℝ))⁻¹ ^ 2 := Finset.sum_le_sum hterm'
      _ = (M : ℝ)⁻¹ * ∑ j ∈ Finset.Ico M (F.sup LatticeProb.supNorm + 1),
          ((j : ℝ))⁻¹ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (M : ℝ)⁻¹ * (2 / (M : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsq' (by positivity)
      _ = 2 / (M : ℝ) ^ 2 := by field_simp
  have hradial_bound :
      (∑ j ∈ Finset.Icc M (F.sup LatticeProb.supNorm),
        (LatticeProb.shellCard 4 j : ℝ) * f j) ≤
        128 * C₁ ^ 3 / (M : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc M (F.sup LatticeProb.supNorm),
          64 * C₁ ^ 3 * ((j : ℝ))⁻¹ ^ 3 := Finset.sum_le_sum hshell
      _ = 64 * C₁ ^ 3 * ∑ j ∈ Finset.Icc M (F.sup LatticeProb.supNorm),
          ((j : ℝ))⁻¹ ^ 3 := by rw [Finset.mul_sum]
      _ ≤ 64 * C₁ ^ 3 * (2 / (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_inv3 (by positivity)
      _ = 128 * C₁ ^ 3 / (M : ℝ) ^ 2 := by ring
  have hLM : (L : ℝ) / 2 ≤ (M : ℝ) := by
    have hnat : L ≤ 2 * M := by
      dsimp [M]
      omega
    have hnat' : (L : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hnat
    linarith
  have hscale : 128 * C₁ ^ 3 / (M : ℝ) ^ 2 ≤ C / (L : ℝ) ^ 2 := by
    dsimp [C]
    have hhalf : (0 : ℝ) < (L : ℝ) / 2 := by positivity
    have hden : ((L : ℝ) / 2) ^ 2 ≤ (M : ℝ) ^ 2 :=
      pow_le_pow_left₀ hhalf.le hLM 2
    calc
      128 * C₁ ^ 3 / (M : ℝ) ^ 2 ≤
          128 * C₁ ^ 3 / ((L : ℝ) / 2) ^ 2 := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = C₁ ^ 3 * 512 / (L : ℝ) ^ 2 := by field_simp; ring
  constructor
  · intro u
    exact (hsup u).trans (by
      have hC1C : C₁ ≤ C := by
        dsimp [C]
        have hpow : C₁ ≤ C₁ ^ 3 := by
          calc
            C₁ = C₁ * 1 := by ring
            _ ≤ C₁ * C₁ := mul_le_mul_of_nonneg_left hC₁one hC₁.le
            _ ≤ (C₁ * C₁) * C₁ := by
              calc
                C₁ * C₁ = (C₁ * C₁) * 1 := by ring
                _ ≤ (C₁ * C₁) * C₁ :=
                  mul_le_mul_of_nonneg_left hC₁one (by positivity)
            _ = C₁ ^ 3 := by ring
        nlinarith [hpow]
      exact div_le_div_of_nonneg_right hC1C (by positivity))
  · rw [hcube_support, hcubeF]
    exact (hsumF.trans (hradial.trans hradial_bound)).trans hscale

/-! These are the three deterministic obligations not discharged in this file yet.
They are named propositions, rather than assumed theorems, so the assembly below
can be checked independently without adding an unproved assumption. -/

def aux_ballgreen_clause4 : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
      (∑' u : {u : Sandpile.Site 4 //
          (R : ℝ) ≤ BallGreen.latticeNorm u ∧
            BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
        (Sandpile.killedGreen (BallGreen.box r) 0
            ((u : Sandpile.Site 4) + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
        C / (R : ℝ) ^ 2

def aux_ballgreen_clause6 : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      ∀ φ : ℝ → ℝ, BallGreen.IsCutoff φ → ∀ M : ℝ, 1 ≤ M →
        ∀ w : Sandpile.Site 4, BallGreen.latticeNorm w ≤ M * (L : ℝ) →
          (∑' u : Sandpile.Site 4,
            (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2) ≤
            C * (1 + M) ^ 4

def aux_ballgreen_clause7 : Prop :=
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : ℝ, 1 ≤ A →
      (∀ u : Sandpile.Site 4,
          |BallGreen.timeTail r A u| ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A)) ∧
        (∑' u : Sandpile.Site 4, BallGreen.timeTail r A u ^ 2) ≤
          C * Real.exp (-c * A)

theorem aux_ballgreen_assemble
    (h1 : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∀ u : Sandpile.Site 4,
        0 ≤ Sandpile.killedGreen (BallGreen.box r) 0 u ∧
          Sandpile.killedGreen (BallGreen.box r) 0 u ≤ Sandpile.green 4 0 u ∧
          Sandpile.green 4 0 u ≤ C / (1 + BallGreen.latticeNorm u) ^ 2)
    (h2 : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      (∑' u : Sandpile.Site 4,
        Sandpile.killedGreen (BallGreen.box r) 0 u ^ 2) ≤ C * Real.log (r : ℝ))
    (h3 : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      (∑' u : {u : Sandpile.Site 4 //
          BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
        Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4) ^ 2) ≤
        C * Real.log (2 * (L : ℝ) + 2))
    (h4 : aux_ballgreen_clause4)
    (h5 : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L →
      ∀ φ : ℝ → ℝ, BallGreen.IsCutoff φ →
        (∀ u : Sandpile.Site 4,
            |BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
          (∑' u : Sandpile.Site 4, BallGreen.cutField r L φ u ^ 3) ≤
            C / (L : ℝ) ^ 2)
    (h6 : aux_ballgreen_clause6)
    (h7 : aux_ballgreen_clause7) :
    Sandpile.External.BallGreenBounds := by
  obtain ⟨C₁, hC₁, h1⟩ := h1
  obtain ⟨C₂, hC₂, h2⟩ := h2
  obtain ⟨C₃, hC₃, h3⟩ := h3
  obtain ⟨C₄, hC₄, h4⟩ := h4
  obtain ⟨C₅, hC₅, h5⟩ := h5
  obtain ⟨C₆, hC₆, h6⟩ := h6
  obtain ⟨C₇, c, hC₇, hc, h7⟩ := h7
  let C : ℝ := max C₁ (max C₂ (max C₃ (max C₄ (max C₅ (max C₆ C₇)))))
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hC₁le : C₁ ≤ C := by dsimp [C]; exact le_max_left _ _
  have hC₂le : C₂ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃le : C₃ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC₄le : C₄ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hC₅le : C₅ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hC₆le : C₆ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
  have hC₇le : C₇ ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _)
            (le_trans (le_max_right _ _) (le_max_right _ _)))))
  refine ⟨C, c, hC, hc, fun r hr => ?_⟩
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hlogr : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have h := h1 r hr u
    exact ⟨h.1, h.2.1, h.2.2.trans
      (div_le_div_of_nonneg_right hC₁le (by positivity))⟩
  · exact (h2 r hr).trans (mul_le_mul_of_nonneg_right hC₂le hlogr)
  · intro L hL
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hlog : 0 ≤ Real.log (2 * (L : ℝ) + 2) :=
      Real.log_nonneg (by nlinarith)
    exact (h3 r hr L hL).trans (mul_le_mul_of_nonneg_right hC₃le hlog)
  · intro R hR i
    exact (h4 r hr R hR i).trans
      (div_le_div_of_nonneg_right hC₄le (by positivity))
  · intro L hL φ hφ
    obtain ⟨hsup, hcube⟩ := h5 r hr L hL φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro u
      exact hsup u |>.trans (div_le_div_of_nonneg_right hC₅le (by positivity))
    · exact hcube.trans (div_le_div_of_nonneg_right hC₅le (by positivity))
    · intro M hM w hw
      exact h6 r hr L hL φ hφ M hM w hw |>.trans
        (mul_le_mul_of_nonneg_right hC₆le (by positivity))
  · intro A hA
    obtain ⟨hpoint, hsum⟩ := h7 r hr A hA
    refine ⟨?_, ?_⟩
    · intro u
      exact hpoint u |>.trans (by
        gcongr)
    · exact hsum.trans (mul_le_mul_of_nonneg_right hC₇le (by positivity))

end Sandpile.External

namespace Sandpile.External

private theorem aux_bg4_caccioppoli_support {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ B, LatticeProb.Network.netLaplacian G c f x = 0)
    (htest : ∀ x, x ∉ B → f x * η x ^ 2 = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
      4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hg : ∀ x, x ∉ B → f x * η x ^ 2 = 0 := htest
  have hform := LatticeProb.Network.formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) hg hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * LatticeProb.Network.netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x hx]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
        2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
          4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [sq_nonneg ((f x - f y) * η y + (f x + f y) * (η x - η y)),
      sq_nonneg (2 * f x - f y), sq_nonneg (f x), sq_nonneg (f y),
      sq_nonneg (η x - η y), mul_nonneg hc0 (sq_nonneg (f x - f y)),
      mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2
        ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2) +
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) =
          2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2) := by
        simp only [LatticeProb.Network.formOn, Finset.mul_sum]
      have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) =
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        simp only [Finset.mul_sum]
      rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))) =
          (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) +
            ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
      rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      rw [hform]
      ring

end Sandpile.External

namespace Sandpile.External

private theorem aux_bg4_supNorm_adj {x y : Sandpile.Site 4}
    (hxy : (LatticeProb.lattice 4).Adj x y) :
    LatticeProb.supNorm y ≤ LatticeProb.supNorm x + 1 ∧
      LatticeProb.supNorm x ≤ LatticeProb.supNorm y + 1 := by
  have hunit : ∀ i : Fin 4, LatticeProb.supNorm (LatticeProb.unit i) ≤ 1 := by
    intro i
    rw [LatticeProb.supNorm_le_iff]
    intro j
    by_cases hji : j = i
    · subst j
      simp [LatticeProb.unit]
    · simp [LatticeProb.unit, hji]
  have hplus : ∀ z : Sandpile.Site 4, ∀ i : Fin 4,
      LatticeProb.supNorm (z + LatticeProb.unit i) ≤ LatticeProb.supNorm z + 1 := by
    intro z i
    exact (LatticeProb.supNorm_add_le z (LatticeProb.unit i)).trans
      (Nat.add_le_add_left (hunit i) _)
  have hminus : ∀ z : Sandpile.Site 4, ∀ i : Fin 4,
      LatticeProb.supNorm (z - LatticeProb.unit i) ≤ LatticeProb.supNorm z + 1 := by
    intro z i
    calc
      LatticeProb.supNorm (z - LatticeProb.unit i) ≤
          LatticeProb.supNorm z + LatticeProb.supNorm (-LatticeProb.unit i) := by
            simpa only [sub_eq_add_neg] using
              LatticeProb.supNorm_add_le z (-LatticeProb.unit i)
      _ = LatticeProb.supNorm z + LatticeProb.supNorm (LatticeProb.unit i) := by
            rw [LatticeProb.supNorm_neg]
      _ ≤ LatticeProb.supNorm z + 1 := Nat.add_le_add_left (hunit i) _
  have hforward : LatticeProb.supNorm y ≤ LatticeProb.supNorm x + 1 := by
    rcases (LatticeProb.Graph.Zd.adj_iff.mp hxy) with ⟨i, rfl | rfl⟩
    · exact hplus x i
    · exact hminus x i
  have hback : LatticeProb.supNorm x ≤ LatticeProb.supNorm y + 1 := by
    rcases (LatticeProb.Graph.Zd.adj_iff.mp hxy) with ⟨i, hy | hx⟩
    · have h := hminus y i
      rw [hy] at h
      have heq : (x + LatticeProb.unit i) - LatticeProb.unit i = x := by abel
      rw [heq] at h
      rw [hy]
      exact h
    · have h := hplus y i
      rw [hx] at h
      have heq : (x - LatticeProb.unit i) + LatticeProb.unit i = x := by abel
      rw [heq] at h
      rw [hx]
      exact h
  exact ⟨hforward, hback⟩

private theorem aux_bg4_caccioppoli {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ B, LatticeProb.Network.netLaplacian G c f x = 0)
    (hη : ∀ x, x ∉ B → η x = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
      4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hg : ∀ x, x ∉ B → f x * η x ^ 2 = 0 := fun x hx => by rw [hη x hx]; ring
  have hform := LatticeProb.Network.formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) hg hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * LatticeProb.Network.netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x hx]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
        2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
          4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [sq_nonneg ((f x - f y) * η y + (f x + f y) * (η x - η y)),
      sq_nonneg (2 * f x - f y), sq_nonneg (f x), sq_nonneg (f y),
      sq_nonneg (η x - η y), mul_nonneg hc0 (sq_nonneg (f x - f y)),
      mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2
        ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
      Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2) +
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) =
          2 * LatticeProb.Network.formOn G c S f (fun x => f x * η x ^ 2) := by
        simp only [LatticeProb.Network.formOn, Finset.mul_sum]
      have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) =
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        simp only [Finset.mul_sum]
      rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))) =
          (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) +
            ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
      rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      rw [hform]
      ring

end Sandpile.External

namespace Sandpile.External

private theorem aux_bg4_box_eq_set (r : ℕ) :
    BallGreen.box r = (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set (Sandpile.Site 4)) := by
  ext u
  simp only [BallGreen.box, Set.mem_setOf_eq, Finset.mem_coe, LatticeProb.mem_boxFinset_iff,
    Pi.zero_apply, sub_zero]
  constructor
  · intro h i
    have hi : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by exact_mod_cast h i
    simpa only [Int.abs_eq_natAbs] using hi
  · intro h i
    have hi : |u i| ≤ (r : ℤ) := h i
    have hi' : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by
      simpa only [Int.abs_eq_natAbs] using hi
    exact_mod_cast hi'

private theorem aux_bg4_killed_eq_network (r : ℕ) (u : Sandpile.Site 4) :
    Sandpile.killedGreen (BallGreen.box r) 0 u =
      8 * LatticeProb.Graph.killedGreenReal (LatticeProb.lattice 4)
        (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set (Sandpile.Site 4)) 0 u := by
  classical
  have hbox := aux_bg4_box_eq_set r
  let q : Sandpile.Site 4 := fun _ => (r + 1 : ℕ)
  have hq : q ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
    intro hq
    have hcoord := (LatticeProb.mem_boxFinset_iff.mp hq) (0 : Fin 4)
    dsimp [q] at hcoord
    have hcoord' : (r : ℤ) + 1 ≤ (r : ℤ) := by
      rw [sub_zero, abs_of_nonneg (by omega : (0 : ℤ) ≤ (r : ℤ) + 1)] at hcoord
      exact hcoord
    omega
  have hconn : (LatticeProb.lattice 4).Connected := by
    exact LatticeProb.Graph.Zd.latticeConnected 4
  rw [hbox, LatticeProb.Network.killedGreenReal_eq_tsum hconn
    (LatticeProb.boxFinset (0 : Sandpile.Site 4) r) hq 0 u]
  norm_num [LatticeProb.Graph.Zd.degree_eq]
  rw [Sandpile.killedGreen]
  field_simp
  congr 1
  funext k
  rw [← Sandpile.killedKernel_eq_graph]

noncomputable def aux_bg4_eta (R : ℕ) (x : Sandpile.Site 4) : ℝ :=
  min (max 0 (((LatticeProb.supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)))
    (max 0 (min 1 ((4 * (R : ℝ) - (LatticeProb.supNorm x : ℝ)) / (R : ℝ))))

private theorem aux_bg4_eta_zero {R : ℕ} (hR : 0 < R) (x : Sandpile.Site 4)
    (hx : (LatticeProb.supNorm x : ℝ) ≤ (R : ℝ) / 8) :
    aux_bg4_eta R x = 0 := by
  dsimp [aux_bg4_eta]
  have hq : ((LatticeProb.supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8) ≤ 0 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) / 8)).2
    linarith
  rw [max_eq_left hq]
  simp

private theorem aux_bg4_eta_one {R : ℕ} (hR : 0 < R) (x : Sandpile.Site 4)
    (hx₁ : (R : ℝ) / 4 ≤ (LatticeProb.supNorm x : ℝ))
    (hx₂ : (LatticeProb.supNorm x : ℝ) ≤ 3 * (R : ℝ)) :
    aux_bg4_eta R x = 1 := by
  dsimp [aux_bg4_eta]
  have hi : 1 ≤ ((LatticeProb.supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) / 8)).2
    linarith
  have ho : 1 ≤ (4 * (R : ℝ) - (LatticeProb.supNorm x : ℝ)) / (R : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ))).2
    linarith
  have hia : 1 ≤ max 0 (((LatticeProb.supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)) :=
    le_max_of_le_right hi
  have hob : max 0 (min 1 ((4 * (R : ℝ) - (LatticeProb.supNorm x : ℝ)) / (R : ℝ))) = 1 := by
    rw [min_eq_left ho, max_eq_right (by norm_num)]
  rw [hob, min_eq_right hia]

private theorem aux_bg4_eta_lipschitz {R : ℕ} (hR : 0 < R)
    {x y : Sandpile.Site 4} (hxy : (LatticeProb.lattice 4).Adj x y) :
    |aux_bg4_eta R x - aux_bg4_eta R y| ≤ 8 / (R : ℝ) := by
  have hs := aux_bg4_supNorm_adj hxy
  have hdist : |(LatticeProb.supNorm x : ℝ) - (LatticeProb.supNorm y : ℝ)| ≤ 1 := by
    have h1 : (LatticeProb.supNorm y : ℝ) ≤ (LatticeProb.supNorm x : ℝ) + 1 := by
      exact_mod_cast hs.1
    have h2 : (LatticeProb.supNorm x : ℝ) ≤ (LatticeProb.supNorm y : ℝ) + 1 := by
      exact_mod_cast hs.2
    rw [abs_le]
    constructor <;> linarith
  let k₈ : NNReal := ⟨8 / (R : ℝ), by positivity⟩
  let k₁ : NNReal := ⟨1 / (R : ℝ), by positivity⟩
  have hk₈ : (k₈ : ℝ) = 8 / (R : ℝ) := by rfl
  have hk₁ : (k₁ : ℝ) = 1 / (R : ℝ) := by rfl
  have hlin₈ : LipschitzWith k₈ (fun s : ℝ => (s - (R : ℝ) / 8) / ((R : ℝ) / 8)) := by
    intro a b
    rw [edist_dist, edist_dist]
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k₈ : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    change |(a - (R : ℝ) / 8) / ((R : ℝ) / 8) -
        (b - (R : ℝ) / 8) / ((R : ℝ) / 8)| ≤ (k₈ : ℝ) * |a - b|
    dsimp [k₈]
    rw [show (a - (R : ℝ) / 8) / ((R : ℝ) / 8) -
        (b - (R : ℝ) / 8) / ((R : ℝ) / 8) =
          (a - b) / ((R : ℝ) / 8) by ring]
    rw [abs_div]
    have hfac : |(R : ℝ) / 8| * (k₈ : ℝ) = 1 := by
      dsimp [k₈]
      rw [abs_of_pos (by positivity : (0 : ℝ) < (R : ℝ) / 8)]
      change (R : ℝ) / 8 * (8 / (R : ℝ)) = 1
      field_simp
    rw [div_eq_mul_inv]
    have hrecip : |(R : ℝ) / 8|⁻¹ = (k₈ : ℝ) := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < (R : ℝ) / 8)]
      dsimp [k₈]
      change ((R : ℝ) / 8)⁻¹ = 8 / (R : ℝ)
      field_simp
    rw [hrecip]
    rw [hk₈]
    simp [mul_comm]
  have hlin₁ : LipschitzWith k₁ (fun s : ℝ =>
      (4 * (R : ℝ) - s) / (R : ℝ)) := by
    intro a b
    rw [edist_dist, edist_dist]
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k₁ : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    change |(4 * (R : ℝ) - a) / (R : ℝ) -
        (4 * (R : ℝ) - b) / (R : ℝ)| ≤ (k₁ : ℝ) * |a - b|
    dsimp [k₁]
    rw [show (4 * (R : ℝ) - a) / (R : ℝ) -
        (4 * (R : ℝ) - b) / (R : ℝ) = (b - a) / (R : ℝ) by ring,
      abs_div]
    rw [abs_sub_comm]
    have hfac : |(R : ℝ)| * (k₁ : ℝ) = 1 := by
      dsimp [k₁]
      rw [abs_of_pos (by positivity : (0 : ℝ) < (R : ℝ))]
      change (R : ℝ) * (1 / (R : ℝ)) = 1
      field_simp
    rw [div_eq_mul_inv]
    have hrecip : |(R : ℝ)|⁻¹ = (k₁ : ℝ) := by
      rw [abs_of_pos (by positivity : (0 : ℝ) < (R : ℝ))]
      dsimp [k₁]
      change ((R : ℝ))⁻¹ = 1 / (R : ℝ)
      simp [one_div]
    rw [hrecip]
    rw [hk₁]
    simp [mul_comm]
  have hzero : LipschitzWith (0 : NNReal) (fun _ : ℝ => (0 : ℝ)) := by
    intro a b
    simp
  have hone : LipschitzWith (0 : NNReal) (fun _ : ℝ => (1 : ℝ)) := by
    intro a b
    simp
  have hA : LipschitzWith k₈ (fun s : ℝ =>
      max 0 ((s - (R : ℝ) / 8) / ((R : ℝ) / 8))) := by
    simpa [show max (0 : NNReal) k₈ = k₈ by
      apply le_antisymm (max_le (by simp) le_rfl) (le_max_right _ _)] using hzero.max hlin₈
  have hB₀ : LipschitzWith k₁ (fun s : ℝ =>
      min 1 ((4 * (R : ℝ) - s) / (R : ℝ))) := by
    simpa [show max (0 : NNReal) k₁ = k₁ by
      apply le_antisymm (max_le (by simp) le_rfl) (le_max_right _ _)] using hone.min hlin₁
  have hB : LipschitzWith k₁ (fun s : ℝ =>
      max 0 (min 1 ((4 * (R : ℝ) - s) / (R : ℝ)))) := by
    simpa [show max (0 : NNReal) k₁ = k₁ by
      apply le_antisymm (max_le (by simp) le_rfl) (le_max_right _ _)] using hzero.max hB₀
  have hmax : max k₈ k₁ = k₈ := by
    apply le_antisymm
    · apply max_le le_rfl
      exact_mod_cast (show 1 / (R : ℝ) ≤ 8 / (R : ℝ) by
        gcongr
        norm_num)
    · exact le_max_left _ _
  have hmin := hA.min hB
  have hxy' := hmin (LatticeProb.supNorm x : ℝ) (LatticeProb.supNorm y : ℝ)
  rw [hmax] at hxy'
  rw [edist_dist, edist_dist] at hxy'
  rw [ENNReal.coe_nnreal_eq,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k₈ : ℝ))] at hxy'
  have hto := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hxy'
  have hreal : |aux_bg4_eta R x - aux_bg4_eta R y| ≤ (k₈ : ℝ) *
      |(LatticeProb.supNorm x : ℝ) - (LatticeProb.supNorm y : ℝ)| := by
    simpa [aux_bg4_eta, Real.dist_eq] using hto
  have hxy'' : |aux_bg4_eta R x - aux_bg4_eta R y| ≤
      (8 / (R : ℝ)) * |(LatticeProb.supNorm x : ℝ) - (LatticeProb.supNorm y : ℝ)| := by
    simpa [hk₈] using hreal
  exact hxy''.trans (by
    have hk : (0 : ℝ) ≤ 8 / (R : ℝ) := by positivity
    simpa using mul_le_mul_of_nonneg_left hdist hk)

private theorem aux_bg4_eta_zero_outer {R : ℕ} (hR : 0 < R) (x : Sandpile.Site 4)
    (hx : 4 * (R : ℝ) ≤ (LatticeProb.supNorm x : ℝ)) :
    aux_bg4_eta R x = 0 := by
  dsimp [aux_bg4_eta]
  have hq : (4 * (R : ℝ) - (LatticeProb.supNorm x : ℝ)) / (R : ℝ) ≤ 0 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ))).2
    linarith
  rw [min_eq_right (by linarith :
    (4 * (R : ℝ) - (LatticeProb.supNorm x : ℝ)) / (R : ℝ) ≤ 1), max_eq_left hq]
  have hi : 0 ≤ max 0 (((LatticeProb.supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)) :=
    le_max_left _ _
  rw [min_eq_right hi]

theorem aux_ballgreen_clause4_holds : aux_ballgreen_clause4 := by
  obtain ⟨C₀, hC₀, hclause1⟩ := aux_ballgreen_clause1
  let C : ℝ := C₀ ^ 2 * (2 ^ 40 * 11 ^ 4 + 4 * 63 ^ 4 * 256)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro r hr R hR i
  by_cases hRbig : 16 ≤ R
  · have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    have hRbig' : (16 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRbig
    let G := LatticeProb.lattice 4
    let Cfin : Finset (Sandpile.Site 4) := LatticeProb.boxFinset 0 r
    let S : Finset (Sandpile.Site 4) := LatticeProb.boxFinset 0 (4 * R + 1)
    let B : Finset (Sandpile.Site 4) :=
      (LatticeProb.boxFinset 0 (4 * R)).filter
        (fun x => x ∈ Cfin ∧ (R : ℝ) / 8 < (LatticeProb.supNorm x : ℝ))
    let q : Sandpile.Site 4 := fun _ => (r + 1 : ℕ)
    have hq : q ∉ (Cfin : Set (Sandpile.Site 4)) := by
      intro hq
      have hcoord := (LatticeProb.mem_boxFinset_iff.mp hq) (0 : Fin 4)
      dsimp [q, Cfin] at hcoord
      have hcoord' : (r : ℤ) + 1 ≤ (r : ℤ) := by
        rw [sub_zero, abs_of_nonneg (by omega : (0 : ℤ) ≤ (r : ℤ) + 1)] at hcoord
        exact hcoord
      omega
    have hconn : G.Connected := by
      exact LatticeProb.Graph.Zd.latticeConnected 4
    let g : Sandpile.Site 4 → ℝ :=
      LatticeProb.Graph.killedGreenReal G (Cfin : Set (Sandpile.Site 4)) 0
    let f : Sandpile.Site 4 → ℝ := fun x =>
      Sandpile.killedGreen (BallGreen.box r) 0 x
    let eta : Sandpile.Site 4 → ℝ := aux_bg4_eta R
    have hf_eq : ∀ x : Sandpile.Site 4, f x = 8 * g x := by
      intro x
      dsimp [f, g, Cfin, G]
      exact aux_bg4_killed_eq_network r x
    have hCzero : (0 : Sandpile.Site 4) ∈ Cfin := by
      dsimp [Cfin]
      rw [LatticeProb.mem_boxFinset_zero_iff]
      simp [LatticeProb.supNorm]
    have hf : ∀ x ∈ B,
        LatticeProb.Network.netLaplacian G (LatticeProb.Network.unitCond G) f x = 0 := by
      intro x hx
      have hxB := Finset.mem_filter.mp hx
      have hxC : x ∈ (Cfin : Set (Sandpile.Site 4)) := hxB.2.1
      have hx0 : x ≠ 0 := by
        intro hzero
        subst hzero
        have hlarge : (2 : ℝ) ≤ (R : ℝ) / 8 := by
          have : (16 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRbig
          linarith
        have hbad := hxB.2.2
        simp at hbad
        linarith
      have hh := LatticeProb.Network.harmonic_killedGreenReal hconn Cfin hCzero hq hxC hx0
      rw [LatticeProb.Network.netLaplacian_unitCond]
      rw [LatticeProb.Graph.laplacian]
      simp only [hf_eq]
      calc
        (∑ y ∈ G.neighborFinset x, (8 * g y - 8 * g x)) =
            8 * ∑ y ∈ G.neighborFinset x, (g y - g x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = 0 := by
          have hscaled := congrArg (fun z : ℝ => 8 * z) hh
          rw [LatticeProb.Graph.laplacian] at hscaled
          simpa using hscaled
    have htest : ∀ x, x ∉ B → f x * eta x ^ 2 = 0 := by
      intro x hx
      by_cases hxC : x ∈ Cfin
      · by_cases hxbox : x ∈ LatticeProb.boxFinset 0 (4 * R)
        · have hinner : ¬ (R : ℝ) / 8 < (LatticeProb.supNorm x : ℝ) := by
            intro hinner
            exact hx (Finset.mem_filter.mpr ⟨hxbox, hxC, hinner⟩)
          have hη := aux_bg4_eta_zero (R := R) (by omega) x (le_of_not_gt hinner)
          simp [eta, hη]
        · have hsup : 4 * R < LatticeProb.supNorm x := by
            by_contra hnot
            apply hxbox
            rw [LatticeProb.mem_boxFinset_zero_iff]
            exact le_of_not_gt hnot
          have hsup' : 4 * (R : ℝ) ≤ (LatticeProb.supNorm x : ℝ) := by
            exact_mod_cast (Nat.le_of_lt hsup)
          have hη := aux_bg4_eta_zero_outer (R := R) (by omega) x hsup'
          simp [eta, hη]
      · have hzero := Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hxC
        simp [f, hzero]
    have hBS : B ⊆ S := by
      intro x hx
      have hxbox := (Finset.mem_filter.mp hx).1
      have hsup := (LatticeProb.mem_boxFinset_zero_iff.mp hxbox)
      rw [LatticeProb.mem_boxFinset_zero_iff]
      exact hsup.trans (by omega)
    have hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S := by
      intro x hx y hxy
      have hxbox := (Finset.mem_filter.mp hx).1
      have hsupx := (LatticeProb.mem_boxFinset_zero_iff.mp hxbox)
      have hsupy := (aux_bg4_supNorm_adj hxy).1
      have hsupx' : LatticeProb.supNorm x ≤ 4 * R := by exact hsupx
      have hsupy' : LatticeProb.supNorm y ≤ 4 * R + 1 := by omega
      exact (LatticeProb.mem_boxFinset_zero_iff.mpr hsupy')
    have henergy := aux_bg4_caccioppoli_support
      (G := G) (c := LatticeProb.Network.unitCond G) LatticeProb.Network.isCond_unitCond
      S B f eta hf htest hBS hnb
    have hsup_le_norm : ∀ z : Sandpile.Site 4,
        (LatticeProb.supNorm z : ℝ) ≤ BallGreen.latticeNorm z := by
      intro z
      simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using
        LatticeProb.supNorm_le_euclidNorm z
    have hnorm_le_sup : ∀ z : Sandpile.Site 4,
        BallGreen.latticeNorm z ≤ 2 * (LatticeProb.supNorm z : ℝ) := by
      intro z
      have h := LatticeProb.euclidNorm_le_sqrt_mul_supNorm z
      norm_num [BallGreen.latticeNorm, LatticeProb.euclidNorm] at h ⊢
      exact h
    have heta_one : ∀ z : Sandpile.Site 4,
        (R : ℝ) ≤ BallGreen.latticeNorm z →
          BallGreen.latticeNorm z ≤ 2 * (R : ℝ) → eta z = 1 := by
      intro z hz₁ hz₂
      have hlow : (R : ℝ) / 4 ≤ (LatticeProb.supNorm z : ℝ) := by
        have := hnorm_le_sup z
        linarith
      have hupp : (LatticeProb.supNorm z : ℝ) ≤ 3 * (R : ℝ) := by
        exact (hsup_le_norm z).trans hz₂ |>.trans (by linarith)
      exact aux_bg4_eta_one (R := R) (by omega) z hlow hupp
    let hAset : Set (Sandpile.Site 4) :=
      {u | (R : ℝ) ≤ BallGreen.latticeNorm u ∧
        BallGreen.latticeNorm u ≤ 2 * (R : ℝ)}
    change (∑' u : hAset,
      (Sandpile.killedGreen (BallGreen.box r) 0
          ((u : Sandpile.Site 4) + Sandpile.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
      C / (R : ℝ) ^ 2
    rw [tsum_subtype hAset (fun u : Sandpile.Site 4 =>
      (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2)]
    have hzero : ∀ u : Sandpile.Site 4, u ∉ S →
        hAset.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u = 0 := by
      intro u hu
      have huA : u ∉ hAset := by
        intro huA
        have hsup : (LatticeProb.supNorm u : ℝ) ≤ 2 * (R : ℝ) :=
          (hsup_le_norm u).trans huA.2
        have hsup' : LatticeProb.supNorm u ≤ 2 * R := by exact_mod_cast hsup
        apply hu
        rw [LatticeProb.mem_boxFinset_zero_iff]
        exact hsup'.trans (by omega)
      rw [Set.indicator_of_notMem huA]
    rw [tsum_eq_sum hzero]
    let v : Sandpile.Site 4 → Sandpile.Site 4 := fun u => u + Sandpile.unit i
    have hadj : ∀ u : Sandpile.Site 4, (G.Adj u (v u)) := by
      intro u
      dsimp [v, G]
      apply LatticeProb.Graph.Zd.adj_iff.mpr
      exact ⟨i, Or.inl rfl⟩
    have hrow : ∀ u : Sandpile.Site 4, u ∈ S →
        hAset.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u ≤
        ∑ y ∈ G.neighborFinset u,
          LatticeProb.Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
      intro u hu
      have hrow_nonneg : 0 ≤ ∑ y ∈ G.neighborFinset u,
          LatticeProb.Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg
          (mul_nonneg (LatticeProb.Network.isCond_unitCond.nonneg u y) (sq_nonneg _))
          (sq_nonneg _)
      by_cases huA : u ∈ hAset
      · have huone := heta_one u huA.1 huA.2
        have hsingle := Finset.single_le_sum
          (f := fun y => LatticeProb.Network.unitCond G u y *
            (f u - f y) ^ 2 * eta u ^ 2)
          (fun y hy => by
            exact mul_nonneg
              (mul_nonneg (LatticeProb.Network.isCond_unitCond.nonneg u y) (sq_nonneg _))
              (sq_nonneg _))
          (SimpleGraph.mem_neighborFinset _ _ _ |>.mpr (hadj u))
        rw [Set.indicator_of_mem huA]
        calc
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
              Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2 =
              (f u - f (v u)) ^ 2 := by simp [f, v]; ring
          _ ≤ ∑ y ∈ G.neighborFinset u,
              LatticeProb.Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
            have hc : LatticeProb.Network.unitCond G u (v u) = 1 := by
              simp [LatticeProb.Network.unitCond, hadj u]
            simpa [huone, hc] using hsingle
      · rw [Set.indicator_of_notMem huA]
        exact hrow_nonneg
    have hcompare : (∑ u ∈ S,
        hAset.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
        ∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          LatticeProb.Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
      exact Finset.sum_le_sum hrow
    have htarget : (∑ u ∈ S,
        hAset.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
        4 * ∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          LatticeProb.Network.unitCond G u y * (f u ^ 2 + f y ^ 2) *
            (eta u - eta y) ^ 2 := hcompare.trans henergy
    let A₀ : ℝ := (C₀ / ((R : ℝ) / 16) ^ 2) ^ 2
    have hK_sq : ∀ z : Sandpile.Site 4,
        (R : ℝ) / 16 ≤ BallGreen.latticeNorm z → f z ^ 2 ≤ A₀ := by
      intro z hz
      have hpoint := hclause1 r hr z
      have hden : (R : ℝ) / 16 ≤ 1 + BallGreen.latticeNorm z := by
        linarith [show (0 : ℝ) ≤ 1 by norm_num]
      have hdenpow : ((R : ℝ) / 16) ^ 2 ≤
          (1 + BallGreen.latticeNorm z) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hden 2
      have hbound : f z ≤ C₀ / ((R : ℝ) / 16) ^ 2 := by
        exact (hpoint.2.1.trans (hpoint.2.2.trans
          (div_le_div_of_nonneg_left hC₀.le (by positivity) hdenpow)))
      have hfnonneg : 0 ≤ f z := by
        simpa [f] using hpoint.1
      have hright : 0 ≤ C₀ / ((R : ℝ) / 16) ^ 2 := by
        exact div_nonneg hC₀.le (by positivity)
      dsimp [A₀]
      exact (sq_le_sq₀ hfnonneg hright).mpr hbound
    have hterm_energy : ∀ x : Sandpile.Site 4, x ∈ S →
        ∀ y, y ∈ G.neighborFinset x →
          LatticeProb.Network.unitCond G x y * (f x ^ 2 + f y ^ 2) *
              (eta x - eta y) ^ 2 ≤
            2 * A₀ * (8 / (R : ℝ)) ^ 2 := by
      intro x hx y hy
      have hxy : G.Adj x y :=
        (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hcond : LatticeProb.Network.unitCond G x y = 1 := by
        simp [LatticeProb.Network.unitCond, hxy]
      by_cases heq : eta x = eta y
      · simp [heq, hcond]
        dsimp [A₀]
        positivity
      · have hη := aux_bg4_eta_lipschitz (R := R) (by omega) hxy
        have hηsq : (eta x - eta y) ^ 2 ≤ (8 / (R : ℝ)) ^ 2 := by
          have habs : |eta x - eta y| ≤ 8 / (R : ℝ) := by
            simpa [eta] using hη
          have habs_sq := (sq_le_sq₀ (abs_nonneg (eta x - eta y))
            (by positivity : (0 : ℝ) ≤ 8 / (R : ℝ))).mpr habs
          simpa [sq_abs] using habs_sq
        have hnonzero : eta x ≠ 0 ∨ eta y ≠ 0 := by
          by_cases hx0 : eta x = 0
          · by_cases hy0 : eta y = 0
            · exact False.elim (heq (by rw [hx0, hy0]))
            · exact Or.inr hy0
          · exact Or.inl hx0
        have hnormx : (R : ℝ) / 16 ≤ BallGreen.latticeNorm x := by
          rcases hnonzero with hxη | hyη
          · have hsup : (R : ℝ) / 8 < (LatticeProb.supNorm x : ℝ) := by
              by_contra hnot
              have hz := aux_bg4_eta_zero (R := R) (by omega) x
                (le_of_not_gt hnot)
              exact hxη (by simpa [eta] using hz)
            exact (by
              have := hsup_le_norm x
              linarith)
          · have hsupy : (R : ℝ) / 8 < (LatticeProb.supNorm y : ℝ) := by
              by_contra hnot
              have hz := aux_bg4_eta_zero (R := R) (by omega) y
                (le_of_not_gt hnot)
              exact hyη (by simpa [eta] using hz)
            have hsupxy : (LatticeProb.supNorm y : ℝ) ≤
                (LatticeProb.supNorm x : ℝ) + 1 := by
              exact_mod_cast (aux_bg4_supNorm_adj hxy).1
            have hsupx : (R : ℝ) / 8 - 1 <
                (LatticeProb.supNorm x : ℝ) := by linarith
            have hnorm := hsup_le_norm x
            linarith
        have hnormy : (R : ℝ) / 16 ≤ BallGreen.latticeNorm y := by
          rcases hnonzero with hxη | hyη
          · have hsupx : (R : ℝ) / 8 < (LatticeProb.supNorm x : ℝ) := by
              by_contra hnot
              have hz := aux_bg4_eta_zero (R := R) (by omega) x
                (le_of_not_gt hnot)
              exact hxη (by simpa [eta] using hz)
            have hsupxy : (LatticeProb.supNorm x : ℝ) ≤
                (LatticeProb.supNorm y : ℝ) + 1 := by
              exact_mod_cast (aux_bg4_supNorm_adj hxy).2
            have hsupy : (R : ℝ) / 8 - 1 <
                (LatticeProb.supNorm y : ℝ) := by linarith
            have hnorm := hsup_le_norm y
            linarith
          · have hsup : (R : ℝ) / 8 < (LatticeProb.supNorm y : ℝ) := by
              by_contra hnot
              have hz := aux_bg4_eta_zero (R := R) (by omega) y
                (le_of_not_gt hnot)
              exact hyη (by simpa [eta] using hz)
            exact (by
              have := hsup_le_norm y
              linarith)
        have hfx := hK_sq x hnormx
        have hfy := hK_sq y hnormy
        have hsumf : f x ^ 2 + f y ^ 2 ≤ 2 * A₀ := by linarith
        rw [hcond]
        calc
          1 * (f x ^ 2 + f y ^ 2) * (eta x - eta y) ^ 2 ≤
              (2 * A₀) * (eta x - eta y) ^ 2 := by
                exact mul_le_mul_of_nonneg_right (by simpa using hsumf)
                  (sq_nonneg _)
          _ ≤ (2 * A₀) * (8 / (R : ℝ)) ^ 2 := by
                exact mul_le_mul_of_nonneg_left hηsq (by positivity)
    let M : ℝ := 2 * A₀ * (8 / (R : ℝ)) ^ 2
    have henergy_bound :
        (∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          LatticeProb.Network.unitCond G u y * (f u ^ 2 + f y ^ 2) *
            (eta u - eta y) ^ 2) ≤ (S.card : ℝ) * 8 * M := by
      calc
        _ ≤ ∑ u ∈ S, ∑ y ∈ G.neighborFinset u, M := by
          apply Finset.sum_le_sum
          intro u hu
          apply Finset.sum_le_sum
          intro y hy
          exact hterm_energy u hu y hy
        _ = (S.card : ℝ) * 8 * M := by
          calc
            (∑ u ∈ S, ∑ y ∈ G.neighborFinset u, M) =
                ∑ u ∈ S, ((G.neighborFinset u).card : ℝ) * M := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [Finset.sum_const, nsmul_eq_mul]
            _ = (S.card : ℝ) * 8 * M := by
              have hdeg : ∀ u : Sandpile.Site 4,
                  (G.neighborFinset u).card = 8 := by
                intro u
                dsimp [G]
                norm_num [LatticeProb.Graph.Zd.degree_eq]
              simp [hdeg, Finset.sum_const, nsmul_eq_mul]
              ring
    have hcardS : (S.card : ℝ) ≤ (11 * (R : ℝ)) ^ 4 := by
      dsimp [S]
      rw [LatticeProb.card_boxFinset_zero]
      push_cast
      have hbase : 2 * (4 * (R : ℝ) + 1) + 1 ≤ 11 * (R : ℝ) := by
        have hRone : (1 : ℝ) ≤ (R : ℝ) := by
          exact_mod_cast (show 1 ≤ R by omega)
        linarith
      exact pow_le_pow_left₀ (by positivity) hbase 4
    have hM : 0 ≤ M := by
      dsimp [M, A₀]
      positivity
    have hcount : 4 * ((S.card : ℝ) * 8 * M) ≤
        4 * ((11 * (R : ℝ)) ^ 4 * 8 * M) := by
      gcongr
    have hscale : 4 * ((11 * (R : ℝ)) ^ 4 * 8 * M) ≤
        C / (R : ℝ) ^ 2 := by
      have heq : 4 * ((11 * (R : ℝ)) ^ 4 * 8 * M) =
          C₀ ^ 2 * ((2 : ℝ) ^ 28 * 11 ^ 4) / (R : ℝ) ^ 2 := by
        dsimp [M, A₀]
        field_simp [ne_of_gt hRpos]
        ring
      rw [heq]
      apply (div_le_div_iff_of_pos_right (by positivity :
        (0 : ℝ) < (R : ℝ) ^ 2)).2
      have hcoef : C₀ ^ 2 * ((2 : ℝ) ^ 28 * 11 ^ 4) ≤
          C₀ ^ 2 * ((2 : ℝ) ^ 40 * 11 ^ 4) := by
        gcongr <;> norm_num
      have hCbig : C₀ ^ 2 * ((2 : ℝ) ^ 40 * 11 ^ 4) ≤ C := by
        dsimp [C]
        nlinarith [sq_nonneg C₀]
      exact hcoef.trans hCbig
    exact htarget.trans ((mul_le_mul_of_nonneg_left
      henergy_bound (by norm_num)).trans (hcount.trans hscale))
  · have hRle : R ≤ 15 := by omega
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    let A : Set (Sandpile.Site 4) :=
      {u | (R : ℝ) ≤ BallGreen.latticeNorm u ∧
        BallGreen.latticeNorm u ≤ 2 * (R : ℝ)}
    change (∑' u : A,
      (Sandpile.killedGreen (BallGreen.box r) 0
          ((u : Sandpile.Site 4) + Sandpile.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
      C / (R : ℝ) ^ 2
    rw [tsum_subtype A (fun u : Sandpile.Site 4 =>
      (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2)]
    let T : Finset (Sandpile.Site 4) := LatticeProb.boxFinset 0 (2 * R + 1)
    have hzero : ∀ u : Sandpile.Site 4, u ∉ T →
        A.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u = 0 := by
      intro u hu
      have huA : u ∉ A := by
        intro hAu
        have hsup : (LatticeProb.supNorm u : ℝ) ≤ 2 * (R : ℝ) := by
          have hnorm := LatticeProb.supNorm_le_euclidNorm u
          have hnorm' : (LatticeProb.supNorm u : ℝ) ≤ BallGreen.latticeNorm u := by
            simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using hnorm
          exact hnorm'.trans hAu.2
        have hsup' : LatticeProb.supNorm u ≤ 2 * R := by exact_mod_cast hsup
        apply hu
        rw [LatticeProb.mem_boxFinset_zero_iff]
        apply LatticeProb.supNorm_le_iff.mpr
        intro j
        rw [Int.abs_eq_natAbs]
        have hcoord := (LatticeProb.supNorm_le_iff.mp hsup') j
        have hcoord' : ((u j).natAbs : ℤ) ≤ (2 * R : ℤ) := by
          simpa only [Int.abs_eq_natAbs, Nat.cast_mul, Nat.cast_ofNat] using hcoord
        have hcoordNat : (u j).natAbs ≤ 2 * R := by exact_mod_cast hcoord'
        omega
      rw [Set.indicator_of_notMem huA]
    rw [tsum_eq_sum hzero]
    have hterm : ∀ u : Sandpile.Site 4, u ∈ T →
        A.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u ≤
        4 * C₀ ^ 2 := by
      intro u hu
      by_cases hAu : u ∈ A
      · rw [Set.indicator_of_mem hAu]
        have hu0 := (hclause1 r hr u).1
        have huv0 := (hclause1 r hr (u + Sandpile.unit i)).1
        have huC := (hclause1 r hr u).2.2
        have huvC := (hclause1 r hr (u + Sandpile.unit i)).2.2
        have huB : Sandpile.killedGreen (BallGreen.box r) 0 u ≤ C₀ := by
          have hn : 0 ≤ BallGreen.latticeNorm u := by
            dsimp [BallGreen.latticeNorm]
            positivity
          have hden : (1 : ℝ) ≤ (1 + BallGreen.latticeNorm u) ^ 2 := by
            nlinarith [sq_nonneg (BallGreen.latticeNorm u)]
          have hq : C₀ / (1 + BallGreen.latticeNorm u) ^ 2 ≤ C₀ := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1 + BallGreen.latticeNorm u) ^ 2)).2
            nlinarith [hC₀.le, hden]
          exact (hclause1 r hr u).2.1.trans (huC.trans hq)
        have huvB : Sandpile.killedGreen (BallGreen.box r) 0
            (u + Sandpile.unit i) ≤ C₀ := by
          have hn : 0 ≤ BallGreen.latticeNorm (u + Sandpile.unit i) := by
            dsimp [BallGreen.latticeNorm]
            positivity
          have hden : (1 : ℝ) ≤ (1 + BallGreen.latticeNorm (u + Sandpile.unit i)) ^ 2 := by
            nlinarith [sq_nonneg (BallGreen.latticeNorm (u + Sandpile.unit i))]
          have hq : C₀ / (1 + BallGreen.latticeNorm (u + Sandpile.unit i)) ^ 2 ≤ C₀ := by
            apply (div_le_iff₀ (by positivity :
              (0 : ℝ) < (1 + BallGreen.latticeNorm (u + Sandpile.unit i)) ^ 2)).2
            nlinarith [hC₀.le, hden]
          exact (hclause1 r hr (u + Sandpile.unit i)).2.1.trans (huvC.trans hq)
        nlinarith [sq_nonneg
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u)]
      · rw [Set.indicator_of_notMem hAu]
        positivity
    have hsum : (∑ u ∈ T,
        A.indicator (fun u : Sandpile.Site 4 =>
          (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
            Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
        4 * C₀ ^ 2 * (T.card : ℝ) := by
      calc
        _ ≤ ∑ u ∈ T, (4 * C₀ ^ 2) := Finset.sum_le_sum hterm
        _ = 4 * C₀ ^ 2 * (T.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [mul_comm]
    have hcard : (T.card : ℝ) ≤ 63 ^ 4 := by
      dsimp [T]
      rw [LatticeProb.card_boxFinset_zero]
      have hnat : 2 * (2 * R + 1) + 1 ≤ 63 := by omega
      have hcast : (2 * (2 * R + 1) + 1 : ℝ) ≤ 63 := by exact_mod_cast hnat
      push_cast
      exact pow_le_pow_left₀ (by positivity) hcast 4
    have hmain : 4 * C₀ ^ 2 * (T.card : ℝ) ≤ C / (R : ℝ) ^ 2 := by
      have hR2 : (R : ℝ) ^ 2 ≤ 256 := by
        have : (R : ℝ) ≤ 15 := by exact_mod_cast hRle
        nlinarith
      have hprod : (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2 ≤ C := by
        calc
          (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2 ≤
              4 * C₀ ^ 2 * (63 : ℝ) ^ 4 * 256 := by
                gcongr
          _ ≤ C := by
            dsimp [C]
            nlinarith [sq_nonneg C₀]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)).2
      calc
        4 * C₀ ^ 2 * (T.card : ℝ) * (R : ℝ) ^ 2 ≤
            (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2 := by
              gcongr
        _ ≤ C := hprod
    exact hsum.trans hmain

end Sandpile.External

namespace Sandpile.External

/-- **Minkowski's inequality for `BallGreen.latticeNorm`.**  The Euclidean norm of a sum of two
lattice vectors is at most the sum of the two Euclidean norms, by the usual Cauchy-Schwarz
argument on the cross term. -/
theorem aux_bg6_latticeNorm_add_le (a b : Sandpile.Site 4) :
    BallGreen.latticeNorm (a + b) ≤ BallGreen.latticeNorm a + BallGreen.latticeNorm b := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 4))
    (fun i => ((a i : ℤ) : ℝ)) (fun i => ((b i : ℤ) : ℝ))
  have hA : (0:ℝ) ≤ BallGreen.latticeNorm a := Real.sqrt_nonneg _
  have hB : (0:ℝ) ≤ BallGreen.latticeNorm b := Real.sqrt_nonneg _
  have hpt : ∀ i : Fin 4, (((a+b) i : ℤ) : ℝ) ^ 2 =
      ((a i:ℤ):ℝ)^2 + 2*(((a i:ℤ):ℝ)*((b i:ℤ):ℝ)) + ((b i:ℤ):ℝ)^2 := by
    intro i
    have hi : ((a+b) i : ℤ) = (a i : ℤ) + (b i : ℤ) := by simp [Pi.add_apply]
    rw [hi]
    push_cast
    ring
  have hexpand : (∑ i : Fin 4, (((a+b) i:ℤ):ℝ)^2) =
      (∑ i : Fin 4, ((a i:ℤ):ℝ)^2) + 2*(∑ i : Fin 4, ((a i:ℤ):ℝ)*((b i:ℤ):ℝ))
        + (∑ i : Fin 4, ((b i:ℤ):ℝ)^2) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : (∑ i : Fin 4, ((a i:ℤ):ℝ)*((b i:ℤ):ℝ)) ≤
      BallGreen.latticeNorm a * BallGreen.latticeNorm b := hcs
  have haa : BallGreen.latticeNorm a ^ 2 = ∑ i:Fin 4, ((a i:ℤ):ℝ)^2 := by
    unfold BallGreen.latticeNorm
    rw [Real.sq_sqrt (by positivity)]
  have hbb : BallGreen.latticeNorm b ^ 2 = ∑ i:Fin 4, ((b i:ℤ):ℝ)^2 := by
    unfold BallGreen.latticeNorm
    rw [Real.sq_sqrt (by positivity)]
  have hsq : (∑ i:Fin 4, (((a+b) i:ℤ):ℝ)^2) ≤ (BallGreen.latticeNorm a + BallGreen.latticeNorm b)^2 := by
    rw [hexpand]
    have hring : (BallGreen.latticeNorm a + BallGreen.latticeNorm b)^2 =
        BallGreen.latticeNorm a ^2 + 2*(BallGreen.latticeNorm a * BallGreen.latticeNorm b)
          + BallGreen.latticeNorm b^2 := by ring
    rw [hring, haa, hbb]
    linarith [hcross]
  calc BallGreen.latticeNorm (a+b) = Real.sqrt (∑ i:Fin 4, (((a+b) i:ℤ):ℝ)^2) := rfl
    _ ≤ Real.sqrt ((BallGreen.latticeNorm a + BallGreen.latticeNorm b)^2) := Real.sqrt_le_sqrt hsq
    _ = BallGreen.latticeNorm a + BallGreen.latticeNorm b := Real.sqrt_sq (by linarith [hA, hB])

/-- A site of the killed-Green box has Euclidean norm at most `2r`, since the sup-norm is at
most the Euclidean norm and the Euclidean norm is at most `√4 = 2` times the sup-norm. -/
theorem aux_bg6_latticeNorm_le_of_mem_boxFinset {r : ℕ} {u : Sandpile.Site 4}
    (hu : u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r) :
    BallGreen.latticeNorm u ≤ 2 * (r : ℝ) := by
  have hsup : LatticeProb.supNorm u ≤ r := LatticeProb.mem_boxFinset_zero_iff.mp hu
  have h1 : BallGreen.latticeNorm u ≤ Real.sqrt 4 * (LatticeProb.supNorm u : ℝ) := by
    have h := LatticeProb.euclidNorm_le_sqrt_mul_supNorm u
    simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm] using h
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt4] at h1
  have hcast : (LatticeProb.supNorm u : ℝ) ≤ (r:ℝ) := by exact_mod_cast hsup
  nlinarith [h1, hcast]

/-- **The precise residual left for `aux_ballgreen_clause6`.**  The general-shift `L²` gradient
bound for the ball-killed Green function itself (no cutoff), restricted to the region where
`(2+M)L ≤ |u|`.  This is the genuine estimate `aux_ballgreen_clause6` needs beyond what
`aux_ballgreen_clause1` and `aux_ballgreen_clause5` already give: those two only bound `cutField`
and its cube, not a shifted difference, and a shifted-difference sum is not uniformly bounded in
`r` without some cancellation (the uncancelled bound degrades like `log r`, matching
`aux_ballgreen_clause2`).  `aux_ballgreen_clause4` (the annular gradient bound for a unit shift)
is the natural source of that cancellation, via a telescoping sum over a lattice path from `0` to
`w` and a dyadic sum over annuli; that reduction is not carried out here. -/
def aux_bg6_far_residual : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, 2 ≤ L → ∀ M : ℝ, 1 ≤ M →
      ∀ w : Sandpile.Site 4, BallGreen.latticeNorm w ≤ M * (L : ℝ) →
        (∑' u : Sandpile.Site 4,
            Set.indicator {u : Sandpile.Site 4 | (2 + M) * (L : ℝ) ≤ BallGreen.latticeNorm u}
              (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
                Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u) ≤
          C * (1 + M) ^ 4

/-- **`aux_ballgreen_clause6` reduces to the far residual.**  Split `ℤ^4` at the threshold
`(2+M)L`: below it, the crude sup bound of `aux_ballgreen_clause5` costs a factor `(1+M)^4`
against the volume of a ball of that radius (this part needs no cancellation); at or above it,
the cutoff `φ` has saturated to `1` on both `u` and `u-w` (using `1 ≤ M`, so `(2+M)L ≥ 2L`, and
Minkowski's inequality for `BallGreen.latticeNorm`, so `u - w` is also past `2L`), so `cutField`
agrees exactly with `killedGreen (box r) 0`, which is exactly `aux_bg6_far_residual`. -/
theorem aux_bg6_reduce (hfar : aux_bg6_far_residual) : aux_ballgreen_clause6 := by
  classical
  obtain ⟨C₅, hC₅, hclause5⟩ := aux_ballgreen_clause5
  obtain ⟨Cf, hCf, hfar⟩ := hfar
  refine ⟨2500 * C₅ ^ 2 + Cf, by positivity, ?_⟩
  intro r hr L hL φ hφ M hM w hw
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := hLpos.le
  have hMnn : (0 : ℝ) ≤ M := by linarith
  have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) := mul_nonneg hMnn hLnn
  have hLge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 1 ≤ L by omega)
  obtain ⟨hsup, -⟩ := hclause5 r hr L hL φ hφ
  -- the near/far threshold facts: at or above `(2+M)L`, `cutField` agrees with `killedGreen`.
  have hthresh_u : ∀ u : Sandpile.Site 4, (2 + M) * (L : ℝ) ≤ BallGreen.latticeNorm u →
      BallGreen.cutField r L φ u = Sandpile.killedGreen (BallGreen.box r) 0 u := by
    intro u hu
    have h2L : 2 * (L : ℝ) ≤ BallGreen.latticeNorm u := by nlinarith [hM, hLnn]
    have hs : (2 : ℝ) ≤ BallGreen.latticeNorm u / (L : ℝ) := (le_div_iff₀ hLpos).2 (by linarith)
    unfold BallGreen.cutField
    rw [hφ.2.2.2 _ hs, mul_one]
  have hthresh_uw : ∀ u : Sandpile.Site 4, (2 + M) * (L : ℝ) ≤ BallGreen.latticeNorm u →
      BallGreen.cutField r L φ (u - w) = Sandpile.killedGreen (BallGreen.box r) 0 (u - w) := by
    intro u hu
    have htri : BallGreen.latticeNorm u ≤ BallGreen.latticeNorm (u - w) + BallGreen.latticeNorm w := by
      have h := aux_bg6_latticeNorm_add_le (u - w) w
      rwa [sub_add_cancel] at h
    have h2L : 2 * (L : ℝ) ≤ BallGreen.latticeNorm (u - w) := by nlinarith [hw, hu, htri]
    have hs : (2 : ℝ) ≤ BallGreen.latticeNorm (u - w) / (L : ℝ) := (le_div_iff₀ hLpos).2 (by linarith)
    unfold BallGreen.cutField
    rw [hφ.2.2.2 _ hs, mul_one]
  -- a crude pointwise bound, valid everywhere, from the sup bound alone.
  have hcrude : ∀ u : Sandpile.Site 4,
      (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2 ≤
        (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 := by
    intro u
    have h1 := hsup u
    have h2 := hsup (u - w)
    have hb : |BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)| ≤
        2 * (C₅ / (L : ℝ) ^ 2) := by
      have htri : |BallGreen.cutField r L φ u + (-(BallGreen.cutField r L φ (u - w)))| ≤
          |BallGreen.cutField r L φ u| + |-(BallGreen.cutField r L φ (u - w))| :=
        abs_add_le _ _
      rw [abs_neg, ← sub_eq_add_neg] at htri
      calc |BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)|
          ≤ |BallGreen.cutField r L φ u| + |BallGreen.cutField r L φ (u - w)| := htri
        _ ≤ C₅ / (L : ℝ) ^ 2 + C₅ / (L : ℝ) ^ 2 := add_le_add h1 h2
        _ = 2 * (C₅ / (L : ℝ) ^ 2) := by ring
    calc (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2
        = |BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
  -- the threshold radii: `ρ` splits near from far, `bigR2`/`bigS` dominate every support.
  set ρ : ℝ := (2 + M) * (L : ℝ) with hρdef
  set nearBound : ℝ := (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 with hnearBoundDef
  set bigR2 : ℝ := 2 * (r : ℝ) + M * (L : ℝ) with hbigR2def
  set bigS : ℝ := bigR2 + ρ with hbigSdef
  have hρnn : (0 : ℝ) ≤ ρ := by rw [hρdef]; positivity
  have hbigR2nn : (0 : ℝ) ≤ bigR2 := by rw [hbigR2def]; positivity
  have hnearBoundnn : (0 : ℝ) ≤ nearBound := by rw [hnearBoundDef]; positivity
  -- killed-Green support forces `|u| ≤ bigR2`, hence `|u| ≤ bigS`.
  have hsupp : ∀ u : Sandpile.Site 4, bigS < BallGreen.latticeNorm u →
      Sandpile.killedGreen (BallGreen.box r) 0 u = 0 ∧
        Sandpile.killedGreen (BallGreen.box r) 0 (u - w) = 0 := by
    intro u hu
    rw [hbigSdef, hbigR2def] at hu
    constructor
    · by_contra hz
      have hmem : u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
        by_contra hnm
        exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
      have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
      linarith
    · by_contra hz
      have hmem : (u - w) ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
        by_contra hnm
        exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
      have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
      have htri : BallGreen.latticeNorm u ≤
          BallGreen.latticeNorm (u - w) + BallGreen.latticeNorm w := by
        have h := aux_bg6_latticeNorm_add_le (u - w) w
        rwa [sub_add_cancel] at h
      linarith
  -- `D`, `N` and `F` all vanish outside the ball of radius `bigS`.
  have hDzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.ballFinset 4 bigS →
      (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2 = 0 := by
    intro u hu
    have hgt : bigS < BallGreen.latticeNorm u := by
      by_contra hc
      exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
    obtain ⟨hz1, hz2⟩ := hsupp u hgt
    have hc1 : BallGreen.cutField r L φ u = 0 := by unfold BallGreen.cutField; rw [hz1, zero_mul]
    have hc2 : BallGreen.cutField r L φ (u - w) = 0 := by
      unfold BallGreen.cutField; rw [hz2, zero_mul]
    rw [hc1, hc2]; ring
  have hNzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.ballFinset 4 bigS →
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u
        = 0 := by
    intro u hu
    have hgt : bigS < BallGreen.latticeNorm u := by
      by_contra hc
      exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
    have hρlebigS : ρ ≤ bigS := by rw [hbigSdef]; linarith
    apply Set.indicator_of_notMem
    simp only [Set.mem_setOf_eq, not_lt]
    linarith
  have hFzero : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.ballFinset 4 bigS →
      Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
        (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
          Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u = 0 := by
    intro u hu
    have hgt : bigS < BallGreen.latticeNorm u := by
      by_contra hc
      exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
    obtain ⟨hz1, hz2⟩ := hsupp u hgt
    by_cases hmemF : ρ ≤ BallGreen.latticeNorm u
    · have heq : Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
          (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u =
          (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2 := by
        apply Set.indicator_of_mem; exact hmemF
      rw [heq, hz1, hz2]; ring
    · apply Set.indicator_of_notMem; exact hmemF
  -- the pointwise domination `D ≤ N + F`, cased on the `ρ` threshold.
  have hsumle : (∑ u ∈ LatticeProb.ballFinset 4 bigS,
        (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2) ≤
      (∑ u ∈ LatticeProb.ballFinset 4 bigS,
          Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u)
        + (∑ u ∈ LatticeProb.ballFinset 4 bigS,
            Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
              (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
                Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    rcases lt_or_ge (BallGreen.latticeNorm u) ρ with hcase | hcase
    · have hNz : Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ}
          (fun _ => nearBound) u = nearBound := by
        apply Set.indicator_of_mem; exact hcase
      have hFz : Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
          (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u = 0 := by
        apply Set.indicator_of_notMem; exact not_le.mpr hcase
      rw [hNz, hFz, add_zero]
      exact hcrude u
    · have hNz : Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ}
          (fun _ => nearBound) u = 0 := by
        apply Set.indicator_of_notMem; exact not_lt.mpr hcase
      have hFz : Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
          (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u =
          (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2 := by
        apply Set.indicator_of_mem; exact hcase
      rw [hNz, hFz, zero_add, hthresh_u u hcase, hthresh_uw u hcase]
  have hDsum : (∑' u : Sandpile.Site 4,
      (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2) =
      ∑ u ∈ LatticeProb.ballFinset 4 bigS,
        (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2 :=
    tsum_eq_sum hDzero
  have hNsum : (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u) =
      ∑ u ∈ LatticeProb.ballFinset 4 bigS,
        Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u :=
    tsum_eq_sum hNzero
  have hFsum : (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
        (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
          Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u) =
      ∑ u ∈ LatticeProb.ballFinset 4 bigS,
        Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
          (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
            Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u :=
    tsum_eq_sum hFzero
  have hmainle : (∑' u : Sandpile.Site 4,
      (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2) ≤
      (∑' u : Sandpile.Site 4,
          Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u)
        + (∑' u : Sandpile.Site 4,
            Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
              (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
                Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u) := by
    rw [hDsum, hNsum, hFsum]
    exact hsumle
  -- bound the near tsum via the volume of a ball of radius `ρ`.
  have hNboundraw : ∀ u : Sandpile.Site 4, u ∉ LatticeProb.ballFinset 4 ρ →
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u
        = 0 := by
    intro u hu
    have hgt : ρ < BallGreen.latticeNorm u := by
      by_contra hc
      exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
    apply Set.indicator_of_notMem; exact not_lt.mpr hgt.le
  have hNtsum : (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u) =
      ∑ u ∈ LatticeProb.ballFinset 4 ρ,
        Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u :=
    tsum_eq_sum hNboundraw
  have hNfinbound : (∑ u ∈ LatticeProb.ballFinset 4 ρ,
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u) ≤
      (LatticeProb.ballFinset 4 ρ).card • nearBound := by
    rw [← Finset.sum_const]
    apply Finset.sum_le_sum
    intro u _
    by_cases hcm : BallGreen.latticeNorm u < ρ
    · have heq : Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ}
          (fun _ => nearBound) u = nearBound := by
        apply Set.indicator_of_mem; exact hcm
      rw [heq]
    · have heq : Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ}
          (fun _ => nearBound) u = 0 := by
        apply Set.indicator_of_notMem; exact hcm
      rw [heq]
      exact hnearBoundnn
  have hcard : ((LatticeProb.ballFinset 4 ρ).card : ℝ) ≤ (2 * ρ + 1) ^ 4 :=
    LatticeProb.card_ballFinset_le 4 hρnn
  have hAle : 2 * ((2 + M) * (L : ℝ)) + 1 ≤ (5 + 2 * M) * (L : ℝ) := by nlinarith [hLge1]
  have hA4le : (2 * ((2 + M) * (L : ℝ)) + 1) ^ 4 ≤ ((5 + 2 * M) * (L : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hAle 4
  have hnum1 : (2 * ((2 + M) * (L : ℝ)) + 1) ^ 4 * (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 ≤
      ((5 + 2 * M) * (L : ℝ)) ^ 4 * (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 :=
    mul_le_mul_of_nonneg_right hA4le (by positivity)
  have heq1 : ((5 + 2 * M) * (L : ℝ)) ^ 4 * (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 =
      4 * C₅ ^ 2 * (5 + 2 * M) ^ 4 := by
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    field_simp
    ring
  have h52M : (5 + 2 * M : ℝ) ≤ 5 * (1 + M) := by nlinarith [hMnn]
  have h52M4 : (5 + 2 * M : ℝ) ^ 4 ≤ (5 * (1 + M)) ^ 4 :=
    pow_le_pow_left₀ (by linarith) h52M 4
  have hnearFinal : (LatticeProb.ballFinset 4 ρ).card • nearBound ≤ 2500 * C₅ ^ 2 * (1 + M) ^ 4 := by
    rw [nsmul_eq_mul]
    have hstep1 : ((LatticeProb.ballFinset 4 ρ).card : ℝ) * nearBound ≤
        (2 * ρ + 1) ^ 4 * nearBound := mul_le_mul_of_nonneg_right hcard hnearBoundnn
    refine hstep1.trans ?_
    rw [hρdef, hnearBoundDef]
    calc (2 * ((2 + M) * (L : ℝ)) + 1) ^ 4 * (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2
        ≤ ((5 + 2 * M) * (L : ℝ)) ^ 4 * (2 * (C₅ / (L : ℝ) ^ 2)) ^ 2 := hnum1
      _ = 4 * C₅ ^ 2 * (5 + 2 * M) ^ 4 := heq1
      _ ≤ 4 * C₅ ^ 2 * (5 * (1 + M)) ^ 4 := by
          apply mul_le_mul_of_nonneg_left h52M4 (by positivity)
      _ = 2500 * C₅ ^ 2 * (1 + M) ^ 4 := by ring
  have hNtsum_le : (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u) ≤
      2500 * C₅ ^ 2 * (1 + M) ^ 4 := by
    rw [hNtsum]
    exact hNfinbound.trans hnearFinal
  -- the far tsum is exactly the far residual, at this `r, L, M, w`.
  have hFar_spec := hfar r hr L hL M hM w hw
  rw [← hρdef] at hFar_spec
  -- assemble.
  calc (∑' u : Sandpile.Site 4,
      (BallGreen.cutField r L φ u - BallGreen.cutField r L φ (u - w)) ^ 2)
      ≤ (∑' u : Sandpile.Site 4,
            Set.indicator {u : Sandpile.Site 4 | BallGreen.latticeNorm u < ρ} (fun _ => nearBound) u)
          + (∑' u : Sandpile.Site 4,
              Set.indicator {u : Sandpile.Site 4 | ρ ≤ BallGreen.latticeNorm u}
                (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 u -
                  Sandpile.killedGreen (BallGreen.box r) 0 (u - w)) ^ 2) u) := hmainle
    _ ≤ 2500 * C₅ ^ 2 * (1 + M) ^ 4 + Cf * (1 + M) ^ 4 := add_le_add hNtsum_le hFar_spec
    _ = (2500 * C₅ ^ 2 + Cf) * (1 + M) ^ 4 := by ring

end Sandpile.External

namespace Sandpile.External

/-
theorem aux_ballgreen_clause7_holds : aux_ballgreen_clause7 := by
  obtain ⟨G, g, hG, hg, hheat⟩ := Sandpile.External.gaussianUpper 4 (by norm_num)
  obtain ⟨M, hM, hblock⟩ := aux_bg7_survival_block G g hG hg hheat
  let C₀ : ℝ := 32 * G * (M : ℝ)
  let C : ℝ := 81 * C₀ ^ 2 + C₀ + 1
  let c : ℝ := Real.log 2 / (100 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro r hr A hA
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  let B : ℕ := M * r ^ 2
  have hr1 : 1 ≤ r := by omega
  have hr2 : 1 ≤ r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hr1 hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN : r ^ 2 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hrpow : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by
      norm_num
    rw [hrpow]
    nlinarith [hA, sq_nonneg (r : ℝ)]
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hB1 : 1 ≤ B := by omega
  have hblock0 : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) B x ≤ (1 : ℝ) / 2 := by
    intro x
    simpa [B] using hblock r hr x
  have hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := aux_bg7_survival_summable r
  obtain ⟨hf, hhalf⟩ := aux_bg7_half_survival_tsum
    (LatticeProb.boxFinset 0 r) N 0 hs
  have hshift := aux_bg7_survival_shift_tsum
    (LatticeProb.boxFinset 0 r) B hB hblock0 (N / 2) 0
  have hq : ∀ u : Sandpile.Site 4,
      BallGreen.timeTail r A u ≤
        (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
    intro u
    have hKsum : Summable (fun j : ℕ =>
        Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) := by
      exact (Sandpile.summable_killedKernel_transient (by norm_num)
        (BallGreen.box r) 0 u).comp_injective (add_right_injective N)
    have hright : Summable (fun j : ℕ =>
        (4 * G / (r : ℝ) ^ 4) *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) :=
      hf.mul_left (4 * G / (r : ℝ) ^ 4)
    have htail : BallGreen.timeTail r A u ≤
        (4 * G / (r : ℝ) ^ 4) *
          (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := by
      rw [aux_bg7_timeTail_tsum]
      change (∑' j : ℕ, Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) ≤ _
      rw [← tsum_mul_left]
      apply hKsum.tsum_le_tsum
      · intro j
        apply aux_bg7_kernel_step r (N + j) u hr
          (le_trans hN (Nat.le_add_right N j)) G g hG hg hheat
      · exact hright
    calc
      BallGreen.timeTail r A u ≤
          (4 * G / (r : ℝ) ^ 4) *
            (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := htail
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) (N / 2 + t) 0)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * ((B : ℝ) * 2 * ((1 : ℝ) / 2) ^ ((N / 2) / B))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshift (by norm_num)) (by positivity)
      _ = _ := by ring
  have hQ : (A / (100 * (M : ℝ)) - 1) ≤
      (((N / 2) / B : ℕ) : ℝ) := by
    by_cases hsmall : A ≤ 100 * (M : ℝ)
    · have hh : A / (100 * (M : ℝ)) - 1 ≤ 0 := by
        have hden : (0 : ℝ) < 100 * (M : ℝ) := by positivity
        have hdiv : A / (100 * (M : ℝ)) ≤ 1 := by
          apply (div_le_iff₀ hden).2
          simpa using hsmall
        linarith
      have hqnonneg : 0 ≤ (((N / 2) / B : ℕ) : ℝ) := by positivity
      linarith
    · have hNfloor : A * (r : ℝ) ^ 2 < (N : ℝ) + 1 := by
        dsimp [N]
        exact Nat.lt_floor_add_one _
      have hLfloor : (N : ℝ) + 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) + 2 := by
        have hh : N + 1 ≤ 2 * (N / 2 + 1) := by omega
        exact_mod_cast hh
      have hQfloor : ((N / 2 : ℕ) : ℝ) <
          (B : ℝ) * ((((N / 2) / B : ℕ) : ℝ) + 1) := by
        have hBnat : 0 < B := by omega
        have hmod := Nat.mod_lt (N / 2) hBnat
        have hdiv := Nat.div_add_mod (N / 2) B
        have hlt : N / 2 < B * (N / 2 / B) + B := by omega
        have hh : N / 2 < B * (N / 2 / B + 1) := by
          simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
        exact_mod_cast hh
      have hBr : (B : ℝ) = (M : ℝ) * (r : ℝ) ^ 2 := by
        simp [B, Nat.cast_mul, Nat.cast_pow]
      have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      have h1 : A * (r : ℝ) ^ 2 / 2 - 1 < ((N / 2 : ℕ) : ℝ) := by
        nlinarith [hNfloor, hLfloor]
      have h2 := (div_lt_div_iff₀ hBpos hBpos).2
        (mul_lt_mul_of_pos_right h1 hBpos)
      have h3 : ((N / 2 : ℕ) : ℝ) / (B : ℝ) - 1 <
          (((N / 2) / B : ℕ) : ℝ) := by
        have h3a : ((N / 2 : ℕ) : ℝ) / (B : ℝ) <
            (((N / 2) / B : ℕ) : ℝ) + 1 := by
          apply (div_lt_iff₀ hBpos).2
          nlinarith [hQfloor]
        linarith
      have hBge : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
      have h2' : A / (2 * (M : ℝ)) - 1 <
          ((N / 2 : ℕ) : ℝ) / (B : ℝ) := by
        have hInv : 1 / (B : ℝ) ≤ 1 := by
          exact (div_le_iff₀ hBpos).2 (by nlinarith [hBge])
        have hEq : (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) =
            A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
          rw [hBr]
          field_simp [ne_of_gt hMpos, ne_of_gt hrR]
        calc
          A / (2 * (M : ℝ)) - 1 ≤ A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
            linarith
          _ = (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) := hEq.symm
          _ < _ := h2
      have hQlow : A / (2 * (M : ℝ)) - 2 <
          (((N / 2) / B : ℕ) : ℝ) := by
        linarith [h2', h3]
      have hAgt : 100 * (M : ℝ) < A := lt_of_not_ge hsmall
      have hscale : A / (100 * (M : ℝ)) - 1 <
          A / (2 * (M : ℝ)) - 2 := by
        field_simp
        nlinarith [hAgt, hMpos]
      exact (hscale.trans hQlow).le
  have hqexp : ((1 : ℝ) / 2) ^ ((N / 2) / B) ≤
      2 * Real.exp (-c * A) := by
    have hbase : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
    have hmono := Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num) hQ
    have hpow : ((1 : ℝ) / 2) ^ ((N / 2) / B) =
        ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hpow]
    have heq : ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) =
        Real.exp (-c * A) := by
      rw [Real.rpow_def_of_pos hbase]
      dsimp [c]
      rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
      congr 1
      field_simp
    rw [← heq]
    calc
      ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) ≤
          ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ)) - 1) := hmono
      _ = 2 * ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) := by
        have he : A / (100 * (M : ℝ)) - 1 =
            A / (100 * (M : ℝ)) + (-1 : ℝ) := by ring
        rw [he, Real.rpow_add hbase]
        ring
  have hpoint : ∀ u : Sandpile.Site 4,
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
    intro u
    have hnonneg := (aux_bg7_timeTail_factor r A u).1
    have hu := (hq u).trans (by
      calc
        _ ≤ (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
            (2 * Real.exp (-c * A)) :=
          mul_le_mul_of_nonneg_left hqexp (by positivity)
        _ = C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
          dsimp [C₀, B]
          norm_num [Nat.cast_mul, Nat.cast_pow]
          field_simp
          ring)
    calc
      |BallGreen.timeTail r A u| = BallGreen.timeTail r A u := abs_of_nonneg hnonneg
      _ ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hu
  have hbox : BallGreen.box r =
      (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv)
      intro i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi i
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u = 0 := by
    intro u hu
    unfold BallGreen.timeTail
    rw [Sandpile.killedGreen_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      Sandpile.killedGreenTime_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      sub_zero]
  refine ⟨?_, ?_⟩
  · intro u
    have hC₀le : C₀ ≤ C := by
      dsimp [C]
      nlinarith [sq_nonneg C₀]
    calc
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hpoint u
      _ ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        gcongr
  · have hsqzero : ∀ u : Sandpile.Site 4,
        u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
          BallGreen.timeTail r A u ^ 2 = 0 := by
      intro u hu
      rw [hzero u hu, zero_pow (by decide : 2 ≠ 0)]
    rw [tsum_eq_sum hsqzero]
    have hE : Real.exp (-c * A) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hAnonneg : (0 : ℝ) ≤ A := by linarith
      linarith [mul_nonneg hc.le hAnonneg]
    have hsum :
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
      calc
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            BallGreen.timeTail r A u ^ 2) ≤
            ∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          have hp := hpoint u
          have hb : 0 ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by positivity
          have hsq : |BallGreen.timeTail r A u| ^ 2 =
              BallGreen.timeTail r A u ^ 2 := sq_abs _
          nlinarith [sq_nonneg (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) -
            |BallGreen.timeTail r A u|), hsq, abs_nonneg (BallGreen.timeTail r A u)]
        _ = ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, LatticeProb.card_boxFinset_zero]
          norm_num
    calc
      (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := hsum
      _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
        have hcard : ((2 * r + 1 : ℕ) : ℝ) ≤ 3 * (r : ℝ) := by
          push_cast
          nlinarith [show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr1]
        have hcard4 : ((2 * r + 1 : ℕ) : ℝ) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := by gcongr
        calc
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 ≤
              (3 * (r : ℝ)) ^ 4 *
                (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 :=
            mul_le_mul_of_nonneg_right hcard4 (sq_nonneg _)
          _ = 81 * C₀ ^ 2 * Real.exp (-c * A) ^ 2 := by
            have hr4 : (r : ℝ) ^ 4 ≠ 0 := by positivity
            field_simp
            ring
          _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
            have hcoef : 0 ≤ 81 * C₀ ^ 2 := by positivity
            have hE2 : Real.exp (-c * A) ^ 2 ≤ Real.exp (-c * A) := by
              have hE0 : 0 ≤ Real.exp (-c * A) := (Real.exp_pos _).le
              calc
                Real.exp (-c * A) ^ 2 = Real.exp (-c * A) * Real.exp (-c * A) := by ring
                _ ≤ Real.exp (-c * A) * 1 :=
                  mul_le_mul_of_nonneg_left hE hE0
                _ = Real.exp (-c * A) := by ring
            exact mul_le_mul_of_nonneg_left hE2 hcoef
      _ ≤ C * Real.exp (-c * A) := by
        have hcoefC : 81 * C₀ ^ 2 ≤ C := by
          dsimp [C]
          nlinarith [hC₀]
        exact mul_le_mul_of_nonneg_right hcoefC (Real.exp_pos _).le

-/

end Sandpile.External

namespace Sandpile.External

/-
theorem aux_ballgreen_clause7_holds : aux_ballgreen_clause7 := by
  obtain ⟨G, g, hG, hg, hheat⟩ := Sandpile.External.gaussianUpper 4 (by norm_num)
  obtain ⟨M, hM, hblock⟩ := aux_bg7_survival_block G g hG hg hheat
  let C₀ : ℝ := 32 * G * (M : ℝ)
  let C : ℝ := 81 * C₀ ^ 2 + C₀ + 1
  let c : ℝ := Real.log 2 / (100 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro r hr A hA
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  let B : ℕ := M * r ^ 2
  have hr1 : 1 ≤ r := by omega
  have hr2 : 1 ≤ r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hr1 hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN : r ^ 2 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hrpow : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by
      norm_num
    rw [hrpow]
    nlinarith [hA, sq_nonneg (r : ℝ)]
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hB1 : 1 ≤ B := by omega
  have hblock0 : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) B x ≤ (1 : ℝ) / 2 := by
    intro x
    simpa [B] using hblock r hr x
  have hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := aux_bg7_survival_summable r
  obtain ⟨hf, hhalf⟩ := aux_bg7_half_survival_tsum
    (LatticeProb.boxFinset 0 r) N 0 hs
  have hshift := aux_bg7_survival_shift_tsum
    (LatticeProb.boxFinset 0 r) B hB hblock0 (N / 2) 0
  have hq : ∀ u : Sandpile.Site 4,
      BallGreen.timeTail r A u ≤
        (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
    intro u
    have hKsum : Summable (fun j : ℕ =>
        Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) := by
      exact (Sandpile.summable_killedKernel_transient (by norm_num)
        (BallGreen.box r) 0 u).comp_injective (add_right_injective N)
    have hright : Summable (fun j : ℕ =>
        (4 * G / (r : ℝ) ^ 4) *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) :=
      hf.mul_left (4 * G / (r : ℝ) ^ 4)
    have htail : BallGreen.timeTail r A u ≤
        (4 * G / (r : ℝ) ^ 4) *
          (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := by
      rw [aux_bg7_timeTail_tsum]
      change (∑' j : ℕ, Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) ≤ _
      rw [← tsum_mul_left]
      apply hKsum.tsum_le_tsum
      · intro j
        apply aux_bg7_kernel_step r (N + j) u hr
          (le_trans hN (Nat.le_add_right N j)) G g hG hg hheat
      · exact hright
    calc
      BallGreen.timeTail r A u ≤
          (4 * G / (r : ℝ) ^ 4) *
            (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := htail
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) (N / 2 + t) 0)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * ((B : ℝ) * 2 * ((1 : ℝ) / 2) ^ ((N / 2) / B))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshift (by norm_num)) (by positivity)
      _ = _ := by ring
  have hQ : (A / (100 * (M : ℝ)) - 1) ≤
      (((N / 2) / B : ℕ) : ℝ) := by
    by_cases hsmall : A ≤ 100 * (M : ℝ)
    · have hh : A / (100 * (M : ℝ)) - 1 ≤ 0 := by
        have hden : (0 : ℝ) < 100 * (M : ℝ) := by positivity
        have hdiv : A / (100 * (M : ℝ)) ≤ 1 := by
          apply (div_le_iff₀ hden).2
          simpa using hsmall
        linarith
      have hqnonneg : 0 ≤ (((N / 2) / B : ℕ) : ℝ) := by positivity
      linarith
    · have hNfloor : A * (r : ℝ) ^ 2 < (N : ℝ) + 1 := by
        dsimp [N]
        exact Nat.lt_floor_add_one _
      have hLfloor : (N : ℝ) + 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) + 2 := by
        have hh : N + 1 ≤ 2 * (N / 2 + 1) := by omega
        exact_mod_cast hh
      have hQfloor : ((N / 2 : ℕ) : ℝ) <
          (B : ℝ) * ((((N / 2) / B : ℕ) : ℝ) + 1) := by
        have hBnat : 0 < B := by omega
        have hmod := Nat.mod_lt (N / 2) hBnat
        have hdiv := Nat.div_add_mod (N / 2) B
        have hlt : N / 2 < B * (N / 2 / B) + B := by omega
        have hh : N / 2 < B * (N / 2 / B + 1) := by
          simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
        exact_mod_cast hh
      have hBr : (B : ℝ) = (M : ℝ) * (r : ℝ) ^ 2 := by
        simp [B, Nat.cast_mul, Nat.cast_pow]
      have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      have h1 : A * (r : ℝ) ^ 2 / 2 - 1 < ((N / 2 : ℕ) : ℝ) := by
        nlinarith [hNfloor, hLfloor]
      have h2 := (div_lt_div_iff₀ hBpos hBpos).2
        (mul_lt_mul_of_pos_right h1 hBpos)
      have h3 : ((N / 2 : ℕ) : ℝ) / (B : ℝ) - 1 <
          (((N / 2) / B : ℕ) : ℝ) := by
        have h3a : ((N / 2 : ℕ) : ℝ) / (B : ℝ) <
            (((N / 2) / B : ℕ) : ℝ) + 1 := by
          apply (div_lt_iff₀ hBpos).2
          nlinarith [hQfloor]
        linarith
      have hBge : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
      have h2' : A / (2 * (M : ℝ)) - 1 <
          ((N / 2 : ℕ) : ℝ) / (B : ℝ) := by
        have hInv : 1 / (B : ℝ) ≤ 1 := by
          exact (div_le_iff₀ hBpos).2 (by nlinarith [hBge])
        have hEq : (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) =
            A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
          rw [hBr]
          field_simp [ne_of_gt hMpos, ne_of_gt hrR]
        calc
          A / (2 * (M : ℝ)) - 1 ≤ A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
            linarith
          _ = (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) := hEq.symm
          _ < _ := h2
      have hQlow : A / (2 * (M : ℝ)) - 2 <
          (((N / 2) / B : ℕ) : ℝ) := by
        linarith [h2', h3]
      have hAgt : 100 * (M : ℝ) < A := lt_of_not_ge hsmall
      have hscale : A / (100 * (M : ℝ)) - 1 <
          A / (2 * (M : ℝ)) - 2 := by
        field_simp
        nlinarith [hAgt, hMpos]
      exact (hscale.trans hQlow).le
  have hqexp : ((1 : ℝ) / 2) ^ ((N / 2) / B) ≤
      2 * Real.exp (-c * A) := by
    have hbase : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
    have hmono := Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num) hQ
    have hpow : ((1 : ℝ) / 2) ^ ((N / 2) / B) =
        ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hpow]
    have heq : ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) =
        Real.exp (-c * A) := by
      rw [Real.rpow_def_of_pos hbase]
      dsimp [c]
      rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
      congr 1
      field_simp
    rw [← heq]
    calc
      ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) ≤
          ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ)) - 1) := hmono
      _ = 2 * ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) := by
        have he : A / (100 * (M : ℝ)) - 1 =
            A / (100 * (M : ℝ)) + (-1 : ℝ) := by ring
        rw [he, Real.rpow_add hbase]
        ring
  have hpoint : ∀ u : Sandpile.Site 4,
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
    intro u
    have hnonneg := (aux_bg7_timeTail_factor r A u).1
    have hu := (hq u).trans (by
      calc
        _ ≤ (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
            (2 * Real.exp (-c * A)) :=
          mul_le_mul_of_nonneg_left hqexp (by positivity)
        _ = C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
          dsimp [C₀, B]
          norm_num [Nat.cast_mul, Nat.cast_pow]
          field_simp
          ring)
    calc
      |BallGreen.timeTail r A u| = BallGreen.timeTail r A u := abs_of_nonneg hnonneg
      _ ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hu
  have hbox : BallGreen.box r =
      (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv)
      intro i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi i
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u = 0 := by
    intro u hu
    unfold BallGreen.timeTail
    rw [Sandpile.killedGreen_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      Sandpile.killedGreenTime_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      sub_zero]
  refine ⟨?_, ?_⟩
  · intro u
    have hC₀le : C₀ ≤ C := by
      dsimp [C]
      nlinarith [sq_nonneg C₀]
    calc
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hpoint u
      _ ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        gcongr
  · have hsqzero : ∀ u : Sandpile.Site 4,
        u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
          BallGreen.timeTail r A u ^ 2 = 0 := by
      intro u hu
      rw [hzero u hu, zero_pow (by decide : 2 ≠ 0)]
    rw [tsum_eq_sum hsqzero]
    have hE : Real.exp (-c * A) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hAnonneg : (0 : ℝ) ≤ A := by linarith
      linarith [mul_nonneg hc.le hAnonneg]
    have hsum :
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
      calc
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            BallGreen.timeTail r A u ^ 2) ≤
            ∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          have hp := hpoint u
          have hb : 0 ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by positivity
          have hsq : |BallGreen.timeTail r A u| ^ 2 =
              BallGreen.timeTail r A u ^ 2 := sq_abs _
          nlinarith [sq_nonneg (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) -
            |BallGreen.timeTail r A u|), hsq, abs_nonneg (BallGreen.timeTail r A u)]
        _ = ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, LatticeProb.card_boxFinset_zero]
          norm_num
    calc
      (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := hsum
      _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
        have hcard : ((2 * r + 1 : ℕ) : ℝ) ≤ 3 * (r : ℝ) := by
          push_cast
          nlinarith [show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr1]
        have hcard4 : ((2 * r + 1 : ℕ) : ℝ) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := by gcongr
        calc
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 ≤
              (3 * (r : ℝ)) ^ 4 *
                (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 :=
            mul_le_mul_of_nonneg_right hcard4 (sq_nonneg _)
          _ = 81 * C₀ ^ 2 * Real.exp (-c * A) ^ 2 := by
            have hr4 : (r : ℝ) ^ 4 ≠ 0 := by positivity
            field_simp
            ring
          _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
            have hcoef : 0 ≤ 81 * C₀ ^ 2 := by positivity
            have hE2 : Real.exp (-c * A) ^ 2 ≤ Real.exp (-c * A) := by
              have hE0 : 0 ≤ Real.exp (-c * A) := (Real.exp_pos _).le
              calc
                Real.exp (-c * A) ^ 2 = Real.exp (-c * A) * Real.exp (-c * A) := by ring
                _ ≤ Real.exp (-c * A) * 1 :=
                  mul_le_mul_of_nonneg_left hE hE0
                _ = Real.exp (-c * A) := by ring
            exact mul_le_mul_of_nonneg_left hE2 hcoef
      _ ≤ C * Real.exp (-c * A) := by
        have hcoefC : 81 * C₀ ^ 2 ≤ C := by
          dsimp [C]
          nlinarith [hC₀]
        exact mul_le_mul_of_nonneg_right hcoefC (Real.exp_pos _).le

-/

end Sandpile.External

namespace Sandpile.External

/-
theorem aux_ballgreen_clause7_holds : aux_ballgreen_clause7 := by
  obtain ⟨G, g, hG, hg, hheat⟩ := Sandpile.External.gaussianUpper 4 (by norm_num)
  obtain ⟨M, hM, hblock⟩ := aux_bg7_survival_block G g hG hg hheat
  let C₀ : ℝ := 32 * G * (M : ℝ)
  let C : ℝ := 81 * C₀ ^ 2 + C₀ + 1
  let c : ℝ := Real.log 2 / (100 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro r hr A hA
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  let B : ℕ := M * r ^ 2
  have hr1 : 1 ≤ r := by omega
  have hr2 : 1 ≤ r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hr1 hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN : r ^ 2 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hrpow : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by
      norm_num
    rw [hrpow]
    nlinarith [hA, sq_nonneg (r : ℝ)]
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hB1 : 1 ≤ B := by omega
  have hblock0 : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) B x ≤ (1 : ℝ) / 2 := by
    intro x
    simpa [B] using hblock r hr x
  have hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := aux_bg7_survival_summable r
  obtain ⟨hf, hhalf⟩ := aux_bg7_half_survival_tsum
    (LatticeProb.boxFinset 0 r) N 0 hs
  have hshift := aux_bg7_survival_shift_tsum
    (LatticeProb.boxFinset 0 r) B hB hblock0 (N / 2) 0
  have hbox : BallGreen.box r =
      (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv)
      intro i
      have hii := hi i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hii
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hpoint : ∀ u : Sandpile.Site 4,
      0 ≤ BallGreen.timeTail r A u ∧
      BallGreen.timeTail r A u ≤
        (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
    intro u
    have hKsum : Summable (fun j : ℕ =>
        Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) := by
      exact (Sandpile.summable_killedKernel_transient (by norm_num)
        (BallGreen.box r) 0 u).comp_injective (add_right_injective N)
    have htail_sum :
        BallGreen.timeTail r A u ≤
          (4 * G / (r : ℝ) ^ 4) *
            (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := by
      rw [aux_bg7_timeTail_tsum]
      have hright : Summable (fun j : ℕ =>
          (4 * G / (r : ℝ) ^ 4) *
            LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) :=
        hf.mul_left (4 * G / (r : ℝ) ^ 4)
      apply hKsum.tsum_le_tsum
      · intro j
        apply aux_bg7_kernel_step r (N + j) u hr
          (le_trans hN (Nat.le_add_right N j)) G g hG hg hheat
      · exact hright
    have hqbound : BallGreen.timeTail r A u ≤
        (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
      calc
        BallGreen.timeTail r A u ≤
            (4 * G / (r : ℝ) ^ 4) *
              (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
                (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := htail_sum
        _ ≤ (4 * G / (r : ℝ) ^ 4) *
            (2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) (N / 2 + t) 0)) :=
          mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ ≤ (4 * G / (r : ℝ) ^ 4) *
            (2 * ((B : ℝ) * 2 * ((1 : ℝ) / 2) ^ ((N / 2) / B))) :=
          mul_le_mul_of_nonneg_left hshift (by positivity)
        _ = _ := by ring
    have hqexp : ((1 : ℝ) / 2) ^ ((N / 2) / B) ≤
        2 * Real.exp (-c * A) := by
      have hQ : (A / (100 * (M : ℝ)) - 1) ≤
          (((N / 2) / B : ℕ) : ℝ) := by
        by_cases hsmall : A ≤ 100 * (M : ℝ)
        · have hh : A / (100 * (M : ℝ)) - 1 ≤ 0 := by
            have := (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (M : ℝ))).2 hsmall
            linarith
          positivity
        · have hNfloor : A * (r : ℝ) ^ 2 < (N : ℝ) + 1 := by
            dsimp [N]
            exact Nat.lt_floor_add_one _
        have hLfloor : (N : ℝ) < 2 * ((N / 2 : ℕ) : ℝ) + 2 := by
          have hh : N < 2 * (N / 2 + 1) := by omega
          exact_mod_cast hh
        have hQfloor : ((N / 2 : ℕ) : ℝ) <
            (B : ℝ) * ((((N / 2) / B : ℕ) : ℝ) + 1) := by
          have hh : N / 2 < B * (N / 2 / B + 1) := by omega
          exact_mod_cast hh
        have hBr : (B : ℝ) = (M : ℝ) * (r : ℝ) ^ 2 := by
          simp [B, Nat.cast_mul, Nat.cast_pow]
        have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
        have hQlow : (A / (2 * (M : ℝ)) - 2) <
            (((N / 2) / B : ℕ) : ℝ) := by
          have h1 : A * (r : ℝ) ^ 2 / 2 - 1 < ((N / 2 : ℕ) : ℝ) := by
            nlinarith [hNfloor, hLfloor]
          have h2 := (div_lt_div_iff₀ hBpos hBpos).2 h1
          have h3 :
              ((N / 2 : ℕ) : ℝ) / (B : ℝ) - 1 <
                (((N / 2) / B : ℕ) : ℝ) := by
            have := (div_lt_iff₀ hBpos).2 (by nlinarith [hQfloor])
            linarith
          rw [hBr] at h2
          have hBge : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
          have hInv : 1 / (B : ℝ) ≤ 1 := by
            exact (div_le_iff₀ hBpos).2 (by nlinarith)
          have hmain : A / (2 * (M : ℝ)) - 2 ≤
              A / (100 * (M : ℝ)) - 1 := by
            field_simp
            nlinarith [hsmall, hMpos]
          linarith
        exact hQlow.trans (by
          field_simp
          nlinarith [hsmall, hMpos])
      have hbase : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      have hpow : ((1 : ℝ) / 2) ^ ((N / 2) / B) =
          ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      have hmono := Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num)
        hQ
      rw [hpow]
      have heq : ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) =
          Real.exp (-c * A) := by
        rw [Real.rpow_def_of_pos hbase]
        dsimp [c]
        rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
          rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
        congr 1
        field_simp
      rw [← heq]
      calc
        ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) ≤
            ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ)) - 1) := hmono
        _ = 2 * ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) := by
          rw [← Real.rpow_add hbase.le]
          norm_num
          ring
    have hnonneg : 0 ≤ BallGreen.timeTail r A u :=
      (aux_bg7_timeTail_factor r A u).1
    refine ⟨hnonneg, ?_⟩
    calc
      BallGreen.timeTail r A u ≤
          (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
            ((1 : ℝ) / 2) ^ ((N / 2) / B) := hqbound
      _ ≤ (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          (2 * Real.exp (-c * A)) :=
        mul_le_mul_of_nonneg_left hqexp (by positivity)
      _ = C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        dsimp [C₀, B]
        field_simp
        ring
      _ ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        gcongr
        dsimp [C]
        linarith
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u = 0 := by
    intro u hu
    unfold BallGreen.timeTail
    rw [Sandpile.killedGreen_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      Sandpile.killedGreenTime_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      sub_zero]
  refine ⟨?_, ?_⟩
  · intro u
    by_cases hu : u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r
    · rw [hzero u hu, abs_zero]
      positivity
    · have hh := (show 0 ≤ BallGreen.timeTail r A u from
        (aux_bg7_timeTail_factor r A u).1)
      exact (abs_of_nonneg hh).trans_le (by
        have h := (show BallGreen.timeTail r A u ≤
            C / (r : ℝ) ^ 2 * Real.exp (-c * A) from by
          exact (by
            have := (aux_bg7_timeTail_factor r A u).2
            unfinished))
        exact h)
  · have hsqzero : ∀ u : Sandpile.Site 4,
        u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
          BallGreen.timeTail r A u ^ 2 = 0 := by
      intro u hu
      rw [hzero u hu, zero_pow (by decide : 2 ≠ 0)]
    rw [tsum_eq_sum hsqzero]
    have hsumq := Finset.sum_le_sum (s := LatticeProb.boxFinset (0 : Sandpile.Site 4) r)
      (fun u hu => by
        have h := (aux_bg7_timeTail_factor r A u).2
        unfinished)
    calc
      (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          81 * C₀ ^ 2 * Real.exp (-c * A) := by
        unfinished
      _ ≤ C * Real.exp (-c * A) := by
        have hcoefC : 81 * C₀ ^ 2 ≤ C := by
          dsimp [C]
          nlinarith [hC₀]
        exact mul_le_mul_of_nonneg_right hcoefC (Real.exp_pos _).le
-/

end Sandpile.External

namespace Sandpile.External

/-
theorem aux_ballgreen_clause7_holds : aux_ballgreen_clause7 := by
  obtain ⟨G, g, hG, hg, hheat⟩ := Sandpile.External.gaussianUpper 4 (by norm_num)
  obtain ⟨M, hM, hblock⟩ := aux_bg7_survival_block G g hG hg hheat
  let C₀ : ℝ := 32 * G * (M : ℝ)
  let C : ℝ := 81 * C₀ ^ 2 + C₀ + 1
  let c : ℝ := Real.log 2 / (100 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro r hr A hA
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  let B : ℕ := M * r ^ 2
  have hr1 : 1 ≤ r := by omega
  have hr2 : 1 ≤ r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hr1 hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN : r ^ 2 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hAr : (r : ℝ) ^ 2 ≤ A * (r : ℝ) ^ 2 := by
      nlinarith [hA, sq_nonneg (r : ℝ)]
    exact hAr
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hblock0 : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) B x ≤ (1 : ℝ) / 2 := by
    intro x
    simpa [B] using hblock r hr x
  have hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := aux_bg7_survival_summable r
  obtain ⟨hf, hhalf⟩ := aux_bg7_half_survival_tsum
    (LatticeProb.boxFinset 0 r) N 0 hs
  have hshift := aux_bg7_survival_shift_tsum
    (LatticeProb.boxFinset 0 r) B hB hblock0 (N / 2) 0
  have hKsum : Summable (fun j : ℕ =>
      Sandpile.killedKernel (BallGreen.box r) (N + j) 0 0) := by
    exact (Sandpile.summable_killedKernel_transient (by norm_num)
      (BallGreen.box r) 0 0).comp_injective (add_right_injective N)
  have htail_sum :
      BallGreen.timeTail r A 0 ≤
        (4 * G / (r : ℝ) ^ 4) *
          (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := by
    rw [aux_bg7_timeTail_tsum]
    have hright : Summable (fun j : ℕ =>
        (4 * G / (r : ℝ) ^ 4) *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) :=
      hf.mul_left (4 * G / (r : ℝ) ^ 4)
    apply hKsum.tsum_le_tsum
    · intro j
      apply aux_bg7_kernel_step r (N + j) 0 hr
      exact le_trans hN (Nat.le_add_right N j)
    · exact hright
  have hqbound : BallGreen.timeTail r A 0 ≤
      (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
        ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
    calc
      BallGreen.timeTail r A 0 ≤
          (4 * G / (r : ℝ) ^ 4) *
            (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := htail_sum
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) (N / 2 + t) 0)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * ((B : ℝ) * 2 * ((1 : ℝ) / 2) ^ ((N / 2) / B))) :=
        mul_le_mul_of_nonneg_left hshift (by positivity)
      _ = _ := by ring
  have hqexp : ((1 : ℝ) / 2) ^ ((N / 2) / B) ≤
      2 * Real.exp (-c * A) := by
    have hq0 : (0 : ℝ) ≤ (((N / 2) / B : ℕ) : ℝ) := by positivity
    have hbase : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
    have hbase1 : (1 : ℝ) / 2 ≤ 1 := by norm_num
    have hpow : ((1 : ℝ) / 2) ^ ((N / 2) / B) =
        ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hqreal : (A / (100 * (M : ℝ)) - 1) ≤
        (((N / 2) / B : ℕ) : ℝ) := by
      by_cases hsmall : A ≤ 100 * (M : ℝ)
      · have : A / (100 * (M : ℝ)) - 1 ≤ 0 := by
          have := div_le_one hsmall
          linarith
        linarith
      · unfinished
    rw [hpow]
    have hpowmono := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hqreal
    have heq : ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) =
        Real.exp (-c * A) := by
      rw [Real.rpow_def_of_pos hbase]
      dsimp [c]
      rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
      congr 1
      field_simp
    rw [← heq]
    have hminus : ((1 : ℝ) / 2) ^ (-1 : ℝ) = 2 := by norm_num
    calc
      ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) ≤
          ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ)) - 1) := hpowmono
      _ = 2 * ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) := by
        rw [← Real.rpow_add hbase.le]
        norm_num
        ring
  have hpoint0 : BallGreen.timeTail r A 0 ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
    calc
      BallGreen.timeTail r A 0 ≤
          (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
            ((1 : ℝ) / 2) ^ ((N / 2) / B) := hqbound
      _ ≤ (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          (2 * Real.exp (-c * A)) :=
        mul_le_mul_of_nonneg_left hqexp (by positivity)
      _ = C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        dsimp [C₀, B]
        field_simp
        ring
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u = 0 := by
    intro u hu
    unfold BallGreen.timeTail
    rw [Sandpile.killedGreen_eq_zero_of_target_notMem _ (by
      intro h
      exact hu (by rw [show BallGreen.box r =
        (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) from by
          ext v
          constructor
          · intro hv; apply Sandpile.mem_boxFinset; apply Finset.sup_le
            intro i _
            simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
          · intro hv i
            have hi := (LatticeProb.mem_boxFinset_iff.mp hv) i
            have hi0 : |u i| ≤ (r : ℤ) := by simpa [sub_zero] using hi
            have hi1 : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by
              rw [Int.natCast_natAbs]
              exact hi0
            exact_mod_cast hi1]
        exact h),
      Sandpile.killedGreenTime_eq_zero_of_target_notMem _ (by
        intro h
        exact hu (by rw [show BallGreen.box r =
          (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) from by
            ext v
            constructor
            · intro hv; apply Sandpile.mem_boxFinset; apply Finset.sup_le
              intro i _
              simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
            · intro hv i
              have hi := (LatticeProb.mem_boxFinset_iff.mp hv) i
              have hi0 : |u i| ≤ (r : ℤ) := by simpa [sub_zero] using hi
              have hi1 : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by
                rw [Int.natCast_natAbs]
                exact hi0
              exact_mod_cast hi]
          exact h), sub_zero]
  refine ⟨?_, ?_⟩
  · intro u
    by_cases hu : u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r
    · rw [hzero u hu, abs_zero]
      positivity
    · have htrans : BallGreen.timeTail r A u =
          BallGreen.timeTail r A 0 := by
        unfinished
      rw [htrans]
      exact (abs_of_nonneg (by positivity)).trans (hpoint0)
  · have hsqzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u ^ 2 = 0 := by
      intro u hu; rw [hzero u hu, zero_pow (by decide : 2 ≠ 0)]
    rw [tsum_eq_sum hsqzero]
    have hsumq : ∀ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
        BallGreen.timeTail r A u ^ 2 ≤
          (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
      intro u hu
      unfinished
    calc
      (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 :=
        Finset.sum_le_sum fun u hu => hsumq u hu
      _ = ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
          (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, LatticeProb.card_boxFinset_zero]
        norm_num
      _ ≤ C * Real.exp (-c * A) := by
        unfinished
-/

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_timeTail_tsum (r : ℕ) (A : ℝ) (u : Sandpile.Site 4) :
    BallGreen.timeTail r A u =
      ∑' j : ℕ, Sandpile.killedKernel (BallGreen.box r)
        (⌊A * (r : ℝ) ^ 2⌋₊ + j) 0 u := by
  let D : Set (Sandpile.Site 4) := BallGreen.box r
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  have hsum : Summable (fun k : ℕ => Sandpile.killedKernel D k 0 u) := by
    exact Sandpile.summable_killedKernel_transient (by norm_num) D 0 u
  unfold BallGreen.timeTail
  rw [Sandpile.killedGreen, Sandpile.killedGreenTime]
  have h := hsum.sum_add_tsum_nat_add ⌊A * (r : ℝ) ^ 2⌋₊
  have h' :
      (∑ k ∈ Finset.range ⌊A * (r : ℝ) ^ 2⌋₊,
          Sandpile.killedKernel D k 0 u) +
          ∑' j : ℕ, Sandpile.killedKernel D
            (⌊A * (r : ℝ) ^ 2⌋₊ + j) 0 u =
        ∑' k : ℕ, Sandpile.killedKernel D k 0 u := by
    simpa [Nat.add_comm] using h
  linarith

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_survival_summable (r : ℕ) :
    Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := by
  let D : Set (Sandpile.Site 4) := BallGreen.box r
  have hDset : D = (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [D, BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hv' : v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := hv
      intro i
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv') i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have heq (n : ℕ) :
      LatticeProb.Network.survival (LatticeProb.lattice 4)
          (LatticeProb.boxFinset 0 r) n 0 =
        ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          Sandpile.killedKernel D n 0 v := by
    rw [LatticeProb.Network.survival]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hDset, Sandpile.killedKernel_eq_graph]
  have hker (v : Sandpile.Site 4) :
      Summable (fun n : ℕ => Sandpile.killedKernel D n 0 v) :=
    Sandpile.summable_killedKernel_transient (by norm_num) D 0 v
  apply summable_of_sum_range_le
  · intro n
    exact LatticeProb.Network.survival_nonneg _ _ _
  · intro n
    calc
      ∑ k ∈ Finset.range n,
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) k 0 =
          ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            ∑ k ∈ Finset.range n, Sandpile.killedKernel D k 0 v := by
        simp_rw [heq]
        rw [Finset.sum_comm]
      _ ≤ ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            ∑' k : ℕ, Sandpile.killedKernel D k 0 v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (hker v).sum_le_tsum _ (fun k hk => Sandpile.killedKernel_nonneg D k 0 v)

end Sandpile.External


namespace Sandpile.External

theorem aux_bg7_half_survival_tsum
    (C : Finset (Sandpile.Site 4)) (N : ℕ) (x : Sandpile.Site 4)
    (hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4) C n x)) :
    Summable (fun j : ℕ => LatticeProb.Network.survival (LatticeProb.lattice 4) C
        ((N + j) / 2) x) ∧
    (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4) C
        ((N + j) / 2) x) ≤
      2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4) C
        (N / 2 + t) x) := by
  let S := fun n : ℕ => LatticeProb.Network.survival
    (LatticeProb.lattice 4) C n x
  let f := fun j : ℕ => S ((N + j) / 2)
  let g := fun t : ℕ => S (N / 2 + t)
  have hgs : Summable g := by
    dsimp [g]
    exact hs.comp_injective (add_right_injective (N / 2))
  have he : Summable (fun t : ℕ => f (2 * t)) := by
    have hfun : (fun t : ℕ => f (2 * t)) = g := by
      funext t
      dsimp [f, g]
      congr 1
      omega
    rw [hfun]
    exact hgs
  have ho : Summable (fun t : ℕ => f (2 * t + 1)) := by
    have hh := hs.comp_injective (add_right_injective ((N + 1) / 2))
    have hfun : (fun t : ℕ => f (2 * t + 1)) =
        (fun t : ℕ => S ((N + 1) / 2 + t)) := by
      funext t
      dsimp [f]
      congr 1
      omega
    rw [hfun]
    exact hh
  have hodd : (∑' t : ℕ, f (2 * t + 1)) ≤ ∑' t : ℕ, g t := by
    apply ho.tsum_le_tsum
    · intro t
      dsimp [f, g]
      apply LatticeProb.Network.survival_antitone
      omega
    · exact hgs
  have hdecomp := tsum_even_add_odd he ho
  refine ⟨he.even_add_odd ho, ?_⟩
  dsimp [f, g] at hdecomp ⊢
  calc
    (∑' j : ℕ, S ((N + j) / 2)) =
        (∑' t : ℕ, f (2 * t)) + (∑' t : ℕ, f (2 * t + 1)) := hdecomp.symm
    _ ≤ (∑' t : ℕ, g t) + (∑' t : ℕ, g t) := by
      have heq : (∑' t : ℕ, f (2 * t)) = ∑' t : ℕ, g t := by
        rw [show (fun t : ℕ => f (2 * t)) = g from by
          funext t
          dsimp [f, g]
          congr 1
          omega]
      rw [heq]
      exact add_le_add le_rfl hodd
    _ = 2 * (∑' t : ℕ, g t) := by ring

end Sandpile.External


namespace Sandpile.External

theorem aux_bg7_kernel_mass (r n : ℕ) :
    (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) n,
      Sandpile.killedKernel (BallGreen.box r) n 0 v) =
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0 := by
  let D : Set (Sandpile.Site 4) := BallGreen.box r
  have hDset : D = (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [D, BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hv' : v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := hv
      intro i
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv') i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hzero : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) n →
        Sandpile.killedKernel D n 0 v = 0 := by
    intro v hv
    by_contra hne
    exact hv (Sandpile.mem_boxFinset
      (Sandpile.killedKernel_support D n 0 hne))
  have hzeroC : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        Sandpile.killedKernel D n 0 v = 0 := by
    intro v hv
    apply Sandpile.killedKernel_eq_zero_of_target_notMem D
    rw [hDset]
    exact hv
  have hsum :
      (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) n,
        Sandpile.killedKernel D n 0 v) =
        ∑' v : Sandpile.Site 4, Sandpile.killedKernel D n 0 v :=
    (tsum_eq_sum hzero).symm
  rw [hsum, tsum_eq_sum hzeroC]
  apply Finset.sum_congr rfl
  intro v hv
  rw [hDset, Sandpile.killedKernel_eq_graph]

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_survival_shift_tsum
    (C : Finset (Sandpile.Site 4)) (B : ℕ) (hB : 0 < B)
    (hblock : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4) C B x ≤ (1 : ℝ) / 2)
    (K : ℕ) (x : Sandpile.Site 4) :
    (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4) C (K + j) x) ≤
      (B : ℝ) * 2 * ((1 : ℝ) / 2) ^ (K / B) := by
  let S := fun n : ℕ => LatticeProb.Network.survival
    (LatticeProb.lattice 4) C n x
  have hstrong : ∀ (q k : ℕ),
      S (k + q * B) ≤ ((1 : ℝ) / 2) ^ q * S k := by
    intro q
    induction q with
    | zero => intro k; simp [S]
    | succ q ih =>
        intro k
        have hs := LatticeProb.Network.survival_add_le
          (G := LatticeProb.lattice 4) (C := C) (N := B) (θ := (1 : ℝ) / 2)
          hblock
          (k + q * B) x
        have hi := ih k
        have hrewrite : k + (q + 1) * B = (k + q * B) + B := by ring
        rw [hrewrite]
        calc
          S ((k + q * B) + B) ≤ (1 / 2 : ℝ) * S (k + q * B) := hs
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ q * S k) :=
            mul_le_mul_of_nonneg_left hi (by positivity)
          _ = (1 / 2 : ℝ) ^ (q + 1) * S k := by ring
  have hpartial : ∀ n : ℕ,
      ∑ j ∈ Finset.range n, S (K + j) ≤
        (B : ℝ) * 2 * ((1 : ℝ) / 2) ^ (K / B) := by
    intro n
    let q := K / B
    let rem := K % B
    have hK : K = rem + q * B := by
      dsimp [q, rem]
      calc
        K = K % B + B * (K / B) := (Nat.mod_add_div K B).symm
        _ = K % B + (K / B) * B := by rw [Nat.mul_comm]
    have hterm : ∀ j : ℕ, S (K + j) ≤
        ((1 : ℝ) / 2) ^ q * S (rem + j) := by
      intro j
      have heq : K + j = (rem + j) + q * B := by
        rw [hK]
        omega
      rw [heq]
      exact hstrong q (rem + j)
    have hsumterm :
        (∑ j ∈ Finset.range n, S (K + j)) ≤
          ((1 : ℝ) / 2) ^ q * ∑ j ∈ Finset.range n, S (rem + j) := by
      calc
        _ ≤ ∑ j ∈ Finset.range n,
            ((1 : ℝ) / 2) ^ q * S (rem + j) :=
          Finset.sum_le_sum fun j hj => hterm j
        _ = _ := by rw [Finset.mul_sum]
    have hrange :
        ∑ j ∈ Finset.range n, S (rem + j) ≤
          ∑ k ∈ Finset.range (rem + n), S k := by
      have he := Finset.sum_range_add (f := S) rem n
      have hnon : 0 ≤ ∑ k ∈ Finset.range rem, S k :=
        Finset.sum_nonneg fun k hk => LatticeProb.Network.survival_nonneg C k x
      rw [he]
      linarith
    have htotal := LatticeProb.Network.sum_range_survival_le
      (G := LatticeProb.lattice 4) hB (by positivity : (0 : ℝ) ≤ (1 : ℝ) / 2)
      (by norm_num : (1 : ℝ) / 2 < 1) hblock x (rem + n)
    have hpow : ((1 : ℝ) / 2) ^ q = ((1 : ℝ) / 2) ^ (K / B) := by rfl
    calc
      _ ≤ ((1 : ℝ) / 2) ^ q * ∑ j ∈ Finset.range n, S (rem + j) := hsumterm
      _ ≤ ((1 : ℝ) / 2) ^ q * ((B : ℝ) / (1 - (1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hrange.trans htotal) (by positivity)
      _ = (B : ℝ) * 2 * ((1 : ℝ) / 2) ^ (K / B) := by
        rw [hpow]
        norm_num
        ring
  apply Real.tsum_le_of_sum_range_le
  · intro n
    exact LatticeProb.Network.survival_nonneg C (K + n) x
  · intro n
    exact hpartial n

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_killedPair_target_indicator (D : Set (Sandpile.Site 4))
    (n : ℕ) (f : Sandpile.Site 4 → ℝ) (x : Sandpile.Site 4) :
    Sandpile.killedPair D n f x =
      Sandpile.killedPair D n (D.indicator f) x := by
  unfold Sandpile.killedPair
  refine tsum_congr fun y => ?_
  by_cases hy : y ∈ D
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    simp [Sandpile.killedKernel_eq_zero_of_target_notMem D hy]

theorem aux_bg7_killedPair_add (D : Set (Sandpile.Site 4))
    (m n : ℕ) (f : Sandpile.Site 4 → ℝ) (x : Sandpile.Site 4) :
    Sandpile.killedPair D (m + n) f x =
      Sandpile.killedPair D m (fun y => Sandpile.killedPair D n f y) x := by
  induction n generalizing m f x with
  | zero =>
      rw [Nat.add_zero]
      have h := aux_bg7_killedPair_target_indicator D m f x
      simpa only [Sandpile.killedPair_zero] using h
  | succ n ih =>
      calc
        Sandpile.killedPair D (m + (n + 1)) f x =
            Sandpile.killedPair D (m + n)
              (fun z => Sandpile.avg (D.indicator f) z) x := by
                rw [show m + (n + 1) = (m + n) + 1 by omega,
                  Sandpile.killedPair_succ_shift]
        _ = Sandpile.killedPair D m
              (fun y => Sandpile.killedPair D n
                (fun z => Sandpile.avg (D.indicator f) z) y) x :=
              ih m (fun z => Sandpile.avg (D.indicator f) z) x
        _ = Sandpile.killedPair D m
              (fun y => Sandpile.killedPair D (n + 1) f y) x := by
              congr 2
              funext y
              rw [Sandpile.killedPair_succ_shift]

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_killedPair_delta (D : Set (Sandpile.Site 4))
    (n : ℕ) (u x : Sandpile.Site 4) :
    Sandpile.killedPair D n (fun y => if y = u then (1 : ℝ) else 0) x =
      Sandpile.killedKernel D n x u := by
  classical
  unfold Sandpile.killedPair
  rw [tsum_eq_single u]
  · simp
  · intro y hy
    simp [hy]

theorem aux_bg7_killedKernel_semigroup (D : Set (Sandpile.Site 4))
    (m n : ℕ) (x u : Sandpile.Site 4) :
    Sandpile.killedKernel D (m + n) x u =
      ∑ v ∈ LatticeProb.boxFinset x m,
        Sandpile.killedKernel D m x v * Sandpile.killedKernel D n v u := by
  have hdelta : ∀ (q : ℕ) (v : Sandpile.Site 4),
      Sandpile.killedPair D q (fun y => if y = u then 1 else 0) v =
        Sandpile.killedKernel D q v u := by
    intro q v
    exact aux_bg7_killedPair_delta D q u v
  rw [← hdelta (m + n) x, aux_bg7_killedPair_add D m n
    (fun y => if y = u then 1 else 0) x]
  have hzero : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset x m → Sandpile.killedKernel D m x v = 0 := by
    intro v hv
    by_contra hne
    exact hv (Sandpile.mem_boxFinset
      (Sandpile.killedKernel_support D m x hne))
  have hfun : (fun y => Sandpile.killedPair D n
      (fun z => if z = u then (1 : ℝ) else 0) y) =
      (fun y => Sandpile.killedKernel D n y u) := by
    funext y
    exact hdelta n y
  rw [hfun]
  unfold Sandpile.killedPair
  have hzero' : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset x m →
        Sandpile.killedKernel D m x v * Sandpile.killedKernel D n v u = 0 := by
    intro v hv
    rw [hzero v hv, zero_mul]
  rw [tsum_eq_sum hzero']

theorem aux_bg7_kernel_step (r k : ℕ) (u : Sandpile.Site 4)
    (hr : 2 ≤ r) (hk : r ^ 2 ≤ k) (G g : ℝ) (hG : 0 < G) (hg : 0 < g)
    (hheat : ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site 4,
      Sandpile.heatKernel 4 n x y ≤
        G * (n : ℝ) ^ (-(4 : ℝ) / 2) *
          Real.exp (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ))) :
    Sandpile.killedKernel (BallGreen.box r) k 0 u ≤
      (4 * G / (r : ℝ) ^ 4) *
        LatticeProb.Network.survival (LatticeProb.lattice 4)
          (LatticeProb.boxFinset 0 r) (k / 2) 0 := by
  let m := k / 2
  let l := k - m
  have hkl : k = m + l := by
    dsimp [m, l]
    omega
  have hhalf : (m + l) / 2 = m := by
    change (k / 2 + (k - k / 2)) / 2 = k / 2
    omega
  rw [hkl, aux_bg7_killedKernel_semigroup, hhalf]
  have hl : 1 ≤ l := by
    change 1 ≤ k - k / 2
    have hr1 : 1 ≤ r := by omega
    have hr2 : 1 ≤ r ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hr1 hr1
    have : 1 ≤ k := le_trans hr2 hk
    omega
  have hpoint : ∀ v : Sandpile.Site 4,
      Sandpile.killedKernel (BallGreen.box r) l v u ≤ G / (l : ℝ) ^ 2 := by
    intro v
    apply (Sandpile.killedKernel_le_heatKernel _ _ _ _).trans
    have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hexp : Real.exp (-g * Sandpile.External.latticeDist v u ^ 2 / (l : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hh : 0 ≤ g * Sandpile.External.latticeDist v u ^ 2 / (l : ℝ) := by positivity
      have heq : -g * Sandpile.External.latticeDist v u ^ 2 / (l : ℝ) =
          -(g * Sandpile.External.latticeDist v u ^ 2 / (l : ℝ)) := by ring
      rw [heq]
      exact neg_nonpos.mpr hh
    have hp : (l : ℝ) ^ (-(4 : ℝ) / 2) = ((l : ℝ) ^ 2)⁻¹ := by
      rw [show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num,
        Real.rpow_neg (le_of_lt hlpos), Real.rpow_two]
    have hh := hheat l hl v u
    rw [hp] at hh
    have hn : 0 ≤ G * ((l : ℝ) ^ 2)⁻¹ := by positivity
    calc
      Sandpile.heatKernel 4 l v u ≤
          G * ((l : ℝ) ^ 2)⁻¹ * Real.exp
            (-g * Sandpile.External.latticeDist v u ^ 2 / (l : ℝ)) := by
        exact hh
      _ ≤ G * ((l : ℝ) ^ 2)⁻¹ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hn
      _ = G / (l : ℝ) ^ 2 := by rw [div_eq_mul_inv]
  have hsum :
      (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) m,
        Sandpile.killedKernel (BallGreen.box r) m 0 v) =
        LatticeProb.Network.survival (LatticeProb.lattice 4)
          (LatticeProb.boxFinset 0 r) m 0 :=
    aux_bg7_kernel_mass r m
  have hnon : 0 ≤ LatticeProb.Network.survival (LatticeProb.lattice 4)
      (LatticeProb.boxFinset 0 r) m 0 :=
    LatticeProb.Network.survival_nonneg _ _ _
  have hsum' :
      (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) m,
        Sandpile.killedKernel (BallGreen.box r) m 0 v *
          Sandpile.killedKernel (BallGreen.box r) l v u) ≤
        (G / (l : ℝ) ^ 2) *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) m 0 := by
    calc
      _ ≤ ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) m,
          Sandpile.killedKernel (BallGreen.box r) m 0 v * (G / (l : ℝ) ^ 2) :=
        Finset.sum_le_sum fun v hv =>
          mul_le_mul_of_nonneg_left (hpoint v)
            (Sandpile.killedKernel_nonneg _ _ _ _)
      _ = (G / (l : ℝ) ^ 2) *
          ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) m,
            Sandpile.killedKernel (BallGreen.box r) m 0 v := by
        rw [← Finset.sum_mul]
        ring
      _ = _ := by rw [hsum]
  have hlower : (r : ℝ) ^ 2 / 2 ≤ (l : ℝ) := by
    dsimp [l, m]
    have hkR : (r : ℝ) ^ 2 ≤ (k : ℝ) := by exact_mod_cast hk
    have hdivN : k ≤ 2 * (k - k / 2) := by omega
    have hdiv : (k : ℝ) ≤ 2 * ((k - k / 2 : ℕ) : ℝ) := by exact_mod_cast hdivN
    linarith
  have hden : 0 < (r : ℝ) ^ 4 / 4 := by positivity
  have hden' : 0 < (l : ℝ) ^ 2 := by positivity
  have hden_le : (r : ℝ) ^ 4 / 4 ≤ (l : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((r : ℝ) ^ 2 / 2), hlower]
  have hratio : G / (l : ℝ) ^ 2 ≤ 4 * G / (r : ℝ) ^ 4 := by
    rw [show 4 * G / (r : ℝ) ^ 4 = G / ((r : ℝ) ^ 4 / 4) by field_simp]
    apply (div_le_div_iff₀ hden' hden).2
    exact mul_le_mul_of_nonneg_left hden_le hG.le
  exact hsum'.trans (mul_le_mul_of_nonneg_right hratio hnon)

theorem aux_bg7_timeTail_factor (r : ℕ) (A : ℝ) (u : Sandpile.Site 4) :
    0 ≤ BallGreen.timeTail r A u ∧
      BallGreen.timeTail r A u ≤
        Sandpile.green 4 0 0 *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r)
            ⌊A * (r : ℝ) ^ 2⌋₊ 0 := by
  let D : Set (Sandpile.Site 4) := BallGreen.box r
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  have hsum : Summable (fun k : ℕ => Sandpile.killedKernel D k 0 u) := by
    exact Sandpile.summable_killedKernel_transient (by norm_num) D 0 u
  have htail : BallGreen.timeTail r A u =
      ∑' j : ℕ, Sandpile.killedKernel D (N + j) 0 u := by
    unfold BallGreen.timeTail
    dsimp [D, N]
    rw [Sandpile.killedGreen, Sandpile.killedGreenTime]
    have h := hsum.sum_add_tsum_nat_add N
    have h' :
        (∑ k ∈ Finset.range N, Sandpile.killedKernel D k 0 u) +
            ∑' j : ℕ, Sandpile.killedKernel D (N + j) 0 u =
          ∑' k : ℕ, Sandpile.killedKernel D k 0 u := by
      simpa [Nat.add_comm] using h
    linarith
  have hdelta : ∀ (j : ℕ) (v : Sandpile.Site 4),
      Sandpile.killedPair D j (fun y => if y = u then (1 : ℝ) else 0) v =
        Sandpile.killedKernel D j v u := by
    intro j v
    exact aux_bg7_killedPair_delta D j u v
  have hsem : ∀ (j : ℕ),
      Sandpile.killedKernel D (N + j) 0 u =
        ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
          Sandpile.killedKernel D N 0 v * Sandpile.killedKernel D j v u := by
    intro j
    calc
      Sandpile.killedKernel D (N + j) 0 u =
          Sandpile.killedPair D (N + j)
            (fun y => if y = u then (1 : ℝ) else 0) 0 :=
        (hdelta (N + j) 0).symm
      _ = Sandpile.killedPair D N
            (fun v => Sandpile.killedPair D j
              (fun y => if y = u then (1 : ℝ) else 0) v) 0 :=
        aux_bg7_killedPair_add D N j (fun y => if y = u then (1 : ℝ) else 0) 0
      _ = ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
            Sandpile.killedKernel D N 0 v * Sandpile.killedKernel D j v u := by
        rw [Sandpile.killedPair_eq_sum]
        exact Finset.sum_congr rfl fun v hv => by rw [hdelta]
  have hsumj : ∀ v : Sandpile.Site 4,
      Summable (fun j : ℕ => Sandpile.killedKernel D j v u) := by
    intro v
    exact Sandpile.summable_killedKernel_transient (by norm_num) D v u
  have hq : BallGreen.timeTail r A u =
      ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
        Sandpile.killedKernel D N 0 v * Sandpile.killedGreen D v u := by
    rw [htail, show (fun j : ℕ => Sandpile.killedKernel D (N + j) 0 u) =
      fun j => ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
        Sandpile.killedKernel D N 0 v * Sandpile.killedKernel D j v u by
          funext j; exact hsem j]
    rw [Summable.tsum_finsetSum (fun v hv =>
      (hsumj v).mul_left (Sandpile.killedKernel D N 0 v))]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Sandpile.killedGreen]
    rw [tsum_mul_left]
  have hgreen : ∀ v : Sandpile.Site 4,
      Sandpile.killedGreen D v u ≤ Sandpile.green 4 0 0 := by
    intro v
    have hsumFree : Summable (fun k : ℕ => Sandpile.heatKernel 4 k v u) :=
      Sandpile.summable_heatKernel_transient (by norm_num) v u
    have hsumKilled : Summable (fun k : ℕ => Sandpile.killedKernel D k v u) :=
      Summable.of_nonneg_of_le
        (fun k => Sandpile.killedKernel_nonneg D k v u)
        (fun k => Sandpile.killedKernel_le_heatKernel D k v u) hsumFree
    have hdom : Sandpile.killedGreen D v u ≤ Sandpile.green 4 v u := by
      rw [Sandpile.killedGreen, Sandpile.green]
      exact hsumKilled.tsum_le_tsum
        (fun k => Sandpile.killedKernel_le_heatKernel D k v u) hsumFree
    exact hdom.trans (Sandpile.green_le_diagonal (by norm_num) v u)
  have hnonneg : 0 ≤ BallGreen.timeTail r A u := by
    rw [hq]
    exact Finset.sum_nonneg fun v hv =>
      mul_nonneg (Sandpile.killedKernel_nonneg D N 0 v) (by
        rw [Sandpile.killedGreen]
        exact tsum_nonneg fun k => Sandpile.killedKernel_nonneg D k v u)
  refine ⟨hnonneg, ?_⟩
  have hSzero : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) N →
        Sandpile.killedKernel D N 0 v = 0 := by
    intro v hv
    by_contra hne
    exact hv (Sandpile.mem_boxFinset
      (Sandpile.killedKernel_support D N 0 hne))
  have hDset : D = (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [D, BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv i
      have hv' : v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := hv
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv') i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hS : (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
      Sandpile.killedKernel D N 0 v) =
      ∑' v : Sandpile.Site 4, Sandpile.killedKernel D N 0 v :=
    (tsum_eq_sum hSzero).symm
  have hCzero : ∀ v : Sandpile.Site 4,
      v ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        Sandpile.killedKernel D N 0 v = 0 := by
    intro v hv
    apply Sandpile.killedKernel_eq_zero_of_target_notMem D
    rw [hDset]
    exact hv
  have hfull : (∑' v : Sandpile.Site 4, Sandpile.killedKernel D N 0 v) =
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) N 0 := by
    rw [tsum_eq_sum hCzero]
    calc
      (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          Sandpile.killedKernel D N 0 v) =
          ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            LatticeProb.Graph.killedHeat (LatticeProb.lattice 4)
              {w : Sandpile.Site 4 |
                w ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r} N 0 v := by
            apply Finset.sum_congr rfl
            intro v hv
            rw [hDset, Sandpile.killedKernel_eq_graph]
            congr 1
      _ = LatticeProb.Network.survival (LatticeProb.lattice 4)
          (LatticeProb.boxFinset 0 r) N 0 := rfl
  rw [hq]
  calc
    (∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
        Sandpile.killedKernel D N 0 v * Sandpile.killedGreen D v u) ≤
        ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) N,
          Sandpile.killedKernel D N 0 v * Sandpile.green 4 0 0 := by
            exact Finset.sum_le_sum fun v hv =>
              mul_le_mul_of_nonneg_left (hgreen v)
                (Sandpile.killedKernel_nonneg D N 0 v)
    _ = Sandpile.green 4 0 0 *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) N 0 := by
          rw [← Finset.sum_mul, hS, hfull]
          ring

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_gaussian_upper_d4 (G g : ℝ)
    (hG : 0 < G) (hg : 0 < g)
    (hheat : ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site 4,
      Sandpile.heatKernel 4 n x y ≤
        G * (n : ℝ) ^ (-(4 : ℝ) / 2) *
          Real.exp (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) (x y : Sandpile.Site 4) :
    Sandpile.heatKernel 4 n x y ≤ G / (n : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hexp : Real.exp (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ) := by positivity
    have heq : -g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ) =
        -(g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := by ring
    rw [heq]
    exact neg_nonpos.mpr this
  have hp : (n : ℝ) ^ (-(4 : ℝ) / 2) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [show (-(4 : ℝ) / 2) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt hnpos), Real.rpow_two]
  have hnonneg : 0 ≤ G * ((n : ℝ) ^ 2)⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left hexp hnonneg
  calc
    Sandpile.heatKernel 4 n x y ≤
        G * (n : ℝ) ^ (-(4 : ℝ) / 2) * Real.exp
          (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := hheat n hn x y
    _ = G * ((n : ℝ) ^ 2)⁻¹ * Real.exp
        (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := by rw [hp]
    _ ≤ G * ((n : ℝ) ^ 2)⁻¹ := by simpa [mul_assoc] using this
    _ = G / (n : ℝ) ^ 2 := by rw [div_eq_mul_inv]

end Sandpile.External

namespace Sandpile.External

theorem aux_bg7_survival_block (G g : ℝ) (hG : 0 < G) (hg : 0 < g)
    (hheat : ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site 4,
      Sandpile.heatKernel 4 n x y ≤
        G * (n : ℝ) ^ (-(4 : ℝ) / 2) *
          Real.exp (-g * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ))) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ r : ℕ, 2 ≤ r → ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
          (LatticeProb.boxFinset 0 r) (M * r ^ 2) x ≤ (1 : ℝ) / 2 := by
  let M : ℕ := ⌈162 * G + 1⌉₊
  have hMreal : 162 * G + 1 ≤ (M : ℝ) := by
    dsimp [M]
    exact Nat.le_ceil _
  have hM : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨M, hM, ?_⟩
  intro r hr x
  by_cases hx : x ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r
  · let n : ℕ := M * r ^ 2
    have hn : 1 ≤ n := by
      dsimp [n]
      have hr1 : 1 ≤ r := by omega
      have hr2 : 1 ≤ r ^ 2 := by
        simpa [pow_two] using Nat.mul_le_mul hr1 hr1
      exact hr2.trans (Nat.le_mul_of_pos_left (r ^ 2) (by omega))
    have hpoint : ∀ v : Sandpile.Site 4,
        Sandpile.heatKernel 4 n x v ≤ G / (n : ℝ) ^ 2 := by
      intro v
      exact aux_bg7_gaussian_upper_d4 G g hG hg hheat n hn x v
    have hsum :
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset (0 : Sandpile.Site 4) r) n x ≤
          ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r, G / (n : ℝ) ^ 2 := by
      rw [LatticeProb.Network.survival]
      apply Finset.sum_le_sum
      intro v hv
      calc
        LatticeProb.Graph.killedHeat (LatticeProb.lattice 4)
            (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set (Sandpile.Site 4)) n x v =
            Sandpile.killedKernel (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set (Sandpile.Site 4))
              n x v := (Sandpile.killedKernel_eq_graph _ _ _ _).symm
        _ ≤ Sandpile.heatKernel 4 n x v :=
          Sandpile.killedKernel_le_heatKernel _ _ _ _
        _ ≤ G / (n : ℝ) ^ 2 := hpoint v
    have hcard :
        (LatticeProb.boxFinset (0 : Sandpile.Site 4) r).card = (2 * r + 1) ^ 4 := by
      exact LatticeProb.card_boxFinset_zero r
    have hsum' :
        ∑ v ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r, G / (n : ℝ) ^ 2 =
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 * (G / (n : ℝ) ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      norm_num
    change LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset (0 : Sandpile.Site 4) r) n x ≤ (1 : ℝ) / 2
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    have hMR : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
    have hnum : ((2 * r + 1 : ℕ) : ℝ) ≤ 3 * (r : ℝ) := by
      push_cast
      nlinarith [show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast (show 1 ≤ r by omega)]
    have hden : 0 < (M : ℝ) ^ 2 * (r : ℝ) ^ 4 := by positivity
    have hbound :
        ((2 * r + 1 : ℕ) : ℝ) ^ 4 * (G / ((M * r ^ 2 : ℕ) : ℝ) ^ 2) ≤ (1 : ℝ) / 2 := by
      have hMlarge : 162 * G + 1 ≤ (M : ℝ) := hMreal
      have hMnonneg : 0 ≤ (M : ℝ) := by positivity
      have hmul : 0 ≤ ((M : ℝ) - (162 * G + 1)) *
          ((M : ℝ) + (162 * G + 1)) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hMbound : 162 * G ≤ (M : ℝ) ^ 2 := by
        nlinarith [hmul, sq_nonneg (162 * G + 1)]
      have hnum4 : ((2 * r + 1 : ℕ) : ℝ) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := by
        gcongr
      have hnum4G : 2 * ((2 * r + 1 : ℕ) : ℝ) ^ 4 * G ≤
          162 * G * (r : ℝ) ^ 4 := by
        have hh := mul_le_mul_of_nonneg_right hnum4 (by positivity : 0 ≤ 2 * G)
        nlinarith
      have hMboundr : 162 * G * (r : ℝ) ^ 4 ≤
          (M : ℝ) ^ 2 * (r : ℝ) ^ 4 := by
        exact mul_le_mul_of_nonneg_right hMbound (by positivity)
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnum4G.trans hMboundr
    exact hsum.trans (hsum'.le.trans (by simpa [n, Nat.cast_mul, Nat.cast_pow] using hbound))
  · rw [LatticeProb.Network.survival_of_not_mem hx]
    norm_num

end Sandpile.External

namespace Sandpile.External

theorem aux_ballgreen_clause7_holds : aux_ballgreen_clause7 := by
  obtain ⟨G, g, hG, hg, hheat⟩ := Sandpile.External.gaussianUpper 4 (by norm_num)
  obtain ⟨M, hM, hblock⟩ := aux_bg7_survival_block G g hG hg hheat
  let C₀ : ℝ := 32 * G * (M : ℝ)
  let C : ℝ := 81 * C₀ ^ 2 + C₀ + 1
  let c : ℝ := Real.log 2 / (100 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro r hr A hA
  let N : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊
  let B : ℕ := M * r ^ 2
  have hr1 : 1 ≤ r := by omega
  have hr2 : 1 ≤ r ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hr1 hr1
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN : r ^ 2 ≤ N := by
    dsimp [N]
    apply Nat.le_floor
    have hrpow : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by
      norm_num
    rw [hrpow]
    nlinarith [hA, sq_nonneg (r : ℝ)]
  have hB : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hB1 : 1 ≤ B := by omega
  have hblock0 : ∀ x : Sandpile.Site 4,
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) B x ≤ (1 : ℝ) / 2 := by
    intro x
    simpa [B] using hblock r hr x
  have hs : Summable (fun n : ℕ =>
      LatticeProb.Network.survival (LatticeProb.lattice 4)
        (LatticeProb.boxFinset 0 r) n 0) := aux_bg7_survival_summable r
  obtain ⟨hf, hhalf⟩ := aux_bg7_half_survival_tsum
    (LatticeProb.boxFinset 0 r) N 0 hs
  have hshift := aux_bg7_survival_shift_tsum
    (LatticeProb.boxFinset 0 r) B hB hblock0 (N / 2) 0
  have hq : ∀ u : Sandpile.Site 4,
      BallGreen.timeTail r A u ≤
        (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
          ((1 : ℝ) / 2) ^ ((N / 2) / B) := by
    intro u
    have hKsum : Summable (fun j : ℕ =>
        Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) := by
      exact (Sandpile.summable_killedKernel_transient (by norm_num)
        (BallGreen.box r) 0 u).comp_injective (add_right_injective N)
    have hright : Summable (fun j : ℕ =>
        (4 * G / (r : ℝ) ^ 4) *
          LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) :=
      hf.mul_left (4 * G / (r : ℝ) ^ 4)
    have htail : BallGreen.timeTail r A u ≤
        (4 * G / (r : ℝ) ^ 4) *
          (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := by
      rw [aux_bg7_timeTail_tsum]
      change (∑' j : ℕ, Sandpile.killedKernel (BallGreen.box r) (N + j) 0 u) ≤ _
      rw [← tsum_mul_left]
      apply hKsum.tsum_le_tsum
      · intro j
        apply aux_bg7_kernel_step r (N + j) u hr
          (le_trans hN (Nat.le_add_right N j)) G g hG hg hheat
      · exact hright
    calc
      BallGreen.timeTail r A u ≤
          (4 * G / (r : ℝ) ^ 4) *
            (∑' j : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
              (LatticeProb.boxFinset 0 r) ((N + j) / 2) 0) := htail
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * (∑' t : ℕ, LatticeProb.Network.survival (LatticeProb.lattice 4)
            (LatticeProb.boxFinset 0 r) (N / 2 + t) 0)) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ ≤ (4 * G / (r : ℝ) ^ 4) *
          (2 * ((B : ℝ) * 2 * ((1 : ℝ) / 2) ^ ((N / 2) / B))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hshift (by norm_num)) (by positivity)
      _ = _ := by ring
  have hQ : (A / (100 * (M : ℝ)) - 1) ≤
      (((N / 2) / B : ℕ) : ℝ) := by
    by_cases hsmall : A ≤ 100 * (M : ℝ)
    · have hh : A / (100 * (M : ℝ)) - 1 ≤ 0 := by
        have hden : (0 : ℝ) < 100 * (M : ℝ) := by positivity
        have hdiv : A / (100 * (M : ℝ)) ≤ 1 := by
          apply (div_le_iff₀ hden).2
          simpa using hsmall
        linarith
      have hqnonneg : 0 ≤ (((N / 2) / B : ℕ) : ℝ) := by positivity
      linarith
    · have hNfloor : A * (r : ℝ) ^ 2 < (N : ℝ) + 1 := by
        dsimp [N]
        exact Nat.lt_floor_add_one _
      have hLfloor : (N : ℝ) + 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) + 2 := by
        have hh : N + 1 ≤ 2 * (N / 2 + 1) := by omega
        exact_mod_cast hh
      have hQfloor : ((N / 2 : ℕ) : ℝ) <
          (B : ℝ) * ((((N / 2) / B : ℕ) : ℝ) + 1) := by
        have hBnat : 0 < B := by omega
        have hmod := Nat.mod_lt (N / 2) hBnat
        have hdiv := Nat.div_add_mod (N / 2) B
        have hlt : N / 2 < B * (N / 2 / B) + B := by omega
        have hh : N / 2 < B * (N / 2 / B + 1) := by
          simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hlt
        exact_mod_cast hh
      have hBr : (B : ℝ) = (M : ℝ) * (r : ℝ) ^ 2 := by
        simp [B, Nat.cast_mul, Nat.cast_pow]
      have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      have h1 : A * (r : ℝ) ^ 2 / 2 - 1 < ((N / 2 : ℕ) : ℝ) := by
        nlinarith [hNfloor, hLfloor]
      have h2 := (div_lt_div_iff₀ hBpos hBpos).2
        (mul_lt_mul_of_pos_right h1 hBpos)
      have h3 : ((N / 2 : ℕ) : ℝ) / (B : ℝ) - 1 <
          (((N / 2) / B : ℕ) : ℝ) := by
        have h3a : ((N / 2 : ℕ) : ℝ) / (B : ℝ) <
            (((N / 2) / B : ℕ) : ℝ) + 1 := by
          apply (div_lt_iff₀ hBpos).2
          nlinarith [hQfloor]
        linarith
      have hBge : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
      have h2' : A / (2 * (M : ℝ)) - 1 <
          ((N / 2 : ℕ) : ℝ) / (B : ℝ) := by
        have hInv : 1 / (B : ℝ) ≤ 1 := by
          exact (div_le_iff₀ hBpos).2 (by nlinarith [hBge])
        have hEq : (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) =
            A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
          rw [hBr]
          field_simp [ne_of_gt hMpos, ne_of_gt hrR]
        calc
          A / (2 * (M : ℝ)) - 1 ≤ A / (2 * (M : ℝ)) - 1 / (B : ℝ) := by
            linarith
          _ = (A * (r : ℝ) ^ 2 / 2 - 1) / (B : ℝ) := hEq.symm
          _ < _ := h2
      have hQlow : A / (2 * (M : ℝ)) - 2 <
          (((N / 2) / B : ℕ) : ℝ) := by
        linarith [h2', h3]
      have hAgt : 100 * (M : ℝ) < A := lt_of_not_ge hsmall
      have hscale : A / (100 * (M : ℝ)) - 1 <
          A / (2 * (M : ℝ)) - 2 := by
        field_simp
        nlinarith [hAgt, hMpos]
      exact (hscale.trans hQlow).le
  have hqexp : ((1 : ℝ) / 2) ^ ((N / 2) / B) ≤
      2 * Real.exp (-c * A) := by
    have hbase : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
    have hmono := Real.rpow_le_rpow_of_exponent_ge hbase (by norm_num) hQ
    have hpow : ((1 : ℝ) / 2) ^ ((N / 2) / B) =
        ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hpow]
    have heq : ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) =
        Real.exp (-c * A) := by
      rw [Real.rpow_def_of_pos hbase]
      dsimp [c]
      rw [show Real.log ((1 : ℝ) / 2) = -Real.log 2 by
        rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]]
      congr 1
      field_simp
    rw [← heq]
    calc
      ((1 : ℝ) / 2) ^ ((((N / 2) / B : ℕ) : ℝ)) ≤
          ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ)) - 1) := hmono
      _ = 2 * ((1 : ℝ) / 2) ^ (A / (100 * (M : ℝ))) := by
        have he : A / (100 * (M : ℝ)) - 1 =
            A / (100 * (M : ℝ)) + (-1 : ℝ) := by ring
        rw [he, Real.rpow_add hbase]
        ring
  have hpoint : ∀ u : Sandpile.Site 4,
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
    intro u
    have hnonneg := (aux_bg7_timeTail_factor r A u).1
    have hu := (hq u).trans (by
      calc
        _ ≤ (16 * G * (B : ℝ) / (r : ℝ) ^ 4) *
            (2 * Real.exp (-c * A)) :=
          mul_le_mul_of_nonneg_left hqexp (by positivity)
        _ = C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
          dsimp [C₀, B]
          norm_num [Nat.cast_mul, Nat.cast_pow]
          field_simp
          ring)
    calc
      |BallGreen.timeTail r A u| = BallGreen.timeTail r A u := abs_of_nonneg hnonneg
      _ ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hu
  have hbox : BallGreen.box r =
      (LatticeProb.boxFinset (0 : Sandpile.Site 4) r : Set _) := by
    ext v
    constructor
    · intro hv
      apply Sandpile.mem_boxFinset
      apply Finset.sup_le
      intro i _
      simpa [BallGreen.box, Pi.zero_apply, zero_sub, Int.natAbs_neg] using hv i
    · intro hv
      have hi := (LatticeProb.mem_boxFinset_iff.mp hv)
      intro i
      have hi0 : |v i| ≤ (r : ℤ) := by simpa [sub_zero] using hi i
      have hi1 : ((v i).natAbs : ℤ) ≤ (r : ℤ) := by
        rw [Int.natCast_natAbs]
        exact hi0
      exact_mod_cast hi1
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
        BallGreen.timeTail r A u = 0 := by
    intro u hu
    unfold BallGreen.timeTail
    rw [Sandpile.killedGreen_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      Sandpile.killedGreenTime_eq_zero_of_target_notMem _ (by rw [hbox]; exact hu),
      sub_zero]
  refine ⟨?_, ?_⟩
  · intro u
    have hC₀le : C₀ ≤ C := by
      dsimp [C]
      nlinarith [sq_nonneg C₀]
    calc
      |BallGreen.timeTail r A u| ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := hpoint u
      _ ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
        gcongr
  · have hsqzero : ∀ u : Sandpile.Site 4,
        u ∉ LatticeProb.boxFinset (0 : Sandpile.Site 4) r →
          BallGreen.timeTail r A u ^ 2 = 0 := by
      intro u hu
      rw [hzero u hu, zero_pow (by decide : 2 ≠ 0)]
    rw [tsum_eq_sum hsqzero]
    have hE : Real.exp (-c * A) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hAnonneg : (0 : ℝ) ≤ A := by linarith
      linarith [mul_nonneg hc.le hAnonneg]
    have hsum :
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
      calc
        (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
            BallGreen.timeTail r A u ^ 2) ≤
            ∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          apply Finset.sum_le_sum
          intro u hu
          have hp := hpoint u
          have hb : 0 ≤ C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) := by positivity
          have hsq : |BallGreen.timeTail r A u| ^ 2 =
              BallGreen.timeTail r A u ^ 2 := sq_abs _
          nlinarith [sq_nonneg (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A) -
            |BallGreen.timeTail r A u|), hsq, abs_nonneg (BallGreen.timeTail r A u)]
        _ = ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, LatticeProb.card_boxFinset_zero]
          norm_num
    calc
      (∑ u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r,
          BallGreen.timeTail r A u ^ 2) ≤
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
            (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 := hsum
      _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
        have hcard : ((2 * r + 1 : ℕ) : ℝ) ≤ 3 * (r : ℝ) := by
          push_cast
          nlinarith [show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr1]
        have hcard4 : ((2 * r + 1 : ℕ) : ℝ) ^ 4 ≤ (3 * (r : ℝ)) ^ 4 := by gcongr
        calc
          ((2 * r + 1 : ℕ) : ℝ) ^ 4 *
              (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 ≤
              (3 * (r : ℝ)) ^ 4 *
                (C₀ / (r : ℝ) ^ 2 * Real.exp (-c * A)) ^ 2 :=
            mul_le_mul_of_nonneg_right hcard4 (sq_nonneg _)
          _ = 81 * C₀ ^ 2 * Real.exp (-c * A) ^ 2 := by
            have hr4 : (r : ℝ) ^ 4 ≠ 0 := by positivity
            field_simp
            ring
          _ ≤ 81 * C₀ ^ 2 * Real.exp (-c * A) := by
            have hcoef : 0 ≤ 81 * C₀ ^ 2 := by positivity
            have hE2 : Real.exp (-c * A) ^ 2 ≤ Real.exp (-c * A) := by
              have hE0 : 0 ≤ Real.exp (-c * A) := (Real.exp_pos _).le
              calc
                Real.exp (-c * A) ^ 2 = Real.exp (-c * A) * Real.exp (-c * A) := by ring
                _ ≤ Real.exp (-c * A) * 1 :=
                  mul_le_mul_of_nonneg_left hE hE0
                _ = Real.exp (-c * A) := by ring
            exact mul_le_mul_of_nonneg_left hE2 hcoef
      _ ≤ C * Real.exp (-c * A) := by
        have hcoefC : 81 * C₀ ^ 2 ≤ C := by
          dsimp [C]
          nlinarith [hC₀]
        exact mul_le_mul_of_nonneg_right hcoefC (Real.exp_pos _).le

end Sandpile.External

namespace Sandpile.External

def aux_bg6_nrm1 (z : Sandpile.Site 4) : ℕ := ∑ i, (z i).natAbs

theorem aux_bg6_nrm1_eq_zero_iff {z : Sandpile.Site 4} :
    aux_bg6_nrm1 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff.mp h) i (Finset.mem_univ i)
    simpa [Int.natAbs_eq_zero] using hi
  · rintro rfl
    simp [aux_bg6_nrm1]

theorem aux_bg6_nrm1_add_le (z w : Sandpile.Site 4) :
    aux_bg6_nrm1 (z + w) ≤ aux_bg6_nrm1 z + aux_bg6_nrm1 w := by
  rw [aux_bg6_nrm1, aux_bg6_nrm1, aux_bg6_nrm1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le _ _

private theorem aux_bg6_dirVec_self (j : Fin 4) (s : Bool) :
    LatticeProb.dirVec ((j, s) : LatticeProb.Dir 4) j = if s then 1 else -1 := by
  simp [LatticeProb.dirVec]

private theorem aux_bg6_dirVec_of_ne {i j : Fin 4} (s : Bool) (h : i ≠ j) :
    LatticeProb.dirVec ((j, s) : LatticeProb.Dir 4) i = 0 := by
  simp [LatticeProb.dirVec, h]

open Classical in
noncomputable def aux_bg6_towardVec (p y : Sandpile.Site 4) : Sandpile.Site 4 :=
  if h : ∃ j : Fin 4, y j ≠ p j then
    LatticeProb.dirVec ((h.choose, decide (y h.choose < p h.choose)) : LatticeProb.Dir 4)
  else 0

theorem aux_bg6_towardVec_isDir {p y : Sandpile.Site 4} (hne : y ≠ p) :
    ∃ a : LatticeProb.Dir 4,
      aux_bg6_towardVec p y = LatticeProb.dirVec a := by
  classical
  have h : ∃ j : Fin 4, y j ≠ p j := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  exact ⟨(h.choose, decide (y h.choose < p h.choose)), by
    rw [aux_bg6_towardVec, dif_pos h]⟩

theorem aux_bg6_towardVec_unit {p y : Sandpile.Site 4} (hne : y ≠ p) :
    ∃ i : Fin 4, aux_bg6_towardVec p y = LatticeProb.unit i ∨
      aux_bg6_towardVec p y = -LatticeProb.unit i := by
  obtain ⟨⟨i, b⟩, hb⟩ := aux_bg6_towardVec_isDir hne
  cases b
  · exact ⟨i, Or.inr (hb.trans (LatticeProb.dirVec_eq_neg_unit i))⟩
  · exact ⟨i, Or.inl (hb.trans (LatticeProb.dirVec_eq_unit i))⟩

theorem aux_bg6_nrm1_toward {p y : Sandpile.Site 4} (hne : y ≠ p) :
    aux_bg6_nrm1 (p - (y + aux_bg6_towardVec p y)) + 1 = aux_bg6_nrm1 (p - y) := by
  classical
  have h : ∃ j : Fin 4, y j ≠ p j := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  set j := h.choose with hj
  have hjne : y j ≠ p j := h.choose_spec
  have hstep : aux_bg6_towardVec p y =
      LatticeProb.dirVec ((j, decide (y j < p j)) : LatticeProb.Dir 4) := by
    rw [aux_bg6_towardVec, dif_pos h]
  have hsplit : ∀ z : Sandpile.Site 4,
      aux_bg6_nrm1 z = (z j).natAbs + ∑ i ∈ Finset.univ.erase j, (z i).natAbs := by
    intro z
    rw [aux_bg6_nrm1, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hoff : ∀ i ∈ Finset.univ.erase j,
      ((p - (y + aux_bg6_towardVec p y)) i).natAbs = ((p - y) i).natAbs := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp only [Pi.sub_apply, Pi.add_apply, hstep,
      aux_bg6_dirVec_of_ne _ hij, add_zero]
  rw [hsplit (p - (y + aux_bg6_towardVec p y)), hsplit (p - y),
    Finset.sum_congr rfl hoff]
  have hjval : ((p - (y + aux_bg6_towardVec p y)) j).natAbs + 1 =
      ((p - y) j).natAbs := by
    have hv : (aux_bg6_towardVec p y) j = if y j < p j then (1 : ℤ) else -1 := by
      rw [hstep, aux_bg6_dirVec_self]
      by_cases hlt : y j < p j <;> simp [hlt]
    have hpa : (p - (y + aux_bg6_towardVec p y)) j =
        p j - (y j + (aux_bg6_towardVec p y) j) := rfl
    have hpb : (p - y) j = p j - y j := rfl
    rw [hpa, hpb, hv]
    by_cases hlt : y j < p j
    · rw [if_pos hlt]
      omega
    · rw [if_neg hlt]
      have hpy : p j < y j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hjne)
      omega
  omega

noncomputable def aux_bg6_toward (p y : Sandpile.Site 4) : Sandpile.Site 4 :=
  y + aux_bg6_towardVec p y

noncomputable def aux_bg6_gpath (p x : Sandpile.Site 4) (k : ℕ) : Sandpile.Site 4 :=
  (aux_bg6_toward p)^[k] x

@[simp] theorem aux_bg6_gpath_zero (p x : Sandpile.Site 4) :
    aux_bg6_gpath p x 0 = x := rfl

theorem aux_bg6_gpath_succ (p x : Sandpile.Site 4) (k : ℕ) :
    aux_bg6_gpath p x (k + 1) = aux_bg6_toward p (aux_bg6_gpath p x k) := by
  rw [aux_bg6_gpath, aux_bg6_gpath, Function.iterate_succ_apply']

theorem aux_bg6_gpath_nrm1 (p x : Sandpile.Site 4) : ∀ k : ℕ,
    k ≤ aux_bg6_nrm1 (p - x) →
      aux_bg6_nrm1 (p - aux_bg6_gpath p x k) = aux_bg6_nrm1 (p - x) - k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn' : n ≤ aux_bg6_nrm1 (p - x) := Nat.le_of_succ_le hn
    have hprev := ih hn'
    have hpos : 0 < aux_bg6_nrm1 (p - aux_bg6_gpath p x n) := by omega
    have hne : aux_bg6_gpath p x n ≠ p := by
      intro hcon
      rw [hcon, sub_self] at hpos
      rw [aux_bg6_nrm1_eq_zero_iff.mpr rfl] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hstep := aux_bg6_nrm1_toward
      (p := p) (y := aux_bg6_gpath p x n) hne
    rw [aux_bg6_gpath_succ, aux_bg6_toward]
    omega

theorem aux_bg6_gpath_ne {p x : Sandpile.Site 4} {k : ℕ}
    (hk : k < aux_bg6_nrm1 (p - x)) : aux_bg6_gpath p x k ≠ p := by
  intro hcon
  have h := aux_bg6_gpath_nrm1 p x k (le_of_lt hk)
  rw [hcon] at h
  simp only [sub_self] at h
  have hz : aux_bg6_nrm1 (0 : Sandpile.Site 4) = 0 :=
    aux_bg6_nrm1_eq_zero_iff.mpr rfl
  omega

theorem aux_bg6_gpath_end (p x : Sandpile.Site 4) :
    aux_bg6_gpath p x (aux_bg6_nrm1 (p - x)) = p := by
  have h := aux_bg6_gpath_nrm1 p x (aux_bg6_nrm1 (p - x)) le_rfl
  simp only [Nat.sub_self] at h
  have h2 : p - aux_bg6_gpath p x (aux_bg6_nrm1 (p - x)) = 0 :=
    aux_bg6_nrm1_eq_zero_iff.mp h
  exact (sub_eq_zero.mp h2).symm

theorem aux_bg6_gpath_step (w : Sandpile.Site 4) {k : ℕ}
    (hk : k < aux_bg6_nrm1 w) :
    ∃ i : Fin 4,
      aux_bg6_gpath w 0 (k + 1) = aux_bg6_gpath w 0 k + LatticeProb.unit i ∨
      aux_bg6_gpath w 0 (k + 1) = aux_bg6_gpath w 0 k - LatticeProb.unit i := by
  have hne := aux_bg6_gpath_ne (p := w) (x := (0 : Sandpile.Site 4))
    (by simpa using hk)
  obtain ⟨i, hi | hi⟩ := aux_bg6_towardVec_unit hne
  · exact ⟨i, Or.inl (by rw [aux_bg6_gpath_succ, aux_bg6_toward, hi])⟩
  · exact ⟨i, Or.inr (by rw [aux_bg6_gpath_succ, aux_bg6_toward, hi]; abel)⟩


theorem aux_bg6_latticeNorm_unit_le (i : Fin 4) :
    BallGreen.latticeNorm (LatticeProb.unit i) ≤ 1 := by
  have hsum : (∑ j : Fin 4, (((LatticeProb.unit i) j : ℤ) : ℝ) ^ 2) = 1 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [LatticeProb.unit]
    · intro j hj hji
      simp [LatticeProb.unit, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  unfold BallGreen.latticeNorm
  rw [hsum, Real.sqrt_one]

theorem aux_bg6_latticeNorm_neg (z : Sandpile.Site 4) :
    BallGreen.latticeNorm (-z) = BallGreen.latticeNorm z := by
  unfold BallGreen.latticeNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.neg_apply]
  push_cast
  ring

theorem aux_bg6_unit_diff_zero_of_notMem_ball (r : ℕ) (i : Fin 4)
    {u : Sandpile.Site 4}
    (hu : u ∉ LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)) :
    (Sandpile.killedGreen (BallGreen.box r) 0 (u + LatticeProb.unit i) -
      Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2 = 0 := by
  have hgt : 2 * (r : ℝ) + 2 < BallGreen.latticeNorm u := by
    by_contra hc
    exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
  have hzero_u : Sandpile.killedGreen (BallGreen.box r) 0 u = 0 := by
    by_contra hz
    have hmem : u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
      by_contra hnm
      exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
    have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
    linarith
  have hzero_v : Sandpile.killedGreen (BallGreen.box r) 0
      (u + LatticeProb.unit i) = 0 := by
    by_contra hz
    have hmem : u + LatticeProb.unit i ∈
        LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
      by_contra hnm
      exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
    have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
    have htri : BallGreen.latticeNorm u ≤
        BallGreen.latticeNorm (u + LatticeProb.unit i) +
          BallGreen.latticeNorm (-(LatticeProb.unit i)) := by
      have h := aux_bg6_latticeNorm_add_le (u + LatticeProb.unit i)
        (-(LatticeProb.unit i))
      simpa [add_assoc] using h
    have hunit : BallGreen.latticeNorm (LatticeProb.unit i) ≤ 1 :=
      aux_bg6_latticeNorm_unit_le i
    rw [aux_bg6_latticeNorm_neg] at htri
    linarith
  rw [hzero_v, hzero_u]
  ring

theorem aux_bg6_shell_sum_le
    (C₄ : ℝ) (h4 : ∀ r : ℕ, 2 ≤ r → ∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
      (∑' u : {u : Sandpile.Site 4 //
          (R : ℝ) ≤ BallGreen.latticeNorm u ∧
            BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
        (Sandpile.killedGreen (BallGreen.box r) 0
            ((u : Sandpile.Site 4) + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
        C₄ / (R : ℝ) ^ 2)
    (r R : ℕ) (hr : 2 ≤ r) (hR : 2 ≤ R) (i : Fin 4) :
    (∑ u ∈ LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2),
      Set.indicator {u : Sandpile.Site 4 |
        (R : ℝ) ≤ BallGreen.latticeNorm u ∧
          BallGreen.latticeNorm u ≤ 2 * (R : ℝ)}
        (fun u => (Sandpile.killedGreen (BallGreen.box r) 0
            (u + Sandpile.unit i) - Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
      C₄ / (R : ℝ) ^ 2 := by
  let S : Set (Sandpile.Site 4) :=
    {u | (R : ℝ) ≤ BallGreen.latticeNorm u ∧
      BallGreen.latticeNorm u ≤ 2 * (R : ℝ)}
  have h4' := h4 r hr R hR i
  change (∑' u : S,
      (Sandpile.killedGreen (BallGreen.box r) 0
          ((u : Sandpile.Site 4) + Sandpile.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
    C₄ / (R : ℝ) ^ 2 at h4'
  rw [tsum_subtype S (fun u : Sandpile.Site 4 =>
    (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
      Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2)] at h4'
  have hzero : ∀ u : Sandpile.Site 4,
      u ∉ LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2) →
      S.indicator (fun u : Sandpile.Site 4 =>
        (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u = 0 := by
    intro u hu
    by_cases hS : u ∈ S
    · rw [Set.indicator_of_mem hS]
      exact aux_bg6_unit_diff_zero_of_notMem_ball r i hu
    · rw [Set.indicator_of_notMem hS]
  rw [tsum_eq_sum hzero] at h4'
  exact h4'


theorem aux_bg6_unit_tail_le
    (C₄ : ℝ) (hC₄ : 0 < C₄)
    (h4 : ∀ r : ℕ, 2 ≤ r → ∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
      (∑' u : {u : Sandpile.Site 4 //
          (R : ℝ) ≤ BallGreen.latticeNorm u ∧
            BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
        (Sandpile.killedGreen (BallGreen.box r) 0
            ((u : Sandpile.Site 4) + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
        C₄ / (R : ℝ) ^ 2)
    (r T : ℕ) (hr : 2 ≤ r) (hT : 2 ≤ T) (i : Fin 4) :
    (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u}
        (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
      8 * C₄ / (T : ℝ) ^ 2 := by
  let B : ℕ := 2 * r + 2
  let k₀ : ℕ := Nat.log 2 T
  let ball : Finset (Sandpile.Site 4) :=
    LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)
  let shell (j : ℕ) : Set (Sandpile.Site 4) :=
    {u | ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ≤ BallGreen.latticeNorm u ∧
      BallGreen.latticeNorm u ≤ 2 * ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ)}
  let g : Sandpile.Site 4 → ℝ := fun u =>
    (Sandpile.killedGreen (BallGreen.box r) 0 (u + Sandpile.unit i) -
      Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2
  have hballzero : ∀ u : Sandpile.Site 4, u ∉ ball →
      Set.indicator {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} g u = 0 := by
    intro u hu
    by_cases htail : (T : ℝ) ≤ BallGreen.latticeNorm u
    · have hmem : u ∈ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := htail
      rw [Set.indicator_of_mem hmem]
      exact aux_bg6_unit_diff_zero_of_notMem_ball r i (by simpa [ball] using hu)
    · have hmem : u ∉ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := htail
      rw [Set.indicator_of_notMem hmem]
  have hBcast : (B : ℝ) = 2 * (r : ℝ) + 2 := by
    dsimp [B]
    norm_num
  have hpoint : ∀ u ∈ ball,
      Set.indicator {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} g u ≤
        ∑ j ∈ Finset.range (B + 1),
          Set.indicator (shell j) g u := by
    intro u hu
    have hnorm : BallGreen.latticeNorm u ≤ (B : ℝ) := by
      have h := (LatticeProb.mem_ballFinset_iff.mp (by simpa [ball] using hu))
      simpa [BallGreen.latticeNorm, LatticeProb.euclidNorm, hBcast] using h
    have hnormnn : (0 : ℝ) ≤ BallGreen.latticeNorm u := Real.sqrt_nonneg _
    have hnlt : ⌊BallGreen.latticeNorm u⌋₊ < B + 1 := by
      apply (Nat.floor_lt hnormnn).2
      exact lt_of_le_of_lt hnorm (by norm_num)
    have hnB : ⌊BallGreen.latticeNorm u⌋₊ ≤ B := Nat.le_of_lt_succ hnlt
    by_cases htail : (T : ℝ) ≤ BallGreen.latticeNorm u
    · have hTn : T ≤ ⌊BallGreen.latticeNorm u⌋₊ :=
        Nat.le_floor (by exact_mod_cast htail)
      let n : ℕ := ⌊BallGreen.latticeNorm u⌋₊
      let k : ℕ := Nat.log 2 n
      have hnT : T ≤ n := by simpa [n] using hTn
      have hnne : n ≠ 0 := by omega
      have hk₀k : k₀ ≤ k := by
        dsimp [k₀, k]
        exact Nat.log_mono_right hnT
      let j : ℕ := k - k₀
      have hjB : j < B + 1 := by
        have hjk : j ≤ k := Nat.sub_le _ _
        have hkn : k ≤ n := by
          dsimp [k]
          exact Nat.log_le_self 2 n
        dsimp [j, n] at *
        omega
      have hpowlow : 2 ^ k ≤ n := Nat.pow_log_le_self 2 hnne
      have hpowup : n < 2 ^ (k + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) n
      have hfloorlow : (n : ℝ) ≤ BallGreen.latticeNorm u := by
        dsimp [n]
        exact Nat.floor_le hnormnn
      have hfloorup : BallGreen.latticeNorm u < (n : ℝ) + 1 := by
        dsimp [n]
        exact Nat.lt_floor_add_one _
      have hR : 2 ^ k₀ * 2 ^ j = 2 ^ k := by
        calc
          2 ^ k₀ * 2 ^ j = 2 ^ (k₀ + j) := (Nat.pow_add 2 k₀ j).symm
          _ = 2 ^ k := by rw [show k₀ + j = k by omega]
      have hlow : ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ≤ BallGreen.latticeNorm u := by
        rw [hR]
        have hpowlow' : ((2 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpowlow
        exact hpowlow'.trans hfloorlow
      have hnup : n + 1 ≤ 2 ^ (k + 1) := (Nat.lt_iff_add_one_le).mp hpowup
      have hupp : BallGreen.latticeNorm u ≤
          2 * ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) := by
        rw [hR]
        have hcast : ((2 ^ (k + 1) : ℕ) : ℝ) =
            2 * ((2 ^ k : ℕ) : ℝ) := by
          rw [pow_succ]
          push_cast
          ring
        rw [← hcast]
        have hupp' : BallGreen.latticeNorm u <
            ((2 ^ (k + 1) : ℕ) : ℝ) :=
          lt_of_lt_of_le hfloorup (by exact_mod_cast hnup)
        exact hupp'.le
      have hmem : u ∈ shell j := by
        exact ⟨hlow, hupp⟩
      have hnonneg : ∀ l ∈ Finset.range (B + 1), 0 ≤
          Set.indicator (shell l) g u := by
        intro l hl
        by_cases hlm : u ∈ shell l
        · rw [Set.indicator_of_mem hlm]
          dsimp [g]
          positivity
        · rw [Set.indicator_of_notMem hlm]
      have hsingle := Finset.single_le_sum hnonneg (Finset.mem_range.mpr hjB)
      have hchosen : Set.indicator (shell j) g u = g u :=
        Set.indicator_of_mem hmem g
      rw [hchosen] at hsingle
      have htailmem : u ∈ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := htail
      rw [Set.indicator_of_mem htailmem]
      exact hsingle
    · have htailmem : u ∉ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := htail
      rw [Set.indicator_of_notMem htailmem]
      exact Finset.sum_nonneg (by
        intro j hj
        by_cases hmem : u ∈ shell j
        · rw [Set.indicator_of_mem hmem]
          dsimp [g]
          positivity
        · rw [Set.indicator_of_notMem hmem])
  have hsum_point :
      (∑ u ∈ ball, Set.indicator
        {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} g u) ≤
      ∑ u ∈ ball, ∑ j ∈ Finset.range (B + 1),
        Set.indicator (shell j) g u :=
    Finset.sum_le_sum hpoint
  rw [Finset.sum_comm] at hsum_point
  have hsum_shell :
      (∑ j ∈ Finset.range (B + 1), ∑ u ∈ ball,
        Set.indicator (shell j) g u) ≤
      ∑ j ∈ Finset.range (B + 1),
        C₄ / ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    dsimp [ball, shell, g] at ⊢
    exact aux_bg6_shell_sum_le C₄ h4 r (2 ^ k₀ * 2 ^ j) hr
      (by
        have hk₀pos : 0 < k₀ := by
          dsimp [k₀]
          exact Nat.log_pos (by norm_num) hT
        have hpow : 2 ^ 1 ≤ 2 ^ k₀ :=
          Nat.pow_le_pow_right (by norm_num) hk₀pos
        have : 2 ≤ 2 ^ k₀ := by simpa using hpow
        exact le_trans this (Nat.le_mul_of_pos_right _ (by positivity))) i
  have hk₀low : (T : ℝ) / 2 ≤ (2 ^ k₀ : ℝ) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T
    have h' : (T : ℝ) < ((2 ^ (k₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have hpow : ((2 ^ (k₀ + 1) : ℕ) : ℝ) = 2 * (2 ^ k₀ : ℝ) := by
      rw [pow_succ]
      push_cast
      ring
    rw [hpow] at h'
    linarith
  have hterm : ∀ j ∈ Finset.range (B + 1),
      C₄ / ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ^ 2 ≤
        4 * C₄ / (T : ℝ) ^ 2 * ((1 : ℝ) / 4) ^ j := by
    intro j hj
    have hRlow : (T : ℝ) / 2 * (2 ^ j : ℝ) ≤
        ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) := by
      have hcastR : ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) =
          (2 ^ k₀ : ℝ) * (2 ^ j : ℝ) := by norm_num
      rw [hcastR]
      exact mul_le_mul_of_nonneg_right hk₀low (by positivity)
    have hden : ((T : ℝ) / 2 * (2 ^ j : ℝ)) ^ 2 ≤
        ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hRlow 2
    calc
      C₄ / ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ^ 2 ≤
          C₄ / ((T : ℝ) / 2 * (2 ^ j : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_left hC₄.le (by positivity) hden
      _ = 4 * C₄ / (T : ℝ) ^ 2 * ((1 : ℝ) / 4) ^ j := by
        have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
        have hpow4 : ((1 : ℝ) / 4) ^ j * (2 : ℝ) ^ (j * 2) = 1 := by
          calc
            ((1 : ℝ) / 4) ^ j * (2 : ℝ) ^ (j * 2) =
                ((1 : ℝ) / 4) ^ j * ((2 : ℝ) ^ 2) ^ j := by
                  congr 1
                  rw [← pow_mul]
                  congr 1
                  omega
            _ = (((1 : ℝ) / 4) * (2 : ℝ) ^ 2) ^ j := by rw [mul_pow]
            _ = 1 := by norm_num
        have hpow4' : (2 : ℝ) ^ (j * 2) * 4 * ((1 : ℝ) / 4) ^ j = 4 := by
          calc
            (2 : ℝ) ^ (j * 2) * 4 * ((1 : ℝ) / 4) ^ j =
                4 * (((1 : ℝ) / 4) ^ j * (2 : ℝ) ^ (j * 2)) := by ring
            _ = 4 := by rw [hpow4]; ring
        field_simp [hTne]
        rw [← pow_mul]
        calc
          (2 : ℝ) ^ 2 = 4 := by norm_num
          _ = (2 : ℝ) ^ (j * 2) * 4 * ((1 : ℝ) / 4) ^ j := by
            rw [hpow4']
          _ = (2 : ℝ) ^ (j * 2) * 4 * ((1 : ℝ) / 4) ^ j := by ring
  have hgeom : ∑ j ∈ Finset.range (B + 1), ((1 : ℝ) / 4) ^ j ≤ 2 := by
    have hsum_eq : (∑ j ∈ Finset.range (B + 1), ((1 : ℝ) / 4) ^ j) =
        (4 / 3 : ℝ) * (1 - ((1 : ℝ) / 4) ^ (B + 1)) := by
      rw [geom_sum_eq (by norm_num)]
      field_simp
      ring
    rw [hsum_eq]
    have hp : 0 ≤ ((1 : ℝ) / 4) ^ (B + 1) := by positivity
    nlinarith
  have hsum_geom :
      (∑ j ∈ Finset.range (B + 1),
        C₄ / ((2 ^ k₀ * 2 ^ j : ℕ) : ℝ) ^ 2) ≤
      8 * C₄ / (T : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (B + 1),
          4 * C₄ / (T : ℝ) ^ 2 * ((1 : ℝ) / 4) ^ j :=
        Finset.sum_le_sum hterm
      _ = 4 * C₄ / (T : ℝ) ^ 2 *
          (∑ j ∈ Finset.range (B + 1), ((1 : ℝ) / 4) ^ j) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * C₄ / (T : ℝ) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 8 * C₄ / (T : ℝ) ^ 2 := by ring
  rw [tsum_eq_sum hballzero]
  exact hsum_point.trans (hsum_shell.trans hsum_geom)


theorem aux_bg6_nrm1_le_two_norm (z : Sandpile.Site 4) :
    (aux_bg6_nrm1 z : ℝ) ≤ 2 * BallGreen.latticeNorm z := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 4))
    (fun i => |((z i : ℤ) : ℝ)|) (fun _ => (1 : ℝ))
  have hcs' : (∑ i : Fin 4, |((z i : ℤ) : ℝ)|) ≤
      Real.sqrt (∑ i : Fin 4, |((z i : ℤ) : ℝ)| ^ 2) * 2 := by
    norm_num at hcs ⊢
    exact hcs
  have hsq : (∑ i : Fin 4, |((z i : ℤ) : ℝ)| ^ 2) =
      ∑ i : Fin 4, (((z i : ℤ) : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [sq_abs]
  have hnorm : (∑ i : Fin 4, (((z i : ℤ) : ℝ) ^ 2)) =
      (BallGreen.latticeNorm z) ^ 2 := by
    unfold BallGreen.latticeNorm
    rw [Real.sq_sqrt (by positivity)]
  have hsum : (aux_bg6_nrm1 z : ℝ) =
      ∑ i : Fin 4, |((z i : ℤ) : ℝ)| := by
    unfold aux_bg6_nrm1
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Nat.cast_natAbs, Int.cast_abs]
  have hnn : (0 : ℝ) ≤ BallGreen.latticeNorm z := Real.sqrt_nonneg _
  rw [hsq, hnorm, Real.sqrt_sq hnn] at hcs'
  rw [hsum]
  simpa [mul_comm] using hcs'

theorem aux_bg6_gpath_norm_le (w : Sandpile.Site 4) : ∀ k,
    k ≤ aux_bg6_nrm1 w →
      BallGreen.latticeNorm (aux_bg6_gpath w 0 k) ≤ (k : ℝ) := by
  intro k
  induction k with
  | zero => intro _; simp [BallGreen.latticeNorm]
  | succ k ih =>
    intro hk
    have hk' : k < aux_bg6_nrm1 (w - (0 : Sandpile.Site 4)) := by
      simpa using (Nat.lt_of_succ_le hk)
    have hne := aux_bg6_gpath_ne (p := w) (x := (0 : Sandpile.Site 4)) hk'
    obtain ⟨i, hi | hi⟩ := aux_bg6_towardVec_unit hne
    · rw [aux_bg6_gpath_succ, aux_bg6_toward, hi]
      have htri := aux_bg6_latticeNorm_add_le
        (aux_bg6_gpath w 0 k) (LatticeProb.unit i)
      have hu := aux_bg6_latticeNorm_unit_le i
      have hprev := ih (by omega)
      norm_num [Nat.cast_add, Nat.cast_one] at *
      linarith
    · rw [aux_bg6_gpath_succ, aux_bg6_toward, hi]
      have htri := aux_bg6_latticeNorm_add_le
        (aux_bg6_gpath w 0 k) (-(LatticeProb.unit i))
      have hu := aux_bg6_latticeNorm_unit_le i
      rw [aux_bg6_latticeNorm_neg] at htri
      have hprev := ih (by omega)
      norm_num [Nat.cast_add, Nat.cast_one] at *
      linarith

theorem aux_bg6_toward_interval {p y : Sandpile.Site 4}
    (hy : ∀ i : Fin 4, min (0 : ℤ) (p i) ≤ y i ∧ y i ≤ max 0 (p i))
    (hne : y ≠ p) :
    ∀ i : Fin 4,
      min (0 : ℤ) (p i) ≤ aux_bg6_toward p y i ∧
        aux_bg6_toward p y i ≤ max 0 (p i) := by
  classical
  have h : ∃ j : Fin 4, y j ≠ p j := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  let j := h.choose
  have hj : y j ≠ p j := h.choose_spec
  have hstep : aux_bg6_towardVec p y =
      LatticeProb.dirVec ((j, decide (y j < p j)) : LatticeProb.Dir 4) := by
    rw [aux_bg6_towardVec, dif_pos h]
  have hv : (aux_bg6_towardVec p y) j = if y j < p j then (1 : ℤ) else -1 := by
    rw [hstep, aux_bg6_dirVec_self]
    by_cases hlt : y j < p j <;> simp [hlt]
  intro i
  by_cases hij : i = j
  · subst i
    rw [aux_bg6_toward, Pi.add_apply, hv]
    by_cases hlt : y j < p j
    · rw [if_pos hlt]
      have hlow := (hy j).1
      have hupp := (hy j).2
      constructor <;> omega
    · rw [if_neg hlt]
      have hpy : p j < y j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hj)
      have hlow := (hy j).1
      have hupp := (hy j).2
      constructor <;> omega
  · rw [aux_bg6_toward, Pi.add_apply, hstep,
    aux_bg6_dirVec_of_ne _ hij, add_zero]
    exact hy i

theorem aux_bg6_gpath_interval (w : Sandpile.Site 4) : ∀ k,
    k ≤ aux_bg6_nrm1 w →
      ∀ i : Fin 4,
        min (0 : ℤ) (w i) ≤ aux_bg6_gpath w 0 k i ∧
          aux_bg6_gpath w 0 k i ≤ max 0 (w i) := by
  intro k
  induction k with
  | zero =>
      intro _ i
      simp only [aux_bg6_gpath_zero, Pi.zero_apply]
      exact ⟨min_le_left _ _, le_max_left _ _⟩
  | succ k ih =>
      intro hk i
      have hk' : k < aux_bg6_nrm1 (w - (0 : Sandpile.Site 4)) := by
        simpa using (Nat.lt_of_succ_le hk)
      have hne := aux_bg6_gpath_ne (p := w) (x := (0 : Sandpile.Site 4)) hk'
      have hprev := ih (Nat.le_of_succ_le hk)
      have hstep := aux_bg6_toward_interval hprev hne i
      simpa [aux_bg6_gpath_succ] using hstep

theorem aux_bg6_gpath_norm_le_final (w : Sandpile.Site 4) (k : ℕ)
    (hk : k ≤ aux_bg6_nrm1 w) :
    BallGreen.latticeNorm (aux_bg6_gpath w 0 k) ≤ BallGreen.latticeNorm w := by
  have hinter := aux_bg6_gpath_interval w k hk
  have habs : ∀ i : Fin 4,
      |((aux_bg6_gpath w 0 k i : ℤ) : ℝ)| ≤ |((w i : ℤ) : ℝ)| := by
    intro i
    by_cases hw : 0 ≤ w i
    · have hlow : (0 : ℤ) ≤ aux_bg6_gpath w 0 k i := by
        simpa [min_eq_left hw] using (hinter i).1
      have hupp : aux_bg6_gpath w 0 k i ≤ w i := by
        simpa [max_eq_right hw] using (hinter i).2
      rw [abs_of_nonneg (by exact_mod_cast hlow),
        abs_of_nonneg (by exact_mod_cast hw)]
      exact_mod_cast hupp
    · have hw' : w i ≤ 0 := le_of_not_ge hw
      have hlow : w i ≤ aux_bg6_gpath w 0 k i := by
        simpa [min_eq_right hw'] using (hinter i).1
      have hupp : aux_bg6_gpath w 0 k i ≤ 0 := by
        simpa [max_eq_left hw'] using (hinter i).2
      rw [abs_of_nonpos (by exact_mod_cast hupp),
        abs_of_nonpos (by exact_mod_cast hw')]
      norm_num
      exact_mod_cast (show w i ≤ aux_bg6_gpath w 0 k i from hlow)
  have hsum : (∑ i : Fin 4,
      (((aux_bg6_gpath w 0 k i : ℤ) : ℝ) ^ 2)) ≤
      ∑ i : Fin 4, (((w i : ℤ) : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro i hi
    have h := habs i
    have hsqabs :
        |((aux_bg6_gpath w 0 k i : ℤ) : ℝ)| ^ 2 ≤
          |((w i : ℤ) : ℝ)| ^ 2 := by
      nlinarith [abs_nonneg (((aux_bg6_gpath w 0 k i : ℤ) : ℝ)),
        abs_nonneg (((w i : ℤ) : ℝ))]
    simpa only [sq_abs] using hsqabs
  unfold BallGreen.latticeNorm
  exact Real.sqrt_le_sqrt hsum

theorem aux_bg6_unit_diff_neg_zero_of_notMem_ball (r : ℕ) (i : Fin 4)
    {u : Sandpile.Site 4}
    (hu : u ∉ LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)) :
    (Sandpile.killedGreen (BallGreen.box r) 0 (u - LatticeProb.unit i) -
      Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2 = 0 := by
  have hgt : 2 * (r : ℝ) + 2 < BallGreen.latticeNorm u := by
    by_contra hc
    exact hu (LatticeProb.mem_ballFinset_iff.mpr (not_lt.mp hc))
  have hzero_u : Sandpile.killedGreen (BallGreen.box r) 0 u = 0 := by
    by_contra hz
    have hmem : u ∈ LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
      by_contra hnm
      exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
    have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
    linarith
  have hzero_v : Sandpile.killedGreen (BallGreen.box r) 0
      (u - LatticeProb.unit i) = 0 := by
    by_contra hz
    have hmem : u - LatticeProb.unit i ∈
        LatticeProb.boxFinset (0 : Sandpile.Site 4) r := by
      by_contra hnm
      exact hz (Sandpile.killedGreen_box_eq_zero_of_notMem_boxFinset r hnm)
    have hb := aux_bg6_latticeNorm_le_of_mem_boxFinset hmem
    have htri : BallGreen.latticeNorm u ≤
        BallGreen.latticeNorm (u - LatticeProb.unit i) +
          BallGreen.latticeNorm (LatticeProb.unit i) := by
      have h := aux_bg6_latticeNorm_add_le (u - LatticeProb.unit i)
        (LatticeProb.unit i)
      simpa [sub_add_cancel] using h
    have hunit := aux_bg6_latticeNorm_unit_le i
    linarith
  rw [hzero_v, hzero_u]
  ring

theorem aux_bg6_unit_tail_neg_le
    (C₄ : ℝ) (hC₄ : 0 < C₄)
    (h4 : ∀ r : ℕ, 2 ≤ r → ∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
      (∑' u : {u : Sandpile.Site 4 //
          (R : ℝ) ≤ BallGreen.latticeNorm u ∧
            BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
        (Sandpile.killedGreen (BallGreen.box r) 0
            ((u : Sandpile.Site 4) + Sandpile.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 (u : Sandpile.Site 4)) ^ 2) ≤
        C₄ / (R : ℝ) ^ 2)
    (r T : ℕ) (hr : 2 ≤ r) (hT : 4 ≤ T) (i : Fin 4) :
    (∑' u : Sandpile.Site 4,
      Set.indicator {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u}
        (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 (u - LatticeProb.unit i) -
          Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u) ≤
      32 * C₄ / (T : ℝ) ^ 2 := by
  let ball : Finset (Sandpile.Site 4) :=
    LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)
  let neg : Sandpile.Site 4 → ℝ := fun u =>
    Set.indicator {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u}
      (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 (u - LatticeProb.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u
  let pos : Sandpile.Site 4 → ℝ := fun u =>
    Set.indicator {u : Sandpile.Site 4 | ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u}
      (fun u => (Sandpile.killedGreen (BallGreen.box r) 0 (u + LatticeProb.unit i) -
        Sandpile.killedGreen (BallGreen.box r) 0 u) ^ 2) u
  have hneg_zero : ∀ u : Sandpile.Site 4, u ∉ ball → neg u = 0 := by
    intro u hu
    by_cases ht : (T : ℝ) ≤ BallGreen.latticeNorm u
    · have hmem : u ∈ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [neg]
      rw [Set.indicator_of_mem hmem]
      exact aux_bg6_unit_diff_neg_zero_of_notMem_ball r i (by simpa [ball] using hu)
    · have hmem : u ∉ {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [neg]
      rw [Set.indicator_of_notMem hmem]
  have hpos_zero : ∀ u : Sandpile.Site 4, u ∉ ball → pos u = 0 := by
    intro u hu
    by_cases ht : ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u
    · have hmem : u ∈ {u : Sandpile.Site 4 |
          ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [pos]
      rw [Set.indicator_of_mem hmem]
      exact aux_bg6_unit_diff_zero_of_notMem_ball r i (by simpa [ball] using hu)
    · have hmem : u ∉ {u : Sandpile.Site 4 |
          ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [pos]
      rw [Set.indicator_of_notMem hmem]
  have hneg_sum : Summable neg := summable_of_ne_finset_zero
    (s := ball) hneg_zero
  have hpos_sum : Summable pos := summable_of_ne_finset_zero
    (s := ball) hpos_zero
  have hshift_sum : Summable (fun z => neg (z + LatticeProb.unit i)) := by
    have h := ((Equiv.addRight (LatticeProb.unit i)).summable_iff (f := neg)).mpr hneg_sum
    simpa [Function.comp_def] using h
  have hpoint : ∀ z : Sandpile.Site 4,
      neg (z + LatticeProb.unit i) ≤ pos z := by
    intro z
    by_cases ht : (T : ℝ) ≤ BallGreen.latticeNorm (z + LatticeProb.unit i)
    · have hmem : z + LatticeProb.unit i ∈
          {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [neg]
      rw [Set.indicator_of_mem hmem]
      have htri := aux_bg6_latticeNorm_add_le z (LatticeProb.unit i)
      have hu := aux_bg6_latticeNorm_unit_le i
      have hsub : ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm z := by
        have hT' : ((T : ℕ) : ℝ) - 1 = ((T - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (R := ℝ) (by omega)]
          norm_num
        rw [← hT']
        linarith
      have hq : z ∈ {u : Sandpile.Site 4 |
          ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u} := hsub
      dsimp only [pos]
      rw [Set.indicator_of_mem hq]
      ring_nf
      exact le_rfl
    · have hmem : z + LatticeProb.unit i ∉
          {u : Sandpile.Site 4 | (T : ℝ) ≤ BallGreen.latticeNorm u} := ht
      dsimp only [neg]
      rw [Set.indicator_of_notMem hmem]
      change 0 ≤ pos z
      by_cases hq : z ∈ {u : Sandpile.Site 4 |
          ((T - 1 : ℕ) : ℝ) ≤ BallGreen.latticeNorm u}
      · dsimp only [pos]
        rw [Set.indicator_of_mem hq]
        exact sq_nonneg _
      · dsimp only [pos]
        rw [Set.indicator_of_notMem hq]
  have hle := Summable.tsum_le_tsum hpoint hshift_sum hpos_sum
  have hreindex : (∑' u : Sandpile.Site 4, neg u) =
      ∑' z : Sandpile.Site 4, neg (z + LatticeProb.unit i) := by
    symm
    exact (Equiv.addRight (LatticeProb.unit i)).tsum_eq neg
  have htail := aux_bg6_unit_tail_le C₄ hC₄ h4 r (T - 1) hr (by omega) i
  have hposbound : (∑' z : Sandpile.Site 4, pos z) ≤
      8 * C₄ / ((T - 1 : ℕ) : ℝ) ^ 2 := by
    simpa [pos] using htail
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hTmposNat : 0 < T - 1 := by omega
  have hTmpos : (0 : ℝ) < ((T - 1 : ℕ) : ℝ) := by
    exact_mod_cast hTmposNat
  calc
    ∑' u : Sandpile.Site 4, neg u = ∑' z : Sandpile.Site 4, neg (z + LatticeProb.unit i) := hreindex
    _ ≤ ∑' z : Sandpile.Site 4, pos z := hle
    _ ≤ 8 * C₄ / ((T - 1 : ℕ) : ℝ) ^ 2 := hposbound
    _ ≤ 32 * C₄ / (T : ℝ) ^ 2 := by
      have hratio : (T : ℝ) ≤ 2 * ((T - 1 : ℕ) : ℝ) := by
        have hTreal : (4 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
        have hcast : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
          rw [Nat.cast_sub (R := ℝ) (by omega)]
          norm_num
        rw [hcast]
        nlinarith
      have hden : ((T : ℝ) ^ 2) ≤ 4 * ((T - 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((T : ℝ) - 2 * ((T - 1 : ℕ) : ℝ))]
      have hdenpos : 0 < ((T - 1 : ℕ) : ℝ) ^ 2 := sq_pos_of_pos hTmpos
      have hTdenpos : 0 < (T : ℝ) ^ 2 := sq_pos_of_pos hTpos
      apply (div_le_div_iff₀ hdenpos hTdenpos).2
      nlinarith [mul_le_mul_of_nonneg_left hden (le_of_lt hC₄)]

theorem aux_bg6_far_residual_holds : aux_bg6_far_residual := by
  classical
  obtain ⟨C₄, hC₄, h4⟩ := aux_ballgreen_clause4_holds
  refine ⟨1024 * C₄, by positivity, ?_⟩
  intro r hr L hL M hM w hw
  let f : Sandpile.Site 4 → ℝ := fun u =>
    Sandpile.killedGreen (BallGreen.box r) 0 u
  let far : Set (Sandpile.Site 4) :=
    {u | (2 + M) * (L : ℝ) ≤ BallGreen.latticeNorm u}
  let n : ℕ := aux_bg6_nrm1 w
  let p : ℕ → Sandpile.Site 4 := fun k => aux_bg6_gpath w 0 k
  let R : ℕ := 2 * L
  let Apos : Fin 4 → Sandpile.Site 4 → ℝ := fun i z =>
    Set.indicator {z : Sandpile.Site 4 |
        (R : ℝ) ≤ BallGreen.latticeNorm z}
      (fun z => (f (z + LatticeProb.unit i) - f z) ^ 2) z
  let Aneg : Fin 4 → Sandpile.Site 4 → ℝ := fun i z =>
    Set.indicator {z : Sandpile.Site 4 |
        (R : ℝ) ≤ BallGreen.latticeNorm z}
      (fun z => (f (z - LatticeProb.unit i) - f z) ^ 2) z
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (show 0 < L by omega)
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := hLpos.le
  have hMnn : (0 : ℝ) ≤ M := by linarith
  have hRge : 4 ≤ R := by
    dsimp [R]
    omega
  have hRcast : (R : ℝ) = 2 * (L : ℝ) := by
    dsimp [R]
    norm_num
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    rw [hRcast]
    positivity
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := hRpos.le
  have htail_pos : ∀ i : Fin 4, (∑' z : Sandpile.Site 4, Apos i z) ≤
      8 * C₄ / (R : ℝ) ^ 2 := by
    intro i
    have h := aux_bg6_unit_tail_le C₄ hC₄ h4 r R hr (by omega) i
    simpa [Apos, f] using h
  have htail_neg : ∀ i : Fin 4, (∑' z : Sandpile.Site 4, Aneg i z) ≤
      32 * C₄ / (R : ℝ) ^ 2 := by
    intro i
    have h := aux_bg6_unit_tail_neg_le C₄ hC₄ h4 r R hr hRge i
    simpa [Aneg, f] using h
  have hApos_sum : ∀ i : Fin 4, Summable (Apos i) := by
    intro i
    let ball : Finset (Sandpile.Site 4) :=
      LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)
    apply summable_of_ne_finset_zero (s := ball)
    intro z hz
    by_cases hmem : z ∈ {z : Sandpile.Site 4 | (R : ℝ) ≤ BallGreen.latticeNorm z}
    · dsimp only [Apos]
      rw [Set.indicator_of_mem hmem]
      exact aux_bg6_unit_diff_zero_of_notMem_ball r i
        (by simpa [ball] using hz)
    · dsimp only [Apos]
      rw [Set.indicator_of_notMem hmem]
  have hAneg_sum : ∀ i : Fin 4, Summable (Aneg i) := by
    intro i
    let ball : Finset (Sandpile.Site 4) :=
      LatticeProb.ballFinset 4 (2 * (r : ℝ) + 2)
    apply summable_of_ne_finset_zero (s := ball)
    intro z hz
    by_cases hmem : z ∈ {z : Sandpile.Site 4 | (R : ℝ) ≤ BallGreen.latticeNorm z}
    · dsimp only [Aneg]
      rw [Set.indicator_of_mem hmem]
      exact aux_bg6_unit_diff_neg_zero_of_notMem_ball r i
        (by simpa [ball] using hz)
    · dsimp only [Aneg]
      rw [Set.indicator_of_notMem hmem]
  have hApos_nonneg : ∀ i z, 0 ≤ Apos i z := by
    intro i z
    by_cases hmem : z ∈ {z : Sandpile.Site 4 | (R : ℝ) ≤ BallGreen.latticeNorm z}
    · dsimp only [Apos]
      rw [Set.indicator_of_mem hmem]
      positivity
    · dsimp only [Apos]
      rw [Set.indicator_of_notMem hmem]
  have hAneg_nonneg : ∀ i z, 0 ≤ Aneg i z := by
    intro i z
    by_cases hmem : z ∈ {z : Sandpile.Site 4 | (R : ℝ) ≤ BallGreen.latticeNorm z}
    · dsimp only [Aneg]
      rw [Set.indicator_of_mem hmem]
      positivity
    · dsimp only [Aneg]
      rw [Set.indicator_of_notMem hmem]
  have hdiv : C₄ / (R : ℝ) ^ 2 ≤ C₄ / (L : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hRpos) (sq_pos_of_pos hLpos)).2
    have hsq : (L : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
      nlinarith [hRcast, sq_nonneg ((R : ℝ) - (L : ℝ))]
    exact mul_le_mul_of_nonneg_left hsq hC₄.le
  have htail_pos' : ∀ i : Fin 4, (∑' z : Sandpile.Site 4, Apos i z) ≤
      32 * C₄ / (L : ℝ) ^ 2 := by
    intro i
    calc
      _ ≤ 8 * C₄ / (R : ℝ) ^ 2 := htail_pos i
      _ = 8 * (C₄ / (R : ℝ) ^ 2) := by ring
      _ ≤ 8 * (C₄ / (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 8 * C₄ / (L : ℝ) ^ 2 := by ring
      _ ≤ 32 * C₄ / (L : ℝ) ^ 2 := by
        have hnon : 0 ≤ C₄ / (L : ℝ) ^ 2 := by positivity
        calc
          8 * C₄ / (L : ℝ) ^ 2 = 8 * (C₄ / (L : ℝ) ^ 2) := by ring
          _ ≤ 32 * (C₄ / (L : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_right (show (8 : ℝ) ≤ 32 by norm_num) hnon
          _ = 32 * C₄ / (L : ℝ) ^ 2 := by ring
  have htail_neg' : ∀ i : Fin 4, (∑' z : Sandpile.Site 4, Aneg i z) ≤
      32 * C₄ / (L : ℝ) ^ 2 := by
    intro i
    calc
      _ ≤ 32 * C₄ / (R : ℝ) ^ 2 := htail_neg i
      _ = 32 * (C₄ / (R : ℝ) ^ 2) := by ring
      _ ≤ 32 * (C₄ / (L : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 32 * C₄ / (L : ℝ) ^ 2 := by ring
  let step : ℕ → Sandpile.Site 4 → ℝ := fun k u =>
    far.indicator (fun u => (f (u - p (k + 1)) - f (u - p k)) ^ 2) u
  have hstep_nonneg : ∀ k u, 0 ≤ step k u := by
    intro k u
    by_cases hmem : u ∈ far
    · dsimp only [step]
      rw [Set.indicator_of_mem hmem]
      positivity
    · dsimp only [step]
      rw [Set.indicator_of_notMem hmem]
  have hstep_summable_bound : ∀ k, k < n →
      Summable (step k) ∧ (∑' u : Sandpile.Site 4, step k u) ≤
        32 * C₄ / (L : ℝ) ^ 2 := by
    intro k hk
    have hk' : k ≤ aux_bg6_nrm1 w := by
      exact le_trans (Nat.le_of_lt hk) (by simp [n])
    have hpk : BallGreen.latticeNorm (p k) ≤ BallGreen.latticeNorm w := by
      simpa [p] using aux_bg6_gpath_norm_le_final w k hk'
    have hfar2 : ∀ z : Sandpile.Site 4, z + p k ∈ far →
        (R : ℝ) ≤ BallGreen.latticeNorm z := by
      intro z hz
      have htri := aux_bg6_latticeNorm_add_le z (p k)
      dsimp [far] at hz
      rw [hRcast]
      nlinarith [hw, hpk, htri]
    obtain ⟨i, hi | hi⟩ := aux_bg6_gpath_step w (by simpa [n] using hk)
    · have hdom : ∀ z : Sandpile.Site 4, step k (z + p k) ≤ Aneg i z := by
        intro z
        by_cases hz : z + p k ∈ far
        · have hzR := hfar2 z hz
          have hzR' : z ∈ {z : Sandpile.Site 4 |
              (R : ℝ) ≤ BallGreen.latticeNorm z} := hzR
          dsimp only [step, Aneg]
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzR']
          have hi' : p (k + 1) = p k + LatticeProb.unit i := by simpa [p] using hi
          rw [hi']
          ring_nf
          exact le_rfl
        · have hnon := hAneg_nonneg i z
          dsimp only [step]
          rw [Set.indicator_of_notMem hz]
          exact hnon
      have hshift : Summable (fun z => step k (z + p k)) :=
        Summable.of_nonneg_of_le (fun z => hstep_nonneg k (z + p k)) hdom (hAneg_sum i)
      have horig : Summable (step k) := by
        have h := ((Equiv.addRight (p k)).summable_iff (f := step k)).mp hshift
        simpa [Function.comp_def] using h
      have hle := Summable.tsum_le_tsum hdom hshift (hAneg_sum i)
      have hreindex : (∑' u : Sandpile.Site 4, step k u) =
          ∑' z : Sandpile.Site 4, step k (z + p k) := by
        symm
        exact (Equiv.addRight (p k)).tsum_eq (step k)
      refine ⟨horig, ?_⟩
      calc
        ∑' u : Sandpile.Site 4, step k u =
            ∑' z : Sandpile.Site 4, step k (z + p k) := hreindex
        _ ≤ ∑' z : Sandpile.Site 4, Aneg i z := hle
        _ ≤ 32 * C₄ / (L : ℝ) ^ 2 := htail_neg' i
    · have hdom : ∀ z : Sandpile.Site 4, step k (z + p k) ≤ Apos i z := by
        intro z
        by_cases hz : z + p k ∈ far
        · have hzR := hfar2 z hz
          have hzR' : z ∈ {z : Sandpile.Site 4 |
              (R : ℝ) ≤ BallGreen.latticeNorm z} := hzR
          dsimp only [step, Apos]
          rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzR']
          have hi' : p (k + 1) = p k - LatticeProb.unit i := by simpa [p] using hi
          rw [hi']
          ring_nf
          exact le_rfl
        · have hnon := hApos_nonneg i z
          dsimp only [step]
          rw [Set.indicator_of_notMem hz]
          exact hnon
      have hshift : Summable (fun z => step k (z + p k)) :=
        Summable.of_nonneg_of_le (fun z => hstep_nonneg k (z + p k)) hdom (hApos_sum i)
      have horig : Summable (step k) := by
        have h := ((Equiv.addRight (p k)).summable_iff (f := step k)).mp hshift
        simpa [Function.comp_def] using h
      have hle := Summable.tsum_le_tsum hdom hshift (hApos_sum i)
      have hreindex : (∑' u : Sandpile.Site 4, step k u) =
          ∑' z : Sandpile.Site 4, step k (z + p k) := by
        symm
        exact (Equiv.addRight (p k)).tsum_eq (step k)
      refine ⟨horig, ?_⟩
      calc
        ∑' u : Sandpile.Site 4, step k u =
            ∑' z : Sandpile.Site 4, step k (z + p k) := hreindex
        _ ≤ ∑' z : Sandpile.Site 4, Apos i z := hle
        _ ≤ 32 * C₄ / (L : ℝ) ^ 2 := htail_pos' i
  have hstep_sum : Summable (fun u : Sandpile.Site 4 =>
      ∑ k ∈ Finset.range n, step k u) := by
    have haux : ∀ N : ℕ, (∀ k, k < N → Summable (step k)) →
        Summable (fun u : Sandpile.Site 4 => ∑ k ∈ Finset.range N, step k u) := by
      intro N
      induction N with
      | zero =>
          intro _
          simpa only [Finset.sum_range_zero] using
            (summable_zero : Summable (fun _ : Sandpile.Site 4 => (0 : ℝ)))
      | succ N ih =>
          intro hN
          simp only [Finset.sum_range_succ]
          exact (ih (fun k hk => hN k (lt_trans hk (Nat.lt_succ_self N)))).add
            (hN N (Nat.lt_succ_self N))
    exact haux n (fun k hk => (hstep_summable_bound k hk).1)
  have hstep_rhs_sum : Summable (fun u : Sandpile.Site 4 =>
      (n : ℝ) * ∑ k ∈ Finset.range n, step k u) :=
    hstep_sum.mul_left (n : ℝ)
  let F : Sandpile.Site 4 → ℝ := fun u =>
    far.indicator (fun u => (f u - f (u - w)) ^ 2) u
  have hpoint : ∀ u : Sandpile.Site 4, F u ≤
      (n : ℝ) * ∑ k ∈ Finset.range n, step k u := by
    intro u
    by_cases hu : u ∈ far
    · have htel : ∑ k ∈ Finset.range n,
          (f (u - p k) - f (u - p (k + 1))) = f u - f (u - w) := by
        rw [Finset.sum_range_sub' (fun k => f (u - p k)) n]
        have hp0 : p 0 = 0 := by simp [p]
        have hpn : p n = w := by
          dsimp [p, n]
          simpa [sub_zero] using (aux_bg6_gpath_end w 0)
        rw [hp0, hpn]
        simp
      have hcs := sq_sum_le_card_mul_sum_sq
        (s := Finset.range n)
        (f := fun k => f (u - p k) - f (u - p (k + 1)))
      rw [Finset.card_range, htel] at hcs
      dsimp only [F]
      rw [Set.indicator_of_mem hu]
      have hstepmem : ∀ k ∈ Finset.range n, step k u =
          (f (u - p k) - f (u - p (k + 1))) ^ 2 := by
        intro k hk
        dsimp only [step]
        rw [Set.indicator_of_mem hu]
        ring
      have hsum_eq :
          (∑ k ∈ Finset.range n, (f (u - p k) - f (u - p (k + 1))) ^ 2) =
            ∑ k ∈ Finset.range n, step k u :=
        (Finset.sum_congr rfl hstepmem).symm
      rw [hsum_eq] at hcs
      exact hcs
    · dsimp only [F]
      rw [Set.indicator_of_notMem hu]
      have hzero : ∀ k ∈ Finset.range n, step k u = 0 := by
        intro k hk
        dsimp only [step]
        rw [Set.indicator_of_notMem hu]
      rw [Finset.sum_eq_zero hzero]
      simp
  have hF_nonneg : ∀ u, 0 ≤ F u := by
    intro u
    by_cases hu : u ∈ far
    · dsimp only [F]
      rw [Set.indicator_of_mem hu]
      positivity
    · dsimp only [F]
      rw [Set.indicator_of_notMem hu]
  have hF_sum : Summable F :=
    Summable.of_nonneg_of_le hF_nonneg hpoint hstep_rhs_sum
  have htsum := Summable.tsum_le_tsum hpoint hF_sum hstep_rhs_sum
  have hfinite : (∑' u : Sandpile.Site 4,
      (n : ℝ) * ∑ k ∈ Finset.range n, step k u) =
      (n : ℝ) * ∑ k ∈ Finset.range n, (∑' u : Sandpile.Site 4, step k u) := by
    rw [tsum_mul_left, Summable.tsum_finsetSum]
    intro k hk
    exact (hstep_summable_bound k (Finset.mem_range.mp hk)).1
  have henergy : (∑' u : Sandpile.Site 4, F u) ≤
      (n : ℝ) ^ 2 * (32 * C₄ / (L : ℝ) ^ 2) := by
    calc
      _ ≤ ∑' u : Sandpile.Site 4,
          (n : ℝ) * ∑ k ∈ Finset.range n, step k u := htsum
      _ = (n : ℝ) * ∑ k ∈ Finset.range n,
          (∑' u : Sandpile.Site 4, step k u) := hfinite
      _ ≤ (n : ℝ) * ∑ k ∈ Finset.range n,
          (32 * C₄ / (L : ℝ) ^ 2) := by
        gcongr with k hk
        exact (hstep_summable_bound k (Finset.mem_range.mp hk)).2
      _ = (n : ℝ) ^ 2 * (32 * C₄ / (L : ℝ) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range]
        ring
  have hn : (n : ℝ) ≤ 2 * M * (L : ℝ) := by
    dsimp [n]
    have hnorm := aux_bg6_nrm1_le_two_norm w
    nlinarith [hw]
  have hn_sq : (n : ℝ) ^ 2 ≤ (2 * M * (L : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * M * (L : ℝ))]
  have henergy' : (∑' u : Sandpile.Site 4, F u) ≤ 128 * C₄ * M ^ 2 := by
    calc
      _ ≤ (n : ℝ) ^ 2 * (32 * C₄ / (L : ℝ) ^ 2) := henergy
      _ ≤ (2 * M * (L : ℝ)) ^ 2 * (32 * C₄ / (L : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hn_sq (by positivity)
      _ = 128 * C₄ * M ^ 2 := by
        field_simp
        ring
  have hM2 : M ^ 2 ≤ (1 + M) ^ 4 := by
    have h1 : M ^ 2 ≤ (1 + M) ^ 2 := by nlinarith [sq_nonneg M]
    have h2 : (1 + M) ^ 2 ≤ (1 + M) ^ 4 := by
      nlinarith [sq_nonneg ((1 + M) ^ 2 - 1)]
    exact h1.trans h2
  have hfinal : (∑' u : Sandpile.Site 4, F u) ≤
      (1024 * C₄) * (1 + M) ^ 4 := by
    calc
      _ ≤ 128 * C₄ * M ^ 2 := henergy'
      _ ≤ (1024 * C₄) * (1 + M) ^ 4 := by
        nlinarith [hM2]
  simpa [F, far, f] using hfinal

theorem aux_ballgreen_clause6_holds : aux_ballgreen_clause6 :=
  aux_bg6_reduce aux_bg6_far_residual_holds

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The dimension-four ball-killed Green estimates, proved rather than assumed. -/
theorem Sandpile.External.ballGreenBounds : Sandpile.External.BallGreenBounds :=
  Sandpile.External.aux_ballgreen_assemble
    Sandpile.External.aux_ballgreen_clause1
    Sandpile.External.aux_ballgreen_clause2
    Sandpile.External.aux_ballgreen_clause3
    Sandpile.External.aux_ballgreen_clause4_holds
    Sandpile.External.aux_ballgreen_clause5
    Sandpile.External.aux_ballgreen_clause6_holds
    Sandpile.External.aux_ballgreen_clause7_holds
-- FROZEN-STATEMENT-END
