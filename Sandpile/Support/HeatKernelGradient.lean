/-
The same-parity heat-kernel gradient in the Euclidean metric. Translation
identifies the kernels, parity matches the graph norm, and norm comparison
changes only the dimension-dependent constant.
-/
import Sandpile.External.GaussianUpperProved
import Sandpile.External.VarianceScaleProved
import LatticeProb.Walk.GenGrad

open scoped BigOperators

namespace Sandpile

lemma graphNorm_sub_le_dim_mul_latticeDist {d : ℕ} (x y : Site d) :
    (LatticeProb.graphNorm (x - y) : ℝ) ≤ (d : ℝ) * External.latticeDist x y := by
  have hexp : (LatticeProb.graphNorm (x - y) : ℝ) =
      ∑ i : Fin d, |((x i - y i : ℤ) : ℝ)| := by
    unfold LatticeProb.graphNorm
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    push_cast [Pi.sub_apply]
    rfl
  have hcoord (i : Fin d) : |((x i - y i : ℤ) : ℝ)| ≤ External.latticeDist x y := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum
      (f := fun j : Fin d => ((x j - y j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  rw [hexp]
  calc
    _ ≤ ∑ _ : Fin d, External.latticeDist x y := Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := by simp

lemma sameParity_even_graphNorm {d : ℕ} {x y : Site d} (h : External.SameParity x y) :
    Even (LatticeProb.graphNorm (x - y)) := by
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [LatticeProb.graphNorm_cast_zmod]
  exact ZMod.intCast_eq_zero_iff_even.mpr h

lemma exists_heatKernel_tv_gradient (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, External.SameParity x w →
      ∑' y : Site d, |heatKernel d n x y - heatKernel d n w y| ≤
        C * External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := LatticeProb.exists_tsum_abs_srwHeat_even_shift_le hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨C * d, by positivity, ?_⟩
  intro n hn x w hpar
  have he : (∑' y : Site d, |heatKernel d n x y - heatKernel d n w y|) =
      ∑' z : Site d, |LatticeProb.srwHeat d n z - LatticeProb.srwHeat d n (z + (x - w))| := by
    calc
      _ = ∑' y : Site d, |LatticeProb.srwHeat d n (y - x) -
          LatticeProb.srwHeat d n ((y - x) + (x - w))| := by
        apply tsum_congr
        intro y
        rw [heatKernel_eq_srwHeat, heatKernel_eq_srwHeat,
          show y - w = (y - x) + (x - w) by abel]
      _ = _ := (Equiv.subRight x).tsum_eq
        (fun z : Site d => |LatticeProb.srwHeat d n z - LatticeProb.srwHeat d n (z + (x - w))|)
  rw [he]
  calc
    _ ≤ C * (LatticeProb.graphNorm (x - w) : ℝ) / Real.sqrt n :=
      hbound n hn (x - w) (sameParity_even_graphNorm hpar)
    _ ≤ C * ((d : ℝ) * External.latticeDist x w) / Real.sqrt n :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (graphNorm_sub_le_dim_mul_latticeDist x w) hC.le)
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.rpow_div_two_eq_sqrt (-(1 : ℝ)) (Nat.cast_nonneg n), Real.rpow_neg_one]
      ring

end Sandpile
