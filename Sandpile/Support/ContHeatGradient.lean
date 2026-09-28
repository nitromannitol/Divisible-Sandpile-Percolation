import Sandpile.Support.Iterate
import Sandpile.Support.Kernel
import Sandpile.Support.ContGreenFubini
import Sandpile.Support.CorrelationRow
import Sandpile.External.HeatKernelBounds

/-!
# The pointwise gradient bound for the lattice heat kernel

The paper's two estimates from `ssec:green-estimates`, the Gaussian upper bound
(`eq:rw-gaussian-upper`) `p_n(x,y) ≤ C n^{-d/2} e^{-c|x-y|²/n}` and the total-variation gradient
bound (`eq:rw-tv-gradient`) `∑_y |p_n(x,y) - p_n(w,y)| ≤ C|x-w|n^{-1/2}` for `x` and `w` of the
same parity, are packaged into `External.HeatKernelBounds`. `exists_pointwise_gradient` derives
from them the POINTWISE difference bound `|p_n(x,y) - p_n(x',y)| ≤ C|x-x'|n^{-(d+1)/2}` that the
`L²` increment of the Green coefficients, and so the tightness of the rescaled linear field,
actually needs. The proof splits the time `n` into two halves via `tsum_heatKernel_sub`
(Chapman-Kolmogorov with the difference on the first factor,
`p_n(x,y) - p_n(x',y) = ∑_z (p_m(x,z) - p_m(x',z)) p_{m'}(z,y)`), bounds the second half
uniformly in `z` by the Gaussian bound and the first half's contribution by the total-variation
gradient bound (`abs_tsum_mul_le`), and combines the two half-time powers `m^{-1/2}` and
`(m')^{-d/2}`, each at least a third of `n`, into `n^{-(d+1)/2}` via `rpow_neg_third_le`.
`tsum_greenTime_sub_sq` then expands the `L²` increment of the truncated Green kernel
`∑_z (G_k(x,z) - G_k(x',z))^2` at two sites into the double time sum of pointwise kernel
differences that this bound controls.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The difference of two heat kernels at a common time, written through
Chapman-Kolmogorov with the difference on the first factor. -/
theorem tsum_heatKernel_sub (m m' : ℕ) (x x' y : Site d) :
    Sandpile.heatKernel d (m + m') x y - Sandpile.heatKernel d (m + m') x' y
      = ∑' z : Site d,
          (Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z) *
            Sandpile.heatKernel d m' z y := by
  rw [← Sandpile.tsum_heatKernel_mul_heatKernel m m' x y,
    ← Sandpile.tsum_heatKernel_mul_heatKernel m m' x' y,
    ← Summable.tsum_sub (summable_heatKernel_mul m x (fun z => Sandpile.heatKernel d m' z y))
      (summable_heatKernel_mul m x' (fun z => Sandpile.heatKernel d m' z y))]
  exact tsum_congr fun z => (sub_mul _ _ _).symm

/-- A tail bound for a sum against a bounded factor. -/
theorem abs_tsum_mul_le {ι : Type*} (a b : ι → ℝ) (B : ℝ)
    (hB : ∀ z, |b z| ≤ B) (ha : Summable a) :
    |∑' z, a z * b z| ≤ B * ∑' z, |a z| := by
  have habs : Summable fun z => |a z| := ha.abs
  have hmul : Summable fun z => a z * b z := by
    refine Summable.of_norm_bounded (g := fun z => |a z| * B) (habs.mul_right B) fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
  calc |∑' z, a z * b z|
      ≤ ∑' z, |a z * b z| := by
        have := norm_tsum_le_tsum_norm (f := fun z => a z * b z)
          (by simpa [Real.norm_eq_abs] using hmul.abs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' z, |a z| * B := by
        refine Summable.tsum_le_tsum (fun z => ?_) hmul.abs (habs.mul_right B)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    _ = B * ∑' z, |a z| := by rw [tsum_mul_right]; ring

/-- A negative power of a time at least a third of `n` is a bounded multiple of
the same power of `n`. -/
theorem rpow_neg_third_le {n m : ℕ} (hn0 : 1 ≤ n) (hm : 1 ≤ m) (h3 : n ≤ 3 * m)
    {β : ℝ} (hβ : 0 ≤ β) :
    (m : ℝ) ^ (-β) ≤ 3 ^ β * (n : ℝ) ^ (-β) := by
  · have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hn0' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hdiv : (n : ℝ) / 3 ≤ (m : ℝ) := by
      have : (n : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast h3
      linarith
    have hpos : (0:ℝ) < (n : ℝ) / 3 := by linarith
    have hstep : (m : ℝ) ^ (-β) ≤ ((n : ℝ) / 3) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hpos hdiv (by linarith)
    refine le_trans hstep (le_of_eq ?_)
    rw [Real.div_rpow hn0'.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
    field_simp

/-- **The pointwise gradient bound for the lattice heat kernel.**  From the
Gaussian upper bound and the total variation gradient bound of
`ssec:green-estimates`, by splitting the time into two halves: the difference
lands on the first half, where it is summable to `C|x-x'|m^{-1/2}`, and the
second half contributes its uniform bound `C(m')^{-d/2}`. -/
theorem exists_pointwise_gradient (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x x' y : Site d,
      Sandpile.External.SameParity x x' →
      |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n x' y| ≤
        C * Sandpile.External.latticeDist x x' * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
  obtain ⟨⟨C₁, c₁, hC₁, hc₁, hgauss⟩, ⟨C₂, hC₂, hgrad⟩, -⟩ := hHK d hd
  refine ⟨C₁ * C₂ * 3 ^ (((d : ℝ) + 1) / 2), by positivity, ?_⟩
  intro n hn x x' y hpar
  have hn0 : 1 ≤ n := by omega
  have hn0' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hm1 : 1 ≤ n / 2 := by omega
  have hm'1 : 1 ≤ n - n / 2 := by omega
  have hsum : n / 2 + (n - n / 2) = n := by omega
  have h3m : n ≤ 3 * (n / 2) := by omega
  have h3m' : n ≤ 3 * (n - n / 2) := by omega
  set m : ℕ := n / 2 with hmdef
  set m' : ℕ := n - n / 2 with hm'def
  set D : ℝ := Sandpile.External.latticeDist x x' with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  -- the second half is bounded uniformly in the middle point
  have hb : ∀ z : Site d,
      |Sandpile.heatKernel d m' z y| ≤ C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) := by
    intro z
    rw [abs_of_nonneg (heatKernel_nonneg m' z y)]
    have hg := hgauss m' hm'1 z y
    have hexp : Real.exp (-c₁ * Sandpile.External.latticeDist z y ^ 2 / (m' : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hm'0 : (0:ℝ) < (m' : ℝ) := by exact_mod_cast hm'1
      have : 0 ≤ c₁ * Sandpile.External.latticeDist z y ^ 2 := by positivity
      rw [div_nonpos_iff]
      exact Or.inr ⟨by linarith, hm'0.le⟩
    have hfac : 0 ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    calc Sandpile.heatKernel d m' z y
        ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (-c₁ * Sandpile.External.latticeDist z y ^ 2 / (m' : ℝ)) := hg
      _ ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) * 1 := by
          exact mul_le_mul_of_nonneg_left hexp hfac
      _ = C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) := by rw [mul_one, neg_div]
  -- the difference over the first half is summable
  have hs1 : Summable (fun z : Site d => Sandpile.heatKernel d m x z) := by
    simpa using summable_heatKernel_mul m x (fun _ => (1:ℝ))
  have hs2 : Summable (fun z : Site d => Sandpile.heatKernel d m x' z) := by
    simpa using summable_heatKernel_mul m x' (fun _ => (1:ℝ))
  have hA : (m' : ℝ) ^ (-((d : ℝ) / 2)) ≤ 3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2)) :=
    rpow_neg_third_le hn0 hm'1 h3m' (by positivity)
  have hB : (m : ℝ) ^ (-((1 : ℝ) / 2)) ≤ 3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2)) :=
    rpow_neg_third_le hn0 hm1 h3m (by norm_num)
  have hgradm : ∑' z : Site d,
      |Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z|
        ≤ C₂ * D * (m : ℝ) ^ (-((1 : ℝ) / 2)) := by
    have := hgrad m hm1 x x' hpar
    rwa [neg_div, ← hD] at this
  have e3 : (3:ℝ) ^ ((d : ℝ) / 2) * (3:ℝ) ^ ((1 : ℝ) / 2) = (3:ℝ) ^ (((d : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  have e4 : (n:ℝ) ^ (-((d : ℝ) / 2)) * (n:ℝ) ^ (-((1 : ℝ) / 2))
      = (n:ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hn0']
    congr 1
    ring
  have heq : C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
      (C₂ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))))
      = C₁ * C₂ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    calc C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
        (C₂ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))))
        = C₁ * C₂ * (3 ^ ((d : ℝ) / 2) * 3 ^ ((1 : ℝ) / 2)) * D *
            ((n : ℝ) ^ (-((d : ℝ) / 2)) * (n : ℝ) ^ (-((1 : ℝ) / 2))) := by ring
      _ = C₁ * C₂ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
          rw [e3, e4]
  have hkey : Sandpile.heatKernel d n x y - Sandpile.heatKernel d n x' y
      = ∑' z : Site d,
          (Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z) *
            Sandpile.heatKernel d m' z y := by
    rw [← hsum]
    exact tsum_heatKernel_sub m m' x x' y
  rw [hkey]
  calc |∑' z : Site d,
        (Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z) *
          Sandpile.heatKernel d m' z y|
      ≤ C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) *
          ∑' z : Site d, |Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z| :=
        abs_tsum_mul_le _ _ _ hb (hs1.sub hs2)
    _ ≤ C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
          (C₂ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2)))) := by
        have hS0 : (0:ℝ) ≤ ∑' z : Site d,
            |Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z| :=
          tsum_nonneg fun z => abs_nonneg _
        have hS : (∑' z : Site d,
            |Sandpile.heatKernel d m x z - Sandpile.heatKernel d m x' z|)
            ≤ C₂ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))) :=
          le_trans hgradm (mul_le_mul_of_nonneg_left hB (mul_nonneg hC₂.le hD0))
        have hAA : C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2))
            ≤ C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hA hC₁.le
        exact mul_le_mul hAA hS hS0 (mul_nonneg hC₁.le (by positivity))
    _ = C₁ * C₂ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := heq

/-! ### The `L²` increment of the Green coefficients in the space variable -/

/-- **The `L²` increment of the truncated Green kernel at two sites is a double
time sum of differences of transition probabilities.**  Expanding the square and
applying the doubled Fubini identity to each of the three terms, the diagonal
terms give `p_{a+b}(x,x)` and `p_{a+b}(x',x')` and the cross term gives
`p_{a+b}(x,x')`, which the symmetry of the kernel writes as `p_{a+b}(x',x)`.
Each summand is then a difference of the kernel at two sites at a common time,
which is what the pointwise gradient bound estimates. -/
theorem tsum_greenTime_sub_sq (k : ℕ) (x x' : Site d) :
    ∑' z : Site d, (Sandpile.greenTime d k x z - Sandpile.greenTime d k x' z) ^ 2
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
          ((Sandpile.heatKernel d (a + b) x x - Sandpile.heatKernel d (a + b) x' x) +
            (Sandpile.heatKernel d (a + b) x' x' - Sandpile.heatKernel d (a + b) x x')) := by
  have hexp : ∀ z : Site d, (Sandpile.greenTime d k x z - Sandpile.greenTime d k x' z) ^ 2
      = (Sandpile.greenTime d k x z * Sandpile.greenTime d k x z
          + Sandpile.greenTime d k x' z * Sandpile.greenTime d k x' z)
        - (Sandpile.greenTime d k x z * Sandpile.greenTime d k x' z
          + Sandpile.greenTime d k x' z * Sandpile.greenTime d k x z) := by
    intro z; ring
  have s11 := summable_greenTime_mul_greenTime (d := d) k k x x
  have s22 := summable_greenTime_mul_greenTime (d := d) k k x' x'
  have s12 := summable_greenTime_mul_greenTime (d := d) k k x x'
  have s21 := summable_greenTime_mul_greenTime (d := d) k k x' x
  rw [tsum_congr hexp, Summable.tsum_sub (s11.add s22) (s12.add s21),
    Summable.tsum_add s11 s22, Summable.tsum_add s12 s21,
    tsum_greenTime_mul_greenTime k k x x, tsum_greenTime_mul_greenTime k k x' x',
    tsum_greenTime_mul_greenTime k k x x', tsum_greenTime_mul_greenTime k k x' x]
  have hmerge : ∀ F G H I : ℕ → ℕ → ℝ,
      ((∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, F a b) +
          ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, G a b) -
        ((∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, H a b) +
          ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, I a b)
        = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
            (F a b + G a b - (H a b + I a b)) := by
    intro F G H I
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hmerge (fun a b => Sandpile.heatKernel d (a + b) x x)
    (fun a b => Sandpile.heatKernel d (a + b) x' x')
    (fun a b => Sandpile.heatKernel d (a + b) x x')
    (fun a b => Sandpile.heatKernel d (a + b) x' x)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Sandpile.heatKernel_symm (a + b) x x']
  ring

end Sandpile.Support
