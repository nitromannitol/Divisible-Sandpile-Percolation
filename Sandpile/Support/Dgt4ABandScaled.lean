/-
The summed profile `eq:dgt4-band-scaled-profile` of Step 2 of
`thm:dgt4-many-limits` (`sandpile.tex:6223-6250`), assembled from the summation
of the one-step increment bound, the pointwise arithmetic bound, the vanishing
of the error bound and the uniform-convergence step.

The profile `y_{k,n} = z_{k,n}^{-ϑ_k}` depends on the scale as well as on the
time, and the paper sums its increments from the hitting time `τ_k`, where it is
`O(1)`, not from zero.  Both must be carried: a single sequence read at every
scale cannot satisfy the increment hypothesis in the regime of the band
construction, since the band weights tend to zero while the exponents stay
bounded, and `Sandpile.Support.no_single_sequence_summed_profile` proves that.
So the summation is stated for a FAMILY `y : ℕ → ℕ → ℝ` of sequences with a
family of starting indices `s_k = o(R_k^2)`.

The two earlier readings are kept as corollaries, at the constant family and the
zero offset: the sequence-indexed exponents `scaledProfile_of_increments_seq`,
and the fixed exponent `scaledProfile_of_increments`, so nothing already proved
is lost.
-/
import Sandpile.Support.Dgt4ABandPointwiseBound
import Sandpile.Support.Dgt4ABandSupConv
import Sandpile.Support.Dgt4ABandBoundTendsto

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- **The summed profile of Step 2 for a family of profiles started at a family
of offsets** (`sandpile.tex:6218-6245`): if the increments of `y_k` from the
index `s_k` on are `ω_k(1+o(1))/(G(0,0)κ_k)`, uniformly up to the index `TR_k²`,
if `y_k(s_k)` is `O(1)` and `s_k = o(R_k²)`, then `y_k(⌊tR_k²⌋)/L_k → t/κ_k`
uniformly on `[δ,T]`.  The exponents need only be bounded away from zero. -/
theorem scaledProfile_bound_family
    (y : ℕ → ℕ → ℝ) (R L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (s : ℕ → ℕ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0))
    (hys : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, |y k (s k)| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, s k ≤ i → i < n →
          |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T → ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc δ T,
        |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k| ≤ b k := by
  intro δ T hδ hδT
  obtain ⟨C, hC⟩ := hys
  have hkappos : ∀ k, 0 < kap k := fun k => lt_of_lt_of_le hκ0 (hkap k)
  have hLpos : ∀ᶠ k : ℕ in atTop, 0 < L k := hL.eventually_gt_atTop 0
  have hRpos : ∀ᶠ k : ℕ in atTop, 0 < R k := hR.eventually_gt_atTop 0
  have hωpos : ∀ᶠ k : ℕ in atTop, 0 ≤ ω k := by
    filter_upwards [hLpos, hRpos] with k hLk hRk
    have h1 : 0 < R k ^ 2 * ω k := by rw [hRL k]; positivity
    nlinarith [sq_pos_of_pos hRk]
  have hηabs : Tendsto (fun k : ℕ => |η k|) atTop (𝓝 0) := by
    simpa using hη.abs
  have hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  have hone : Tendsto (fun k : ℕ => 1 / R k ^ 2) atTop (𝓝 0) := hR2.const_div_atTop 1
  have hsum : Tendsto (fun k : ℕ => 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0) := by
    simpa using hone.add hs
  have hsfit0 : ∀ᶠ k : ℕ in atTop, 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2 ≤ δ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum δ hδ
    filter_upwards [eventually_ge_atTop N] with k hk
    have hd := hN k hk
    rw [Real.dist_eq, sub_zero] at hd
    exact le_of_lt (lt_of_abs_lt hd)
  have hsfit : ∀ᶠ k : ℕ in atTop, (1 : ℝ) + ((s k : ℕ) : ℝ) ≤ δ * R k ^ 2 := by
    filter_upwards [hsfit0, hRpos] with k h hRk
    have hR2k : 0 < R k ^ 2 := pow_pos hRk 2
    have heq : 1 / R k ^ 2 + ((s k : ℕ) : ℝ) / R k ^ 2
        = (1 + ((s k : ℕ) : ℝ)) / R k ^ 2 := by ring
    rw [heq, div_le_iff₀ hR2k] at h
    linarith
  have hpt : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Set.Icc δ T,
      |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k| ≤
        C / L k + (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) + |η k| * G00 * T := by
    filter_upwards [hLpos, hRpos, hωpos, hC, hsfit, hinc T (lt_trans hδ hδT)] with
      k hLk hRk hωk hCk hsfitk hinc_k
    intro t ht
    have ht0 : t ∈ Set.Icc (0 : ℝ) T := ⟨le_trans hδ.le ht.1, ht.2⟩
    have hR2k : 0 < R k ^ 2 := pow_pos hRk 2
    have hfl : (⌊t * R k ^ 2⌋₊ : ℝ) ≤ t * R k ^ 2 :=
      Nat.floor_le (mul_nonneg ht0.1 (sq_nonneg _))
    have hflT : (⌊t * R k ^ 2⌋₊ : ℝ) ≤ T * R k ^ 2 :=
      le_trans hfl (mul_le_mul_of_nonneg_right ht0.2 (sq_nonneg _))
    have hslt : ((s k : ℕ) : ℝ) < (⌊t * R k ^ 2⌋₊ : ℝ) := by
      have h1 : t * R k ^ 2 - 1 < (⌊t * R k ^ 2⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (t * R k ^ 2)
        linarith
      have h2 : δ * R k ^ 2 ≤ t * R k ^ 2 :=
        mul_le_mul_of_nonneg_right ht.1 hR2k.le
      linarith
    have hsn : s k ≤ ⌊t * R k ^ 2⌋₊ := le_of_lt (by exact_mod_cast hslt)
    have hband : ∀ i : ℕ, s k ≤ i → i < ⌊t * R k ^ 2⌋₊ →
        |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ |η k| * ω k := by
      intro i hi hi'
      exact le_trans (hinc_k ⌊t * R k ^ 2⌋₊ hflT i hi hi')
        (mul_le_mul_of_nonneg_right (le_abs_self _) hωk)
    have hmain := abs_profile_le_of_increments_offset (y k) R L ω (kap k) G00 C (|η k|) T k
      (s k) t (hkappos k) hG hLk (abs_nonneg _) hωk (hRL k) hsn hCk hband ht0
    refine hmain.trans ?_
    have hle : (1 + ((s k : ℕ) : ℝ)) / (kap k * R k ^ 2)
        ≤ (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) := by
      refine div_le_div_of_nonneg_left (by positivity) (mul_pos hκ0 hR2k) ?_
      exact mul_le_mul_of_nonneg_right (hkap k) hR2k.le
    linarith
  exact ⟨fun k => C / L k + (1 + ((s k : ℕ) : ℝ)) / (κ0 * R k ^ 2) + |η k| * G00 * T,
    tendsto_bound_of_scaled_offset R L (fun k => |η k|) s C κ0 G00 T hκ0 hR hL hηabs hs, hpt⟩

/-- **The summed profile of Step 2 for a family of profiles started at a family
of offsets** (`eq:dgt4-band-summed-profile`, `sandpile.tex:6218-6245`):
`y_k(⌊tR_k²⌋)/L_k → t/κ_k` uniformly on `[δ,T]`. -/
theorem scaledProfile_of_increments_family
    (y : ℕ → ℕ → ℝ) (R L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (s : ℕ → ℕ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0))
    (hys : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, |y k (s k)| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, s k ≤ i → i < n →
          |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T →
      Tendsto (fun k : ℕ => ⨆ t ∈ Set.Icc δ T,
          |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k|) atTop (𝓝 0) := by
  intro δ T hδ hδT
  obtain ⟨b, hb, hpt⟩ :=
    scaledProfile_bound_family y R L ω η kap s κ0 hκ0 hkap G00 hG hRL hL hR hη hs hys hinc
      δ T hδ hδT
  exact tendsto_iSup_abs_of_pointwise _ _ δ T hb hpt

/-- **The summed profile of Step 2 in the form the band estimates consume**:
for every tolerance, the rescaled profile is within it of `t/κ_k` for every `t`
in `[δ,T]`, at every large scale. -/
theorem scaledProfile_eventually_family
    (y : ℕ → ℕ → ℝ) (R L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (s : ℕ → ℕ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0))
    (hys : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, |y k (s k)| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, s k ≤ i → i < n →
          |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop,
      ∀ t ∈ Set.Icc δ T, |y k (⌊t * R k ^ 2⌋₊) / L k - t / kap k| ≤ ζ := by
  intro δ T hδ hδT ζ hζ
  obtain ⟨b, hb, hpt⟩ :=
    scaledProfile_bound_family y R L ω η kap s κ0 hκ0 hkap G00 hG hRL hL hR hη hs hys hinc
      δ T hδ hδT
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb ζ hζ
  filter_upwards [hpt, eventually_ge_atTop N] with k hk hkN
  intro t ht
  refine le_trans (hk t ht) ?_
  have hd := hN k hkN
  rw [Real.dist_eq, sub_zero] at hd
  exact le_of_lt (lt_of_abs_lt hd)

/-- **The summed profile read at the integer indices of the band.**  Every
integer `n` with `δR_k² ≤ n ≤ TR_k²` is the index `⌊tR_k²⌋` at `t = n/R_k²`, so
the profile is `n/(R_k²κ_k)` up to any tolerance, uniformly over the band. -/
theorem scaledProfile_at_index
    (y : ℕ → ℕ → ℝ) (R L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (s : ℕ → ℕ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0))
    (hys : ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, |y k (s k)| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, s k ≤ i → i < n →
          |(y k (i + 1) - y k i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ k : ℕ in atTop,
      ∀ n : ℕ, δ * R k ^ 2 ≤ (n : ℝ) → (n : ℝ) ≤ T * R k ^ 2 →
        |y k n / L k - (n : ℝ) / (R k ^ 2 * kap k)| ≤ ζ := by
  intro δ T hδ hδT ζ hζ
  have hev := scaledProfile_eventually_family y R L ω η kap s κ0 hκ0 hkap G00 hG hRL hL hR
    hη hs hys hinc δ T hδ hδT ζ hζ
  filter_upwards [hev, hR.eventually_gt_atTop 0] with k hk hRk
  intro n hn1 hn2
  have hR2k : (0 : ℝ) < R k ^ 2 := pow_pos hRk 2
  have hR2ne : R k ^ 2 ≠ 0 := ne_of_gt hR2k
  have htmem : (n : ℝ) / R k ^ 2 ∈ Set.Icc δ T := by
    constructor
    · rw [le_div_iff₀ hR2k]; linarith
    · rw [div_le_iff₀ hR2k]; linarith
  have hfl : ⌊(n : ℝ) / R k ^ 2 * R k ^ 2⌋₊ = n := by
    rw [div_mul_cancel₀ _ hR2ne, Nat.floor_natCast]
  have hmain := hk ((n : ℝ) / R k ^ 2) htmem
  rw [hfl] at hmain
  have hteq : (n : ℝ) / R k ^ 2 / kap k = (n : ℝ) / (R k ^ 2 * kap k) := div_div _ _ _
  rwa [hteq] at hmain

/-- **The summed profile of Step 2 along a sequence of exponents**
(`sandpile.tex:6218-6245`): if the increments of `y` are `ω(1+o(1))/(G(0,0)κ_k)`,
uniformly up to the index `TR²`, and `y` starts at `O(1)`, then
`y_{⌊tR_k²⌋}/L_k → t/κ_k` uniformly on `[δ,T]`.  The exponents need only be
bounded away from zero. -/
theorem scaledProfile_of_increments_seq
    (y : ℕ → ℝ) (R : ℕ → ℝ) (L : ℕ → ℝ) (ω η kap : ℕ → ℝ) (κ0 : ℝ) (hκ0 : 0 < κ0)
    (hkap : ∀ k, κ0 ≤ kap k)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hy0 : ∃ C : ℝ, ∀ᶠ _k : ℕ in atTop, |y 0| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, i < n →
          |(y (i + 1) - y i) - ω k / (G00 * kap k)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T →
      Tendsto (fun k : ℕ => ⨆ t ∈ Set.Icc δ T,
          |y (⌊t * R k ^ 2⌋₊) / L k - t / kap k|) atTop (𝓝 0) := by
  refine scaledProfile_of_increments_family (fun _ n => y n) R L ω η kap (fun _ => 0) κ0 hκ0
    hkap G00 hG hRL hL hR hη (by simp) ?_ ?_
  · obtain ⟨C, hC⟩ := hy0
    exact ⟨C, by simpa using hC⟩
  · intro T hT
    filter_upwards [hinc T hT] with k hk n hn i _ hi
    exact hk n hn i hi

/-- **The summed profile of Step 2 at a fixed exponent**, the constant-sequence
corollary of `scaledProfile_of_increments_seq`. -/
theorem scaledProfile_of_increments
    (y : ℕ → ℝ) (R : ℕ → ℝ) (L : ℕ → ℝ) (ω η : ℕ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (G00 : ℝ) (hG : 0 < G00)
    (hRL : ∀ k : ℕ, R k ^ 2 * ω k = G00 * L k)
    (hL : Tendsto L atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hy0 : ∃ C : ℝ, ∀ᶠ _k : ℕ in atTop, |y 0| ≤ C)
    (hinc : ∀ T : ℝ, 0 < T → ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
        (n : ℝ) ≤ T * R k ^ 2 → ∀ i : ℕ, i < n →
          |(y (i + 1) - y i) - ω k / (G00 * κ)| ≤ η k * ω k) :
    ∀ δ T : ℝ, 0 < δ → δ < T →
      Tendsto (fun k : ℕ => ⨆ t ∈ Set.Icc δ T,
          |y (⌊t * R k ^ 2⌋₊) / L k - t / κ|) atTop (𝓝 0) :=
  scaledProfile_of_increments_seq y R L ω η (fun _ => κ) κ hκ (fun _ => le_rfl) G00 hG
    hRL hL hR hη hy0 hinc

end Sandpile.Support
