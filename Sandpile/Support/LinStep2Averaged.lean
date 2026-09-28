import Sandpile.Support.LinStep2Uniform

/-!
# Reducing the averaged limit to uniform smallness

The averaged limit `eq:dgt4-averaged-positive-path-limit` reduced to uniform smallness on
`j\leq(1-\varepsilon)n_R` (`sandpile.tex:5571-5583`).

`Support/LinStep2Split.lean` proves the reduction for a family bounded by one at EVERY index.
The averaged sum of the lemma is not of that kind: its summand
`\int_X|\P(S_{n_R,j}(X)=1\mid X)-(1-j/(R^2T))^\kappa|` is bounded by one only for
`j<n_R`, since for `j>R^2T` the profile is a real power of a negative base and is not in
`[0,1]`. The primed lemmas below are the same three statements with the value bound asked
only on `Finset.range n_R`, which is where the split uses it.

`tendsto_averaged_survival_of_uniform` is then the whole of the lemma's first conclusion
reduced to Step 2: if for every `\varepsilon\in(0,1)` and every target the mean deviation
of the survival probability from the profile is eventually at most that target uniformly
over `j\leq(1-\varepsilon)n_R`, then `R^{-2}\sum_{j<n_R}` of it tends to zero. The
summand is bounded by one because the survival probability and the profile both lie in
`[0,1]` there, and it is integrable because the survival probability is a measurable
function of the path.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The split of a sum over `range n` at `m`, with the value bound asked only on
`range n`. -/
theorem sum_range_split_le' (n m : ℕ) (hmn : m ≤ n) (f : ℕ → ℝ) (c : ℝ)
    (hsmall : ∀ j ∈ Finset.range m, f j ≤ c) (hf1 : ∀ j ∈ Finset.range n, f j ≤ 1) :
    ∑ j ∈ Finset.range n, f j ≤ (m : ℝ) * c + ((n : ℝ) - (m : ℝ)) := by
  have hsplit : ∑ j ∈ Finset.Ico 0 m, f j + ∑ j ∈ Finset.Ico m n, f j
      = ∑ j ∈ Finset.Ico 0 n, f j := Finset.sum_Ico_consecutive f (Nat.zero_le m) hmn
  simp only [← Finset.range_eq_Ico] at hsplit
  have h1 : ∑ j ∈ Finset.range m, f j ≤ (m : ℝ) * c := by
    calc ∑ j ∈ Finset.range m, f j ≤ ∑ _j ∈ Finset.range m, c := Finset.sum_le_sum hsmall
      _ = (m : ℝ) * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h2 : ∑ j ∈ Finset.Ico m n, f j ≤ (n : ℝ) - (m : ℝ) := by
    calc ∑ j ∈ Finset.Ico m n, f j ≤ ∑ _j ∈ Finset.Ico m n, (1 : ℝ) :=
          Finset.sum_le_sum fun j hj => hf1 j (by
            rw [Finset.mem_Ico] at hj
            exact Finset.mem_range.mpr hj.2)
      _ = ((n - m : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      _ = (n : ℝ) - (m : ℝ) := by rw [Nat.cast_sub hmn]
  linarith [hsplit, h1, h2]

/-- The split of `R^{-2}\sum_{j<n_R}` at `(1-\varepsilon)n_R`, with the value bound asked
only on `range n_R`. -/
theorem inv_sq_sum_range_le' (R T ε c : ℝ) (hR : 0 < R) (hT : 0 < T) (hε0 : 0 < ε)
    (hc : 0 ≤ c) (n m : ℕ) (hn : (n : ℝ) ≤ R ^ 2 * T) (hm : m ≤ n)
    (hmlb : (1 - ε) * (n : ℝ) ≤ (m : ℝ))
    (f : ℕ → ℝ) (hsmall : ∀ j ∈ Finset.range m, f j ≤ c)
    (hf1 : ∀ j ∈ Finset.range n, f j ≤ 1) :
    (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, f j ≤ T * c + ε * T := by
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hstep := sum_range_split_le' n m hm f c hsmall hf1
  have hsum : ∑ j ∈ Finset.range n, f j ≤ (n : ℝ) * c + ε * (n : ℝ) := by
    have h1 : (m : ℝ) * c ≤ (n : ℝ) * c := mul_le_mul_of_nonneg_right hmn hc
    have h2 : (n : ℝ) - (m : ℝ) ≤ ε * (n : ℝ) := by nlinarith [hmlb]
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkey : (n : ℝ) * c + ε * (n : ℝ) ≤ R ^ 2 * (T * c + ε * T) := by
    nlinarith [hn, hc, hε0.le, hn0]
  calc (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, f j
      ≤ (R ^ 2)⁻¹ * ((n : ℝ) * c + ε * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hR2))
    _ ≤ (R ^ 2)⁻¹ * (R ^ 2 * (T * c + ε * T)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt (inv_pos.mpr hR2))
    _ = T * c + ε * T := by field_simp

/-- The reduction of `eq:dgt4-averaged-positive-path-limit` to uniform smallness, with the
value bound asked only on `range n_R`. The scale filter may be any filter below
`atTop`; the default argument recovers the unrestricted real-scale statement. -/
theorem tendsto_inv_sq_sum_of_uniform' {l : Filter ℝ} (T : ℝ) (hT : 0 < T) (F : ℝ → ℕ → ℝ)
    (hF0 : ∀ R j, 0 ≤ F R j)
    (hF1 : ∀ R : ℝ, ∀ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, F R j ≤ 1)
    (hunif : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ c : ℝ, 0 < c → ∀ᶠ R : ℝ in l,
      ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ → F R j ≤ c)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ * ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊, F R j)
      l (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro η hη
  set ε : ℝ := min (1 / 2) (η / (4 * T)) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεT : ε * T ≤ η / 4 := by
    have h := min_le_right (1 / 2 : ℝ) (η / (4 * T))
    have h2 : ε * T ≤ (η / (4 * T)) * T := mul_le_mul_of_nonneg_right h hT.le
    calc ε * T ≤ (η / (4 * T)) * T := h2
      _ = η / 4 := by field_simp
  set c : ℝ := η / (4 * T) with hcdef
  have hc0 : 0 < c := by positivity
  have hTc : T * c ≤ η / 4 := by
    rw [hcdef]
    field_simp
    norm_num
  filter_upwards [hunif ε ⟨hε0, hε1⟩ c hc0, (eventually_gt_atTop (0 : ℝ)).filter_mono hl,
      (eventually_ge_atTop (1 : ℝ)).filter_mono hl, (eventually_ge_atTop (1 / T)).filter_mono hl]
    with R hsmall hR0 hR1 hRT
  have hRT' : (1 : ℝ) ≤ R * T := by
    have h := mul_le_mul_of_nonneg_right hRT hT.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hT)] at h
  have hRT1 : (1 : ℝ) ≤ R ^ 2 * T := by
    nlinarith [hRT', hR1, hT.le,
      mul_nonneg (mul_nonneg hR0.le hT.le) (by linarith : (0 : ℝ) ≤ R - 1)]
  set n : ℕ := ⌊R ^ 2 * T⌋₊ with hndef
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hRT1)
  have hnle : (n : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
  set m : ℕ := ⌊(1 - ε) * (n : ℝ)⌋₊ + 1 with hmdef
  have hn0R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hfloorlt : ⌊(1 - ε) * (n : ℝ)⌋₊ < n := by
    rw [Nat.floor_lt (by nlinarith [hε1, hn0R])]
    nlinarith [hε0, hn0R]
  have hm : m ≤ n := hfloorlt
  have hmlb : (1 - ε) * (n : ℝ) ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one ((1 - ε) * (n : ℝ))
    rw [hmdef]
    push_cast
    linarith
  have hkey := inv_sq_sum_range_le' R T ε c hR0 hT hε0 hc0.le n m hnle hm hmlb (F R)
    (fun j hj => hsmall j (by
      have := Finset.mem_range.mp hj
      omega)) (fun j hj => hF1 R j hj)
  have hnn : 0 ≤ (R ^ 2)⁻¹ * ∑ j ∈ Finset.range n, F R j := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => hF0 R j
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  linarith [hkey, hTc, hεT]

/-- **`eq:dgt4-averaged-positive-path-limit` from Step 2** (`sandpile.tex:5566-5578`).  If
the mean deviation of the survival probability from the profile is eventually uniformly
small over `j\leq(1-\varepsilon)n_R`, for every `\varepsilon` and every target, then
`R^{-2}\sum_{j<n_R}` of it tends to zero. -/
theorem tendsto_averaged_survival_of_uniform [NeZero d] {l : Filter ℝ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (T kappa : ℝ) (hT : 0 < T) (hkappa : 0 < kappa)
    (huni : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ c : ℝ, 0 < c → ∀ᶠ R : ℝ in l,
      ∀ j : ℕ, j ≤ ⌊(1 - ε) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)⌋₊ →
        ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
              ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
              (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
            - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa| ∂(walkLaw d 0) ≤ c)
    (hl : l ≤ atTop := by exact le_rfl) :
    Tendsto (fun R : ℝ => (R ^ 2)⁻¹ *
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
                ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
                (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
              - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa| ∂(walkLaw d 0))
      l (𝓝 0) := by
  refine tendsto_inv_sq_sum_of_uniform' T hT _ (fun R j => integral_nonneg fun X => abs_nonneg _)
    (fun R j hj => ?_) huni hl
  have hjn : j < ⌊R ^ 2 * T⌋₊ := Finset.mem_range.mp hj
  have hRT1 : (1 : ℝ) ≤ R ^ 2 * T := Nat.floor_pos.mp (by omega)
  have hRT0 : (0 : ℝ) < R ^ 2 * T := by linarith
  have hnle : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT0.le
  have hjlt : (j : ℝ) < R ^ 2 * T := by
    have : (j : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hjn
    linarith
  have hb0 : (0 : ℝ) ≤ 1 - (j : ℝ) / (R ^ 2 * T) := by
    have : (j : ℝ) / (R ^ 2 * T) ≤ 1 := (div_le_one hRT0).mpr hjlt.le
    linarith
  have hb1 : 1 - (j : ℝ) / (R ^ 2 * T) ≤ 1 := by
    have : (0 : ℝ) ≤ (j : ℝ) / (R ^ 2 * T) := by positivity
    linarith
  have hp0 : (0 : ℝ) ≤ (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa := Real.rpow_nonneg hb0 kappa
  have hp1 : (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa ≤ 1 :=
    Real.rpow_le_one hb0 hb1 hkappa.le
  have hbound : ∀ X : ℕ → Site d,
      |(∫ σ, Set.indicator {Y : ℕ → Site d |
            ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
          - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa| ≤ 1 := by
    intro X
    have hA0 := survivalProb_nonneg ν ⌊R ^ 2 * T⌋₊ j X
    have hA1 := survivalProb_le_one ν ⌊R ^ 2 * T⌋₊ j X
    rw [abs_le]
    constructor <;> linarith
  have hmeas : AEStronglyMeasurable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d |
            ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
          - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa|) (walkLaw d 0) :=
    (((stronglyMeasurable_survivalProb ν ⌊R ^ 2 * T⌋₊ j).sub
      stronglyMeasurable_const).aestronglyMeasurable).norm
  have hint : Integrable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d |
            ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
          - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa|) (walkLaw d 0) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hmeas
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_abs]
        exact hbound X)
  calc ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
              ∀ r ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Y r)}
              (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν))
            - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa| ∂(walkLaw d 0)
      ≤ ∫ _X : ℕ → Site d, (1 : ℝ) ∂(walkLaw d 0) :=
        integral_mono hint (integrable_const 1) hbound
    _ = 1 := by
        rw [integral_const, probReal_univ, smul_eq_mul, mul_one]

end Sandpile
