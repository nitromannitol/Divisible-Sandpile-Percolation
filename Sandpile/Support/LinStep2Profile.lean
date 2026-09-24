/-
The replacement of `n_R` by `R^2T` in the profile (`sandpile.tex:5571-5574`).

The paper's Step 2 produces the profile `(1-j/n_R)^\kappa`, while the lemma's conclusion is
stated with `(1-j/(R^2T))^\kappa`; the paper says "Since `n_R/(R^2T)\to1`, replacing `n_R`
by `R^2T` changes the weight by `o(1)` uniformly for `j\leq(1-\varepsilon)n_R`."  The two
arguments differ by at most `1/n_R` (`abs_profile_arg_sub_le`), because
`0\leq R^2T-n_R<1` and `j\leq n_R`, and the profile is uniformly continuous on `[0,1]`
(`Sandpile.exists_delta_rpow`), so the difference of the two powers is eventually below any
target, uniformly in `j` (`eventually_abs_profile_sub_lt`).
-/
import Sandpile.Support.LinStep2Connect

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The two profile arguments differ by at most `1/n_R`. -/
theorem abs_profile_arg_sub_le (T R : ℝ) (hRT : 1 ≤ R ^ 2 * T) (j : ℕ)
    (hj : j < ⌊R ^ 2 * T⌋₊) :
    |(1 - (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) - (1 - (j : ℝ) / (R ^ 2 * T))|
      ≤ 1 / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by
  set N : ℝ := R ^ 2 * T with hN
  set n : ℕ := ⌊N⌋₊ with hn
  have hN0 : (0 : ℝ) < N := by linarith
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnN : (n : ℝ) ≤ N := Nat.floor_le hN0.le
  have hNn : N < (n : ℝ) + 1 := Nat.lt_floor_add_one N
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hjn : (j : ℝ) ≤ (n : ℝ) := by
    have : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
    linarith
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rw [abs_sub_comm]
  have hid : (1 - (j : ℝ) / N) - (1 - (j : ℝ) / (n : ℝ))
      = (j : ℝ) * (N - (n : ℝ)) / ((n : ℝ) * N) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * N),
    abs_of_nonneg (mul_nonneg hj0 (sub_nonneg.mpr hnN))]
  rw [div_le_div_iff₀ (by positivity) hn0]
  have h1 : (j : ℝ) * (N - (n : ℝ)) ≤ (n : ℝ) * (N - (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hjn (sub_nonneg.mpr hnN)
  have h2 : (n : ℝ) * (N - (n : ℝ)) ≤ (n : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hn0.le
  have h3 : (j : ℝ) * (N - (n : ℝ)) ≤ (n : ℝ) := by linarith
  have h4 : (j : ℝ) * (N - (n : ℝ)) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right h3 hn0.le
  have h5 : (n : ℝ) * (n : ℝ) ≤ (n : ℝ) * N := mul_le_mul_of_nonneg_left hnN hn0.le
  linarith

/-- **The `n_R\to R^2T` replacement in the profile** (`sandpile.tex:5566-5569`), uniformly
in `j<n_R`. -/
theorem eventually_abs_profile_sub_lt (T : ℝ) (hT : 0 < T) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ R : ℝ in atTop, ∀ j : ℕ, j < ⌊R ^ 2 * T⌋₊ →
      |(1 - (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) ^ kappa
        - (1 - (j : ℝ) / (R ^ 2 * T)) ^ kappa| < eps := by
  obtain ⟨δ, hδ, hcont⟩ := exists_delta_rpow kappa hkappa heps
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  have hfl : Tendsto (fun R : ℝ => ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp hsq)
  filter_upwards [hfl.eventually_ge_atTop (1 / δ + 1), hsq.eventually_ge_atTop 1]
    with R hbig hRT
  intro j hj
  have hN0 : (0 : ℝ) < R ^ 2 * T := by linarith
  have hn1 : 1 ≤ ⌊R ^ 2 * T⌋₊ := by omega
  have hnR : (0 : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn1
    linarith
  have hnN : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le hN0.le
  have hjltn : (j : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast hj
  have hmem1 : (1 - (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have : (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ 1 := (div_le_one hnR).mpr hjltn.le
      linarith
    · have : (0 : ℝ) ≤ (j : ℝ) / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by positivity
      linarith
  have hmem2 : (1 - (j : ℝ) / (R ^ 2 * T)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have : (j : ℝ) / (R ^ 2 * T) ≤ 1 := (div_le_one hN0).mpr (by linarith)
      linarith
    · have : (0 : ℝ) ≤ (j : ℝ) / (R ^ 2 * T) := by positivity
      linarith
  refine hcont _ hmem1 _ hmem2 ?_
  have hle := abs_profile_arg_sub_le T R hRT j hj
  have hsmall : 1 / ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) < δ := by
    rw [div_lt_iff₀ hnR]
    have hδ1 : 1 / δ + 1 ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := hbig
    have : 1 / δ < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  linarith [hle, hsmall]

/-- The mean deviation of the survival probability from any constant is finite: the
integrand is measurable in the path and bounded by `1+|p|`. -/
theorem integrable_abs_survivalProb_sub [NeZero d] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (p : ℝ) :
    Integrable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
          (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - p|) (walkLaw d 0) := by
  have hmeas : AEStronglyMeasurable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
          (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - p|) (walkLaw d 0) :=
    (((stronglyMeasurable_survivalProb ν n j).sub
      stronglyMeasurable_const).aestronglyMeasurable).norm
  refine Integrable.mono' (integrable_const (1 + |p|)) hmeas
    (Filter.Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  have h0 := survivalProb_nonneg ν n j X
  have h1 := survivalProb_le_one ν n j X
  have hp : -|p| ≤ p := neg_abs_le p
  have hp' : p ≤ |p| := le_abs_self p
  rw [abs_le]
  constructor <;> linarith

/-- **The profile replacement carried through the integral** (`sandpile.tex:5566-5569`):
changing the profile by at most `c₂` changes the mean deviation by at most `c₂`. -/
theorem integral_abs_survival_sub_profile_real_le [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n j : ℕ) (p q c1 c2 : ℝ)
    (h1 : ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - p| ∂(walkLaw d 0) ≤ c1)
    (h2 : |p - q| ≤ c2) :
    ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - q| ∂(walkLaw d 0) ≤ c1 + c2 := by
  have hint1 := integrable_abs_survivalProb_sub (d := d) ν n j p
  have hint2 := integrable_abs_survivalProb_sub (d := d) ν n j q
  have hpt : ∀ X : ℕ → Site d,
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
          (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - q|
        ≤ |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - p| + c2 := by
    intro X
    have htri : |(∫ σ, Set.indicator {Y : ℕ → Site d |
          ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
          ∂(centeredMassLaw d ν)) - q|
        ≤ |(∫ σ, Set.indicator {Y : ℕ → Site d |
            ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
            ∂(centeredMassLaw d ν)) - p| + |p - q| := by
      calc |(∫ σ, Set.indicator {Y : ℕ → Site d |
              ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
              ∂(centeredMassLaw d ν)) - q|
          = |((∫ σ, Set.indicator {Y : ℕ → Site d |
              ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
              ∂(centeredMassLaw d ν)) - p) + (p - q)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith [htri, h2]
  have hintg : Integrable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
          (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - p| + c2) (walkLaw d 0) :=
    hint1.add (integrable_const c2)
  have hmono := integral_mono hint2 hintg hpt
  have hval : ∫ X, (|(∫ σ, Set.indicator {Y : ℕ → Site d |
        ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
        ∂(centeredMassLaw d ν)) - p| + c2) ∂(walkLaw d 0)
      = (∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d |
          ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} (fun _ => (1 : ℝ)) X
          ∂(centeredMassLaw d ν)) - p| ∂(walkLaw d 0)) + c2 := by
    rw [integral_add hint1 (integrable_const c2), integral_const, probReal_univ, smul_eq_mul,
      one_mul]
  rw [hval] at hmono
  linarith [hmono, h1]

end Sandpile
