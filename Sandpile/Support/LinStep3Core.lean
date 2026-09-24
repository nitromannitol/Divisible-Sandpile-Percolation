/-
The second conclusion of `lem:dgt4-path-survival`, `eq:dgt4-positive-path-covariance`
(`sandpile.tex:5584-5610`).

`Support/LinStep3Cov.lean` proves the estimate along one pair of paths, with the threshold
replacement, the three factorizations and the weight bound as hypotheses.  Here they are
supplied.  The paper fixes `\delta\in(0,T)` and observes that `n_R-\delta R^2\leq(1-\delta/(2T))n_R`
for all large `R`, so the window hypothesis `eq:dgt4-uniform-contact-thresholds` at
`\varepsilon=\delta/(2T)` covers every time the two paths visit; the weights are then at most
`2G(0,0)\kappa/(\delta R^2)`, which is the paper's `C/(\delta R^2)` with `C=4G(0,0)\kappa`,
and at least `G(0,0)\kappa/(2n_R)`, which is what Step 1 needs at the lower end.

`fact_on_finset` reads Step 1 on a finset of sites with a level attached to each, through the
enumeration of `Support/LinStep3Sites.lean`.  The factorization is applied three times, to the
sites of `X`, to those of `Y`, and to those of both, whence the bound `2TR^2` on the size of
the family.

The paper's "collecting the uniform errors into `\varepsilon_R(\delta)\to0`" is
`exists_tendsto_zero_of_eventually`: a bound that holds eventually in `R` at every positive
target, and trivially at the target one, holds at a nonnegative target that tends to zero.
-/
import Sandpile.Support.LinStep3Cov
import Sandpile.Support.LinStep2Core
import Sandpile.Support.LinGaussShift
import Sandpile.Support.LinStationary

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The factorization of Step 1 read on a finset of sites with a level attached to each. -/
theorem fact_on_finset (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (S : Finset (Site d)) (lev : Site d → ℝ)
    (theta K R A : ℝ)
    (hfact : ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs → (m : ℝ) ≤ A →
      ∀ lv : Fin m → ℝ,
        (∀ k, (centeredMassLaw d ν).real {σ : Site d → ℝ | lv k < J σ 0} ≤ K / R ^ 2) →
        (∀ k, 1 / (K * R ^ 2) ≤ (centeredMassLaw d ν).real
          {σ : Site d → ℝ | lv k < J σ 0}) →
        |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ k : Fin m, J σ (xs k) ≤ lv k}
          - ∏ k : Fin m, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ lv k}| ≤ theta)
    (hcard : ((S.card : ℕ) : ℝ) ≤ A)
    (hup : ∀ x ∈ S, (centeredMassLaw d ν).real {σ : Site d → ℝ | lev x < J σ 0} ≤ K / R ^ 2)
    (hlow : ∀ x ∈ S, 1 / (K * R ^ 2) ≤ (centeredMassLaw d ν).real
      {σ : Site d → ℝ | lev x < J σ 0}) :
    |(centeredMassLaw d ν).real (⋂ x ∈ S, {σ : Site d → ℝ | J σ x ≤ lev x})
      - ∏ x ∈ S, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ lev x}| ≤ theta := by
  classical
  obtain ⟨m, e, hinj, hmem, hsurj, hcardeq, hprod⟩ := exists_finset_enum S
  have h := hfact m e hinj (by rw [hcardeq]; exact hcard) (fun k => lev (e k))
    (fun k => hup (e k) (hmem k)) (fun k => hlow (e k) (hmem k))
  have hset : {σ : Site d → ℝ | ∀ k : Fin m, J σ (e k) ≤ lev (e k)}
      = ⋂ x ∈ S, {σ : Site d → ℝ | J σ x ≤ lev x} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hh x hx
      obtain ⟨k, hk⟩ := hsurj x hx
      have := hh k
      rwa [hk] at this
    · intro hh k
      exact hh (e k) (hmem k)
  rw [hset, hprod (fun x => (centeredMassLaw d ν).real
    {σ : Site d → ℝ | J σ 0 ≤ lev x})] at h
  exact h

/-- The joint level is at least the level at the later of the two path lengths. -/
theorem jointLevel_ge (i j : ℕ) (X Y : ℕ → Site d) (b : ℕ → ℝ) (hb : Antitone b)
    (x : Site d) : b (max i j) ≤ jointLevel i j X Y b x := by
  classical
  rw [jointLevel]
  have hX : b (max i j) ≤ b (lastTimeOf i X x) :=
    hb (le_trans (lastTimeOf_le i X x) (le_max_left i j))
  have hY : b (max i j) ≤ b (lastTimeOf j Y x) :=
    hb (le_trans (lastTimeOf_le j Y x) (le_max_right i j))
  split_ifs
  · exact le_min hX hY
  · exact hX
  · exact hY

/-- The joint level is at most the level at time zero. -/
theorem jointLevel_le_first (i j : ℕ) (X Y : ℕ → Site d) (b : ℕ → ℝ) (hb : Antitone b)
    (x : Site d) : jointLevel i j X Y b x ≤ b 0 := by
  classical
  rw [jointLevel]
  have hX : b (lastTimeOf i X x) ≤ b 0 := hb (Nat.zero_le _)
  have hY : b (lastTimeOf j Y x) ≤ b 0 := hb (Nat.zero_le _)
  split_ifs
  · exact le_trans (min_le_left _ _) hX
  · exact hX
  · exact hY

/-- The covariance of two survival indicators is at most one in absolute value. -/
theorem abs_cov_survival_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n i j : ℕ) (X Y : ℕ → Site d) :
    |(∫ σ, (Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
            (fun _ => (1 : ℝ)) X) *
          (Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
            (fun _ => (1 : ℝ)) Y) ∂(centeredMassLaw d ν))
        - (∫ σ, Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
              (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) *
          (∫ σ, Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
              (fun _ => (1 : ℝ)) Y ∂(centeredMassLaw d ν))| ≤ 1 := by
  rw [integral_survival_mul_eq_measureReal ν n i j X Y,
    integral_survival_eq_measureReal ν n i X, integral_survival_eq_measureReal ν n j Y]
  have ha0 : (0 : ℝ) ≤ (centeredMassLaw d ν).real
      ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
        {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}) := measureReal_nonneg
  have ha1 : (centeredMassLaw d ν).real
      ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
        {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}) ≤ 1 := measureReal_le_one
  have hb0 : (0 : ℝ) ≤ (centeredMassLaw d ν).real
      {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} := measureReal_nonneg
  have hb1 : (centeredMassLaw d ν).real
      {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ≤ 1 := measureReal_le_one
  have hc0 : (0 : ℝ) ≤ (centeredMassLaw d ν).real
      {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} := measureReal_nonneg
  have hc1 : (centeredMassLaw d ν).real
      {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor
  · nlinarith [hb0, hc0, hb1, hc1, ha1]
  · nlinarith [hb0, hc0, hb1, hc1, ha0]

set_option maxHeartbeats 2000000 in
/-- **`eq:dgt4-positive-path-covariance`**, the second conclusion of
`lem:dgt4-path-survival` (`sandpile.tex:5579-5605`), from the window hypothesis along any filter of
diverging scales. The error tends to zero along that same filter. -/
theorem exists_cov_bound_core [NeZero d] {l : Filter ℝ}
    (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (hnull : ∀ c : ℝ, NullMeasurableSet {σ : Site d → ℝ | c < J σ 0} (centeredMassLaw d ν))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in l, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η)
    (hfactev : ∀ theta : ℝ, 0 < theta → ∀ K : ℝ, 1 ≤ K → ∀ᶠ R : ℝ in l,
      ∀ (m : ℕ) (xs : Fin m → Site d), Function.Injective xs → (m : ℝ) ≤ 2 * T * R ^ 2 →
      ∀ lev : Fin m → ℝ,
        (∀ k, (centeredMassLaw d ν).real {σ : Site d → ℝ | lev k < J σ 0} ≤ K / R ^ 2) →
        (∀ k, 1 / (K * R ^ 2) ≤ (centeredMassLaw d ν).real
          {σ : Site d → ℝ | lev k < J σ 0}) →
        |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ k : Fin m, J σ (xs k) ≤ lev k}
          - ∏ k : Fin m, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ lev k}| ≤ theta)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 T)
    (hl : l ≤ atTop := by exact le_rfl) :
    ∃ efun : ℝ → ℝ, (∀ R, 0 ≤ efun R) ∧ Tendsto efun l (𝓝 0) ∧
      ∀ R : ℝ, ∀ i j : ℕ,
        (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
        (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
        ∀ X Y : ℕ → Site d,
          |(∫ σ, (Set.indicator {Z : ℕ → Site d |
                ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)} (fun _ => (1 : ℝ)) X) *
              (Set.indicator {Z : ℕ → Site d |
                ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)} (fun _ => (1 : ℝ)) Y)
              ∂(centeredMassLaw d ν))
            - (∫ σ, Set.indicator {Z : ℕ → Site d |
                  ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)}
                  (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) *
              (∫ σ, Set.indicator {Z : ℕ → Site d |
                  ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)}
                  (fun _ => (1 : ℝ)) Y ∂(centeredMassLaw d ν))|
            ≤ 4 * (κ * green d 0 0) / (δ * R ^ 2) *
                (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                  Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h))
              + efun R := by
  classical
  obtain ⟨hδ0, hδT⟩ := hδ
  have hd3 : 3 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hmono := monotone_meanOdometer_of_var hd1 ν hvar'
  have hG : (0 : ℝ) < green d 0 0 := lt_of_lt_of_le zero_lt_one (one_le_green hd3)
  have hGk : (0 : ℝ) < κ * green d 0 0 := mul_pos hκ hG
  set Gk : ℝ := κ * green d 0 0 with hGkdef
  set ε : ℝ := δ / (2 * T) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hεdef, div_lt_one (by positivity)]
    linarith
  set L : ℝ := Real.log (1 / ε) with hLdef
  have hL0 : (0 : ℝ) ≤ L := Real.log_nonneg ((one_le_div hε0).mpr hε1.le)
  set K : ℝ := max 1 (max (2 * Gk / δ) (2 * T / Gk)) with hKdef
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hK1 : 2 * Gk / δ ≤ K := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK2 : 2 * T / Gk ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hK1' : 2 * Gk ≤ K * δ := by
    rw [div_le_iff₀ hδ0] at hK1
    linarith
  have hK2' : 2 * T ≤ K * Gk := by
    rw [div_le_iff₀ hGk] at hK2
    linarith
  clear_value K L ε Gk
  have hsq : Tendsto (fun R : ℝ => R ^ 2 * T) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_mul_const hT
  refine exists_tendsto_zero_of_eventually
    (fun R e => ∀ i j : ℕ,
      (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
      (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
      ∀ X Y : ℕ → Site d,
        |(∫ σ, (Set.indicator {Z : ℕ → Site d |
              ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)} (fun _ => (1 : ℝ)) X) *
            (Set.indicator {Z : ℕ → Site d |
              ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)} (fun _ => (1 : ℝ)) Y)
            ∂(centeredMassLaw d ν))
          - (∫ σ, Set.indicator {Z : ℕ → Site d |
                ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)}
                (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) *
            (∫ σ, Set.indicator {Z : ℕ → Site d |
                ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)}
                (fun _ => (1 : ℝ)) Y ∂(centeredMassLaw d ν))|
          ≤ 4 * Gk / (δ * R ^ 2) *
              (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h))
            + e) ?_ ?_ hl
  · intro R i j _ _ X Y
    have hcount : (0 : ℝ) ≤ ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
        Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun h _ =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hcoef : (0 : ℝ) ≤ 4 * Gk / (δ * R ^ 2) := by positivity
    have hone := abs_cov_survival_le_one ν ⌊R ^ 2 * T⌋₊ i j X Y
    nlinarith [hcount, hcoef, hone]
  · intro e he
    set eta : ℝ := min (1 / 2) (e / (8 * (1 + L))) with hetadef
    have hetap : 0 < eta := lt_min (by norm_num) (by positivity)
    have hetahalf : eta ≤ 1 / 2 := min_le_left _ _
    have hetaE : eta ≤ e / (8 * (1 + L)) := min_le_right _ _
    have hetaL : 4 * (eta * (1 + L)) ≤ e / 2 := by
      have h1 : eta * (1 + L) ≤ e / (8 * (1 + L)) * (1 + L) :=
        mul_le_mul_of_nonneg_right hetaE (by linarith)
      have h2 : e / (8 * (1 + L)) * (1 + L) = e / 8 := by
        field_simp
      linarith
    set theta : ℝ := e / 6 with hthetadef
    have hthetap : 0 < theta := by positivity
    have hthetaE : 3 * theta ≤ e / 2 := by
      rw [hthetadef]
      linarith
    clear_value theta eta
    filter_upwards [hthresholds ε ⟨hε0, hε1⟩ eta hetap, hfactev theta hthetap K hK,
      (hsq.eventually_ge_atTop 2).filter_mono hl, (eventually_gt_atTop (0 : ℝ)).filter_mono hl] with R h_thr h_fact h_RT h_R0
    intro i j hi hj X Y
    have hRT0 : (0 : ℝ) < R ^ 2 * T := by linarith
    set n : ℕ := ⌊R ^ 2 * T⌋₊ with hndef
    have hnle : (n : ℝ) ≤ R ^ 2 * T := Nat.floor_le hRT0.le
    have hnlt : R ^ 2 * T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnhalf : R ^ 2 * T / 2 ≤ (n : ℝ) := by linarith
    have hR2 : (0 : ℝ) < R ^ 2 := by positivity
    have hδR : (0 : ℝ) < δ * R ^ 2 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have hilt : i < n := by
      have hlt : (i : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hlt
    have hjlt : j < n := by
      have hlt : (j : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hlt
    set M : ℕ := max i j with hMdef
    have hMle : (M : ℝ) ≤ (n : ℝ) - δ * R ^ 2 := by
      rcases le_total i j with h | h
      · rw [hMdef, max_eq_right h]
        exact hj
      · rw [hMdef, max_eq_left h]
        exact hi
    have hMlt : M < n := by
      have hlt : (M : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hlt
    have hεn : ε * (n : ℝ) ≤ δ * R ^ 2 := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)]
      nlinarith [hnle, hδ0.le, hR2.le]
    have hexp : (1 - ε) * (n : ℝ) = (n : ℝ) - ε * (n : ℝ) := by ring
    have hMn : (M : ℝ) ≤ (1 - ε) * (n : ℝ) := by
      rw [hexp]
      linarith
    have hiR : (i : ℝ) ≤ (M : ℝ) := by
      have : i ≤ M := le_max_left i j
      exact_mod_cast this
    have hjR : (j : ℝ) ≤ (M : ℝ) := by
      have : j ≤ M := le_max_right i j
      exact_mod_cast this
    have hin : (i : ℝ) ≤ (1 - ε) * (n : ℝ) := le_trans hiR hMn
    have hjn : (j : ℝ) ≤ (1 - ε) * (n : ℝ) := le_trans hjR hMn
    obtain ⟨b, hbdef, hb⟩ : ∃ b : ℕ → ℝ,
        (∀ r, b r = meanOdometer (centeredMassLaw d ν) (n - r - 1)) ∧ Antitone b :=
      ⟨fun r => meanOdometer (centeredMassLaw d ν) (n - r - 1), fun r => rfl,
        fun r s hrs => hmono (by omega)⟩
    have hanti : ∀ u v : ℝ, u ≤ v → (centeredMassLaw d ν).real
        {σ : Site d → ℝ | v < J σ 0} ≤ (centeredMassLaw d ν).real
        {σ : Site d → ℝ | u < J σ 0} := by
      intro u v huv
      exact measureReal_mono (fun σ hσ => lt_of_le_of_lt huv hσ) (measure_ne_top _ _)
    obtain ⟨hAw, hBw⟩ := window_of_thresholds n M hMlt ε hε0 hMn eta
      (fun m => |(m : ℝ) * ((centeredMassLaw d ν)
          {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
          (green d 0 0 * κ) - 1|)
      (fun m => (m : ℝ) * ((centeredMassLaw d ν)
          (symmDiff {σ | odometer σ m 0 = 0}
            {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal)
      (fun m => abs_nonneg _)
      (fun m => mul_nonneg (Nat.cast_nonneg m) ENNReal.toReal_nonneg) h_thr
    have hwin : ∀ r, r ≤ M → |((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        {σ : Site d → ℝ | b r < J σ 0} / Gk - 1| ≤ eta := by
      intro r hr
      have hAr := hAw r hr
      rw [hbdef r, hGkdef, measureReal_def, mul_comm κ (green d 0 0)]
      exact hAr
    have hthrM : ∀ r, r ≤ M → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta := by
      intro r hr
      have hBr := hBw r hr
      rw [hbdef r, measureReal_def]
      exact hBr
    have hnrpos : ∀ r, r ≤ M → (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
      intro r hr
      have h : 0 < n - r := by omega
      exact_mod_cast h
    have hnrge : ∀ r, r ≤ M → δ * R ^ 2 ≤ ((n - r : ℕ) : ℝ) := by
      intro r hr
      have hrn : r ≤ n := by omega
      rw [cast_nat_sub_eq n r hrn]
      have hrM : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hr
      linarith
    have hpiu : ∀ r, r ≤ M → (centeredMassLaw d ν).real
        {σ : Site d → ℝ | b r < J σ 0} ≤ 2 * Gk / (δ * R ^ 2) := by
      intro r hr
      have h1 := weight_le_of_abs_le (n - r) (by omega) Gk eta
        ((centeredMassLaw d ν).real {σ : Site d → ℝ | b r < J σ 0}) hGk (by linarith)
        (hwin r hr)
      refine le_trans h1 ?_
      rw [div_le_div_iff₀ (hnrpos r hr) hδR]
      have hstep := mul_le_mul_of_nonneg_left (hnrge r hr) (by positivity : (0:ℝ) ≤ 2 * Gk)
      linarith [hstep]
    have hpi0 : Gk / (2 * (n : ℝ)) ≤ (centeredMassLaw d ν).real
        {σ : Site d → ℝ | b 0 < J σ 0} := by
      have h := weight_ge_of_abs_le (n - 0) (by omega) Gk eta
        ((centeredMassLaw d ν).real {σ : Site d → ℝ | b 0 < J σ 0}) hGk hetahalf
        (hwin 0 (Nat.zero_le _))
      simpa [Nat.sub_zero] using h
    have hupall : ∀ t : ℝ, b M ≤ t → (centeredMassLaw d ν).real
        {σ : Site d → ℝ | t < J σ 0} ≤ K / R ^ 2 := by
      intro t ht
      refine le_trans (hanti (b M) t ht) (le_trans (hpiu M le_rfl) ?_)
      rw [div_le_div_iff₀ hδR hR2]
      have hstep := mul_le_mul_of_nonneg_right hK1' hR2.le
      linarith [hstep]
    have hlowall : ∀ t : ℝ, t ≤ b 0 → 1 / (K * R ^ 2) ≤ (centeredMassLaw d ν).real
        {σ : Site d → ℝ | t < J σ 0} := by
      intro t ht
      refine le_trans ?_ (le_trans hpi0 (hanti t (b 0) ht))
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 2 * (n : ℝ) ≤ 2 * (R ^ 2 * T) := by linarith
      have h2 : R ^ 2 * (2 * T) ≤ R ^ 2 * (K * Gk) := mul_le_mul_of_nonneg_left hK2' hR2.le
      linarith [h1, h2]
    have hiplus : ((i : ℝ) + 1) ≤ (n : ℝ) := by
      have hcast : ((i + 1 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hilt
      push_cast at hcast
      linarith
    have hjplus : ((j : ℝ) + 1) ≤ (n : ℝ) := by
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hjlt
      push_cast at hcast
      linarith
    have hn2 : 2 * (n : ℝ) ≤ 2 * T * R ^ 2 := by
      nlinarith [hnle, hT.le, hR2.le]
    have hcardX : ((((Finset.range (i + 1)).image X).card : ℕ) : ℝ) ≤ 2 * T * R ^ 2 := by
      have h1 : ((Finset.range (i + 1)).image X).card ≤ i + 1 :=
        le_trans Finset.card_image_le (by rw [Finset.card_range])
      have h2 : ((((Finset.range (i + 1)).image X).card : ℕ) : ℝ) ≤ ((i : ℝ) + 1) := by
        have h3 := (Nat.cast_le (α := ℝ)).mpr h1
        push_cast at h3
        linarith
      linarith [h2, hiplus, hn2, hn1]
    have hcardY : ((((Finset.range (j + 1)).image Y).card : ℕ) : ℝ) ≤ 2 * T * R ^ 2 := by
      have h1 : ((Finset.range (j + 1)).image Y).card ≤ j + 1 :=
        le_trans Finset.card_image_le (by rw [Finset.card_range])
      have h2 : ((((Finset.range (j + 1)).image Y).card : ℕ) : ℝ) ≤ ((j : ℝ) + 1) := by
        have h3 := (Nat.cast_le (α := ℝ)).mpr h1
        push_cast at h3
        linarith
      linarith [h2, hjplus, hn2, hn1]
    have hcardJ : ((((Finset.range (i + 1)).image X ∪
        (Finset.range (j + 1)).image Y).card : ℕ) : ℝ) ≤ 2 * T * R ^ 2 := by
      have h1 : ((Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y).card
          ≤ ((Finset.range (i + 1)).image X).card + ((Finset.range (j + 1)).image Y).card :=
        Finset.card_union_le _ _
      have h2 : ((Finset.range (i + 1)).image X).card ≤ i + 1 :=
        le_trans Finset.card_image_le (by rw [Finset.card_range])
      have h3 : ((Finset.range (j + 1)).image Y).card ≤ j + 1 :=
        le_trans Finset.card_image_le (by rw [Finset.card_range])
      have h4 : ((Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y).card
          ≤ (i + 1) + (j + 1) := by omega
      have h5 := (Nat.cast_le (α := ℝ)).mpr h4
      push_cast at h5
      linarith [h5, hiplus, hjplus, hn2]
    have hfactX := fact_on_finset ν J ((Finset.range (i + 1)).image X)
      (fun x => b (lastTimeOf i X x)) theta K R (2 * T * R ^ 2) h_fact hcardX
      (fun x _ => hupall _ (hb (le_trans (lastTimeOf_le i X x) (le_max_left i j))))
      (fun x _ => hlowall _ (hb (Nat.zero_le _)))
    have hfactY := fact_on_finset ν J ((Finset.range (j + 1)).image Y)
      (fun x => b (lastTimeOf j Y x)) theta K R (2 * T * R ^ 2) h_fact hcardY
      (fun x _ => hupall _ (hb (le_trans (lastTimeOf_le j Y x) (le_max_right i j))))
      (fun x _ => hlowall _ (hb (Nat.zero_le _)))
    have hfactJ := fact_on_finset ν J
      ((Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y)
      (jointLevel i j X Y b) theta K R (2 * T * R ^ 2) h_fact hcardJ
      (fun x _ => hupall _ (jointLevel_ge i j X Y b hb x))
      (fun x _ => hlowall _ (jointLevel_le_first i j X Y b hb x))
    have hHX := harmonic_window_le n i hilt ε hε0 hin
    have hHY := harmonic_window_le n j hjlt ε hε0 hjn
    rw [← hLdef] at hHX hHY
    have hmain := abs_cov_survival_le ν J b hb hshift hnull n i j hilt hjlt X Y eta theta
      (2 * Gk / (δ * R ^ 2)) (1 + L) (1 + L) hetap.le (by positivity)
      (fun r hr => hthrM r (le_trans hr (le_max_left i j)))
      (fun r hr => hthrM r (le_trans hr (le_max_right i j)))
      hHX hHY hfactJ hfactX hfactY
      (fun x => hpiu (lastTimeOf i X x) (le_trans (lastTimeOf_le i X x) (le_max_left i j)))
      (fun x => hpiu (lastTimeOf j Y x) (le_trans (lastTimeOf_le j Y x) (le_max_right i j)))
    have hcount : (0 : ℝ) ≤ ∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
        Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h) :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun h _ =>
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hcoef : 2 * (2 * Gk / (δ * R ^ 2)) = 4 * Gk / (δ * R ^ 2) := by ring
    rw [hcoef] at hmain
    linarith [hmain, hetaL, hthetaE, hcount]

/-- **`eq:dgt4-positive-path-covariance` in both branches of the threshold-field dichotomy of `sandpile.tex:5449-5450`**
(`sandpile.tex:5579-5605`).  The constant is `C = 4G(0,0)\kappa`. -/
theorem exists_cov_bound [NeZero d]
    (hNormal : External.NormalComparison) (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hatom : ∀ z : ℝ, ν {z} = 0)
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ((∀ σ x, J σ x = -(green d 0 0 * scenery d σ x)) ∨
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧
        ∀ σ x, J σ x = -infiniteGreenField (scenery d σ) x)))
    (T : ℝ) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (hthresholds : ∀ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ᶠ R : ℝ in atTop, ∀ m : ℕ, ⌈ε * (⌊R ^ 2 * T⌋₊ : ℝ)⌉₊ ≤ m → m ≤ ⌊R ^ 2 * T⌋₊ →
        |(m : ℝ) * ((centeredMassLaw d ν)
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0}).toReal /
            (green d 0 0 * κ) - 1| +
          (m : ℝ) * ((centeredMassLaw d ν)
            (symmDiff {σ | odometer σ m 0 = 0}
              {σ | meanOdometer (centeredMassLaw d ν) (m - 1) < J σ 0})).toReal ≤ η) :
    ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) T →
      ∃ efun : ℝ → ℝ, (∀ R, 0 ≤ efun R) ∧ Tendsto efun atTop (𝓝 0) ∧
        ∀ R : ℝ, ∀ i j : ℕ,
          (i : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          (j : ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) - δ * R ^ 2 →
          ∀ X Y : ℕ → Site d,
            |(∫ σ, (Set.indicator {Z : ℕ → Site d |
                  ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)} (fun _ => (1 : ℝ)) X) *
                (Set.indicator {Z : ℕ → Site d |
                  ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)} (fun _ => (1 : ℝ)) Y)
                ∂(centeredMassLaw d ν))
              - (∫ σ, Set.indicator {Z : ℕ → Site d |
                    ∀ r ≤ i, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - r) (Z r)}
                    (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) *
                (∫ σ, Set.indicator {Z : ℕ → Site d |
                    ∀ h ≤ j, 0 < odometer σ (⌊R ^ 2 * T⌋₊ - h) (Z h)}
                    (fun _ => (1 : ℝ)) Y ∂(centeredMassLaw d ν))|
              ≤ 4 * (κ * green d 0 0) / (δ * R ^ 2) *
                  (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
                    Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h))
                + efun R := by
  intro δ hδ
  rcases hJ with hind | ⟨⟨v, hvdef⟩, hgau⟩
  · refine exists_cov_bound_core hd ν hvar' J
      (fun t b y => measure_threshold_symmDiff_shift ν J hind t b y)
      (fun b => nullMeasurableSet_threshold_indep ν J hind 0 b) T hT κ hκ hthresholds
      ?_ δ hδ
    intro theta htheta K hK
    refine Filter.Eventually.of_forall (fun R m xs hxs _ lev _ _ => ?_)
    rw [indep_path_factorization ν J hind m xs hxs lev, sub_self, abs_zero]
    exact htheta.le
  · subst hvdef
    have hv : 0 < (v : ℝ) := by
      rcases lt_or_eq_of_le v.coe_nonneg with h | h
      · exact h
      · exfalso
        have hv0 : v = 0 := by
          have hz : (v : ℝ) = 0 := h.symm
          exact_mod_cast hz
        have hz := hatom 0
        rw [hv0, ProbabilityTheory.gaussianReal_zero_var] at hz
        rw [MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_singleton (0 : ℝ))] at hz
        exact one_ne_zero hz
    refine exists_cov_bound_core hd (gaussianReal 0 v) hvar' J
      (fun t b y => measure_threshold_symmDiff_shift_gauss hd v J hgau t b y)
      (fun b => nullMeasurableSet_threshold_of hd v J hgau 0 b) T hT κ hκ hthresholds
      ?_ δ hδ
    intro theta htheta K hK
    exact eventually_gauss_path_factorization_tails hNormal hd v hv J hgau (2 * T) K
      (by positivity) hK htheta

end Sandpile
