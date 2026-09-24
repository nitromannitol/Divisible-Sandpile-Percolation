/-
The covariance estimate of Step 3 of `lem:dgt4-path-survival` along one pair of paths
(`sandpile.tex:5584-5610`).

The paper's argument is four estimates in a row.  The threshold replacement
`eq:dgt4-path-contact-replacement` is applied to `X`, to `Y`, and to the two together
(`abs_measureReal_inter_sub_le`), which costs the two harmonic errors twice.  The
factorization `eq:dgt4-path-threshold-factorization` is applied to the sites visited by `X`,
to those visited by `Y`, and to those visited by at least one of them, which costs `\theta`
three times; here the events are read through their last visits indexed by SITES
(`Support/LinStep3Sites.lean`), the joint one carrying the smaller of the two levels at a
shared site.  The two factorized products then differ by at most the sum of the two
thresholds over the shared sites, which is the deterministic estimate of
`Support/LinStep3Product.lean`, and the passage from shared sites to shared times is its
counting lemma.  Finally the product of the two marginals is compared with the product of the
two factorizations by `|ab-a'b'|\leq|a-a'|+|b-b'|` for numbers in `[0,1]`.

The total is `C/(\delta R^2)\sum_{r\leq i}\sum_{h\leq j}\one_{\{X_r=Y_h\}}` plus the collected
uniform errors, which is `eq:dgt4-positive-path-covariance`.
-/
import Sandpile.Support.LinStep3Sites
import Sandpile.Support.LinStep2Pi
import Sandpile.Support.LinHarmonicWindow

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

theorem abs_mul_sub_mul_le (a b a' b' : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb'0 : 0 ≤ b') (hb'1 : b' ≤ 1) :
    |a * b - a' * b'| ≤ |a - a'| + |b - b'| := by
  have hid : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [hid]
  have h1 : |a * (b - b') + (a - a') * b'| ≤ |a * (b - b')| + |(a - a') * b'| :=
    abs_add_le _ _
  have h2 : |a * (b - b')| = |a| * |b - b'| := abs_mul _ _
  have h3 : |(a - a') * b'| = |a - a'| * |b'| := abs_mul _ _
  have h4 : |a| ≤ 1 := by rw [abs_of_nonneg ha0]; exact ha1
  have h5 : |b'| ≤ 1 := by rw [abs_of_nonneg hb'0]; exact hb'1
  have h6 : |a| * |b - b'| ≤ 1 * |b - b'| :=
    mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
  have h7 : |a - a'| * |b'| ≤ |a - a'| * 1 :=
    mul_le_mul_of_nonneg_left h5 (abs_nonneg _)
  linarith [h1, h2.le, h2.ge, h3.le, h3.ge, h6, h7]

/-- The joint survival indicator integrates to the measure of the intersection of the two
scenery events. -/
theorem integral_survival_mul_eq_measureReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n i j : ℕ) (X Y : ℕ → Site d) :
    ∫ σ, (Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
          (fun _ => (1 : ℝ)) X) *
        (Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
          (fun _ => (1 : ℝ)) Y) ∂(centeredMassLaw d ν)
      = (centeredMassLaw d ν).real
          ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
            {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}) := by
  have hfun : (fun σ : Site d → ℝ =>
      (Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
          (fun _ => (1 : ℝ)) X) *
        (Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
          (fun _ => (1 : ℝ)) Y))
      = Set.indicator ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
          {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)})
          (1 : (Site d → ℝ) → ℝ) := by
    funext σ
    by_cases h1 : ∀ r ≤ i, 0 < odometer σ (n - r) (X r) <;>
      by_cases h2 : ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)
    · rw [Set.indicator_of_mem (show X ∈ {Z : ℕ → Site d |
        ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)} from h1),
        Set.indicator_of_mem (show Y ∈ {Z : ℕ → Site d |
        ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)} from h2),
        Set.indicator_of_mem (show σ ∈ {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
          {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} from ⟨h1, h2⟩)]
      norm_num
    · rw [Set.indicator_of_notMem (show Y ∉ {Z : ℕ → Site d |
        ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)} from h2),
        Set.indicator_of_notMem (show σ ∉ {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
          {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} from fun hc => h2 hc.2)]
      ring
    · rw [Set.indicator_of_notMem (show X ∉ {Z : ℕ → Site d |
        ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)} from h1),
        Set.indicator_of_notMem (show σ ∉ {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
          {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} from fun hc => h1 hc.1)]
      ring
    · rw [Set.indicator_of_notMem (show X ∉ {Z : ℕ → Site d |
        ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)} from h1),
        Set.indicator_of_notMem (show σ ∉ {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
          {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)} from fun hc => h1 hc.1)]
      ring
  rw [hfun, integral_indicator_one
    ((measurableSet_survivalSet n i X).inter (measurableSet_survivalSet n j Y))]


/-- **The covariance estimate of Step 3 along one pair of paths**
(`sandpile.tex:5579-5605`). -/
theorem abs_cov_survival_le [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (hnull : ∀ c : ℝ, NullMeasurableSet {σ : Site d → ℝ | c < J σ 0} (centeredMassLaw d ν))
    (n i j : ℕ) (hi : i < n) (hj : j < n) (X Y : ℕ → Site d)
    (eta theta cbd HX HY : ℝ) (heta0 : 0 ≤ eta) (hcbd0 : 0 ≤ cbd)
    (hthrX : ∀ r, r ≤ i → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hthrY : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hHX : ∑ r ∈ Finset.range (i + 1), (((n - r : ℕ) : ℝ))⁻¹ ≤ HX)
    (hHY : ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ ≤ HY)
    (hfactJ : |(centeredMassLaw d ν).real
          (⋂ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
            {σ : Site d → ℝ | J σ x ≤ jointLevel i j X Y b x})
        - ∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
            (centeredMassLaw d ν).real
              {σ : Site d → ℝ | J σ 0 ≤ jointLevel i j X Y b x}| ≤ theta)
    (hfactX : |(centeredMassLaw d ν).real
          (⋂ x ∈ (Finset.range (i + 1)).image X,
            {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf i X x)})
        - ∏ x ∈ (Finset.range (i + 1)).image X, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ b (lastTimeOf i X x)}| ≤ theta)
    (hfactY : |(centeredMassLaw d ν).real
          (⋂ x ∈ (Finset.range (j + 1)).image Y,
            {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf j Y x)})
        - ∏ x ∈ (Finset.range (j + 1)).image Y, (centeredMassLaw d ν).real
            {σ : Site d → ℝ | J σ 0 ≤ b (lastTimeOf j Y x)}| ≤ theta)
    (hpX : ∀ x : Site d, (centeredMassLaw d ν).real
        {σ : Site d → ℝ | b (lastTimeOf i X x) < J σ 0} ≤ cbd)
    (hpY : ∀ x : Site d, (centeredMassLaw d ν).real
        {σ : Site d → ℝ | b (lastTimeOf j Y x) < J σ 0} ≤ cbd) :
    |(∫ σ, (Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
            (fun _ => (1 : ℝ)) X) *
          (Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
            (fun _ => (1 : ℝ)) Y) ∂(centeredMassLaw d ν))
        - (∫ σ, Set.indicator {Z : ℕ → Site d | ∀ r ≤ i, 0 < odometer σ (n - r) (Z r)}
              (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) *
          (∫ σ, Set.indicator {Z : ℕ → Site d | ∀ h ≤ j, 0 < odometer σ (n - h) (Z h)}
              (fun _ => (1 : ℝ)) Y ∂(centeredMassLaw d ν))|
      ≤ 2 * cbd * (∑ r ∈ Finset.range (i + 1), ∑ h ∈ Finset.range (j + 1),
            Set.indicator {p : ℕ × ℕ | X p.1 = Y p.2} (fun _ => (1 : ℝ)) (r, h))
        + (2 * (eta * HX) + 2 * (eta * HY) + 3 * theta) := by
  classical
  set P : Measure (Site d → ℝ) := centeredMassLaw d ν with hPdef
  set p : Site d → ℝ := fun x => P.real {σ : Site d → ℝ | b (lastTimeOf i X x) < J σ 0} with hp
  set q : Site d → ℝ := fun x => P.real {σ : Site d → ℝ | b (lastTimeOf j Y x) < J σ 0} with hq
  have hcompl : ∀ t : ℝ, P.real {σ : Site d → ℝ | J σ 0 ≤ t} = 1 - P.real {σ | t < J σ 0} :=
    fun t => measureReal_le_eq_one_sub P (fun σ => J σ 0) t (hnull t)
  have hanti : Antitone (fun t : ℝ => P.real {σ : Site d → ℝ | t < J σ 0}) :=
    thresholdProb_antitone P (fun σ => J σ 0)
  have hp0 : ∀ x, 0 ≤ p x := fun x => measureReal_nonneg
  have hq0 : ∀ x, 0 ≤ q x := fun x => measureReal_nonneg
  have hp1 : ∀ x, p x ≤ 1 := fun x => measureReal_le_one
  have hq1 : ∀ x, q x ≤ 1 := fun x => measureReal_le_one
  -- the threshold replacement along each path
  have hposX : ∀ r ∈ Finset.range (i + 1), (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
    intro r hr
    have := Finset.mem_range.mp hr
    have h : 0 < n - r := by omega
    exact_mod_cast h
  have hposY : ∀ r ∈ Finset.range (j + 1), (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
    intro r hr
    have := Finset.mem_range.mp hr
    have h : 0 < n - r := by omega
    exact_mod_cast h
  have hsymX : ∀ r ∈ Finset.range (i + 1), ((n - r : ℕ) : ℝ) *
      P.real (symmDiff {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)}
        {σ : Site d → ℝ | J σ (X r) ≤ b r}) ≤ eta := by
    intro r hr
    have hrr : r ≤ i := by
      have := Finset.mem_range.mp hr
      omega
    rw [symmDiff_survival_threshold (n - r) (X r) (b r) J, measureReal_def,
      hshift (n - r) (b r) (X r), ← measureReal_def]
    exact hthrX r hrr
  have hsymY : ∀ r ∈ Finset.range (j + 1), ((n - r : ℕ) : ℝ) *
      P.real (symmDiff {σ : Site d → ℝ | 0 < odometer σ (n - r) (Y r)}
        {σ : Site d → ℝ | J σ (Y r) ≤ b r}) ≤ eta := by
    intro r hr
    have hrr : r ≤ j := by
      have := Finset.mem_range.mp hr
      omega
    rw [symmDiff_survival_threshold (n - r) (Y r) (b r) J, measureReal_def,
      hshift (n - r) (b r) (Y r), ← measureReal_def]
    exact hthrY r hrr
  have hsumX : ∑ r ∈ Finset.range (i + 1),
      P.real (symmDiff {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)}
        {σ : Site d → ℝ | J σ (X r) ≤ b r}) ≤ eta * HX := by
    refine le_trans (sum_le_of_mul_le n i eta _ hposX hsymX) ?_
    exact mul_le_mul_of_nonneg_left hHX heta0
  have hsumY : ∑ r ∈ Finset.range (j + 1),
      P.real (symmDiff {σ : Site d → ℝ | 0 < odometer σ (n - r) (Y r)}
        {σ : Site d → ℝ | J σ (Y r) ≤ b r}) ≤ eta * HY := by
    refine le_trans (sum_le_of_mul_le n j eta _ hposY hsymY) ?_
    exact mul_le_mul_of_nonneg_left hHY heta0
  -- the events as intersections
  have hCXeq : {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)}
      = ⋂ r ∈ Finset.range (i + 1), {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)} :=
    setOf_forall_le_eq_iInter i (fun r σ => 0 < odometer σ (n - r) (X r))
  have hCYeq : {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}
      = ⋂ r ∈ Finset.range (j + 1), {σ : Site d → ℝ | 0 < odometer σ (n - r) (Y r)} :=
    setOf_forall_le_eq_iInter j (fun r σ => 0 < odometer σ (n - r) (Y r))
  have hTXeq : (⋂ r ∈ Finset.range (i + 1), {σ : Site d → ℝ | J σ (X r) ≤ b r})
      = ⋂ x ∈ (Finset.range (i + 1)).image X,
          {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf i X x)} :=
    iInter_single_eq_image i X b hb (fun σ x => J σ x)
  have hTYeq : (⋂ r ∈ Finset.range (j + 1), {σ : Site d → ℝ | J σ (Y r) ≤ b r})
      = ⋂ x ∈ (Finset.range (j + 1)).image Y,
          {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf j Y x)} :=
    iInter_single_eq_image j Y b hb (fun σ x => J σ x)
  have hTJeq := iInter_joint_eq_image i j X Y b hb (fun (σ : Site d → ℝ) x => J σ x)
  -- the products
  have hprodX : ∏ x ∈ (Finset.range (i + 1)).image X,
      P.real {σ : Site d → ℝ | J σ 0 ≤ b (lastTimeOf i X x)}
      = ∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x) :=
    Finset.prod_congr rfl fun x _ => hcompl _
  have hprodY : ∏ x ∈ (Finset.range (j + 1)).image Y,
      P.real {σ : Site d → ℝ | J σ 0 ≤ b (lastTimeOf j Y x)}
      = ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x) :=
    Finset.prod_congr rfl fun x _ => hcompl _
  have hjfac : ∀ x : Site d, P.real {σ : Site d → ℝ | J σ 0 ≤ jointLevel i j X Y b x}
      = (if x ∈ (Finset.range (i + 1)).image X then
          (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
        else 1 - q x) := by
    intro x
    rw [hcompl, jointLevel]
    by_cases h1 : x ∈ (Finset.range (i + 1)).image X
    · by_cases h2 : x ∈ (Finset.range (j + 1)).image Y
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        have hmax := antitone_min_eq_max (fun t : ℝ => P.real {σ : Site d → ℝ | t < J σ 0})
          hanti (b (lastTimeOf i X x)) (b (lastTimeOf j Y x))
        rw [hmax]
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
    · rw [if_neg h1, if_neg h1]
  have hprodJ : ∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
      P.real {σ : Site d → ℝ | J σ 0 ≤ jointLevel i j X Y b x}
      = ∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
        (if x ∈ (Finset.range (i + 1)).image X then
          (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
        else 1 - q x) :=
    Finset.prod_congr rfl fun x _ => hjfac x
  -- the three chains
  have hXchain : |P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)}
      - ∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)| ≤ eta * HX + theta := by
    have h1 := abs_measureReal_iInter_sub_le_all P (Finset.range (i + 1))
      (fun r => {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)})
      (fun r => {σ : Site d → ℝ | J σ (X r) ≤ b r})
    rw [← hCXeq, hTXeq] at h1
    rw [hprodX] at hfactX
    have htri := abs_sub_le (P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)})
      (P.real (⋂ x ∈ (Finset.range (i + 1)).image X,
        {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf i X x)}))
      (∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x))
    linarith [h1, hsumX, hfactX, htri]
  have hYchain : |P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}
      - ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x)| ≤ eta * HY + theta := by
    have h1 := abs_measureReal_iInter_sub_le_all P (Finset.range (j + 1))
      (fun r => {σ : Site d → ℝ | 0 < odometer σ (n - r) (Y r)})
      (fun r => {σ : Site d → ℝ | J σ (Y r) ≤ b r})
    rw [← hCYeq, hTYeq] at h1
    rw [hprodY] at hfactY
    have htri := abs_sub_le (P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)})
      (P.real (⋂ x ∈ (Finset.range (j + 1)).image Y,
        {σ : Site d → ℝ | J σ x ≤ b (lastTimeOf j Y x)}))
      (∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x))
    linarith [h1, hsumY, hfactY, htri]
  have hJchain : |P.real ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
        {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)})
      - ∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
        (if x ∈ (Finset.range (i + 1)).image X then
          (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
        else 1 - q x)| ≤ (eta * HX + eta * HY) + theta := by
    have h1 := abs_measureReal_inter_sub_le P (Finset.range (i + 1)) (Finset.range (j + 1))
      (fun r => {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)})
      (fun r => {σ : Site d → ℝ | J σ (X r) ≤ b r})
      (fun r => {σ : Site d → ℝ | 0 < odometer σ (n - r) (Y r)})
      (fun r => {σ : Site d → ℝ | J σ (Y r) ≤ b r})
    rw [← hCXeq, ← hCYeq, hTJeq] at h1
    rw [hprodJ] at hfactJ
    have htri := abs_sub_le (P.real ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
        {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}))
      (P.real (⋂ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
        {σ : Site d → ℝ | J σ x ≤ jointLevel i j X Y b x}))
      (∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
        (if x ∈ (Finset.range (i + 1)).image X then
          (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
        else 1 - q x))
    linarith [h1, hsumX, hsumY, hfactJ, htri]
  -- the separated product and the shared sites
  have hsep := abs_prod_joint_sub_prod_sep_le_count i j X Y p q cbd hp0 hp1 hq0 hq1 hcbd0
    (fun x => hpX x) (fun x => hpY x)
  have hqprod0 : (0 : ℝ) ≤ ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x) :=
    Finset.prod_nonneg fun x _ => by linarith [hq1 x]
  have hqprod1 : ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x) ≤ 1 :=
    Finset.prod_le_one (fun x _ => by linarith [hq1 x]) (fun x _ => by linarith [hq0 x])
  rw [integral_survival_mul_eq_measureReal ν n i j X Y,
    integral_survival_eq_measureReal ν n i X, integral_survival_eq_measureReal ν n j Y]
  have hmul := abs_mul_sub_mul_le
    (P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)})
    (P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)})
    (∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x))
    (∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x))
    measureReal_nonneg measureReal_le_one hqprod0 hqprod1
  have htri1 := abs_sub_le
    (P.real ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
      {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}))
    (∏ x ∈ (Finset.range (i + 1)).image X ∪ (Finset.range (j + 1)).image Y,
      (if x ∈ (Finset.range (i + 1)).image X then
        (if x ∈ (Finset.range (j + 1)).image Y then 1 - max (p x) (q x) else 1 - p x)
      else 1 - q x))
    ((∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)) *
      ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x))
  have htri2 := abs_sub_le
    (P.real ({σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} ∩
      {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}))
    ((∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)) *
      ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x))
    (P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} *
      P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)})
  have habs : |(∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)) *
        (∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x))
      - P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} *
        P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}|
      = |P.real {σ : Site d → ℝ | ∀ r ≤ i, 0 < odometer σ (n - r) (X r)} *
          P.real {σ : Site d → ℝ | ∀ h ≤ j, 0 < odometer σ (n - h) (Y h)}
        - (∏ x ∈ (Finset.range (i + 1)).image X, (1 - p x)) *
          ∏ x ∈ (Finset.range (j + 1)).image Y, (1 - q x)| := abs_sub_comm _ _
  linarith [hJchain, hsep, hmul, htri1, htri2, habs.le, habs.ge, hXchain, hYchain]

/-- **From an eventual bound at every target to a vanishing error function.**
The scale filter may be any filter below `atTop`. At each scale choose the
smallest admissible reciprocal with index bounded by the ceiling of the scale;
any fixed reciprocal is eventually an admissible candidate. -/
theorem exists_tendsto_zero_of_eventually {l : Filter ℝ}
    (F : ℝ → ℝ → Prop) (hbig : ∀ R : ℝ, F R 1)
    (hev : ∀ e : ℝ, 0 < e → ∀ᶠ R : ℝ in l, F R e)
    (hl : l ≤ atTop := by exact le_rfl) :
    ∃ efun : ℝ → ℝ, (∀ R, 0 ≤ efun R) ∧ Tendsto efun l (𝓝 0) ∧
      ∀ R, F R (efun R) := by
  classical
  let N : ℝ → ℕ := fun R => Nat.findGreatest
    (fun k => F R (1 / ((k : ℝ) + 1))) ⌈R⌉₊
  refine ⟨fun R => if h : ∃ k : ℕ, k ≤ ⌈R⌉₊ ∧ F R (1 / ((k : ℝ) + 1))
      then 1 / ((N R : ℝ) + 1) else 1,
    fun R => by dsimp only; split_ifs <;> positivity, ?_, ?_⟩
  · rw [NormedAddGroup.tendsto_nhds_zero]
    intro e he
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / e)
    filter_upwards [(eventually_ge_atTop (k : ℝ)).filter_mono hl,
      hev (1 / ((k : ℝ) + 1)) (by positivity)] with R hR hF
    have hkc : k ≤ ⌈R⌉₊ := by
      exact_mod_cast hR.trans (Nat.le_ceil R)
    rw [dif_pos ⟨k, hkc, hF⟩]
    have hNk : k ≤ N R := Nat.le_findGreatest hkc hF
    have hNkR : (k : ℝ) ≤ (N R : ℝ) := by exact_mod_cast hNk
    have hle : 1 / ((N R : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hlt : 1 / ((k : ℝ) + 1) < e := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ he] at hk
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle.trans_lt hlt
  · intro R
    dsimp only
    split_ifs with h
    · obtain ⟨k, hk, hF⟩ := h
      exact Nat.findGreatest_spec (P := fun k => F R (1 / ((k : ℝ) + 1))) hk hF
    · exact hbig R

end Sandpile
