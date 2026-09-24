/-
The deviation estimate that the first step of the heavy-tailed case needs
(`sandpile.tex:5361-5377`), from the Bernstein concentration inequality of
`Sandpile.Support.Dgt4Bernstein`.

The truncated field has independent coordinates whose weighted contributions lie in a
bounded interval, but its one-site laws differ from site to site and have no exponential
moment uniform in the site.  The concentration inequality is therefore applied not to the
truncated field but to the ORIGINAL i.i.d. field composed with the truncation: the map
`y \mapsto \max(y,-t/c_z)` is one-Lipschitz, so the composed functional has the same
coordinate Lipschitz coefficients, and clamping it from above at a point beyond which the
scenery puts no mass makes it bounded without changing it almost surely.
-/
import Sandpile.Support.Dgt4Bernstein
import Sandpile.Support.Dgt4PairKernel

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The value `y` clamped into `[lo, hi]`. -/
noncomputable def clampAt (lo hi y : ℝ) : ℝ := max (min y hi) lo

theorem clampAt_le (lo hi y : ℝ) (h : lo ≤ hi) : clampAt lo hi y ≤ hi :=
  max_le (min_le_right _ _) h

theorem le_clampAt (lo hi y : ℝ) : lo ≤ clampAt lo hi y := le_max_right _ _

/-- Clamping is one-Lipschitz. -/
theorem abs_clampAt_sub_le (lo hi y y' : ℝ) :
    |clampAt lo hi y - clampAt lo hi y'| ≤ |y - y'| := by
  rw [clampAt, clampAt]
  refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
  rcases le_total y y' with h | h
  · rw [abs_of_nonpos (by simp [min_le_min h le_rfl]),
      abs_of_nonpos (by linarith : y - y' ≤ 0)]
    have h1 : y' ⊓ hi - y ⊓ hi ≤ y' - y := by
      rcases le_total y' hi with h2 | h2
      · rw [min_eq_left h2, min_eq_left (le_trans h h2)]
      · rw [min_eq_right h2]
        rcases le_total y hi with h3 | h3
        · rw [min_eq_left h3]; linarith
        · rw [min_eq_right h3]; linarith
    linarith
  · rw [abs_of_nonneg (by simp [min_le_min h le_rfl]),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ y - y')]
    have h1 : y ⊓ hi - y' ⊓ hi ≤ y - y' := by
      rcases le_total y hi with h2 | h2
      · rw [min_eq_left h2, min_eq_left (le_trans h h2)]
      · rw [min_eq_right h2]
        rcases le_total y' hi with h3 | h3
        · rw [min_eq_left h3]; linarith
        · rw [min_eq_right h3]; linarith
    linarith

/-- Clamped values move by at most the length of the interval. -/
theorem abs_clampAt_sub_le_range (lo hi y y' : ℝ) (h : lo ≤ hi) :
    |clampAt lo hi y - clampAt lo hi y'| ≤ hi - lo := by
  rw [abs_sub_le_iff]
  constructor <;>
    [linarith [clampAt_le lo hi y h, le_clampAt lo hi y'];
     linarith [clampAt_le lo hi y' h, le_clampAt lo hi y]]

/-- Below the upper level, clamping is the truncation from below. -/
theorem clampAt_eq_max (lo hi y : ℝ) (h : y ≤ hi) : clampAt lo hi y = max y lo := by
  rw [clampAt, min_eq_left h]

theorem abs_clampAt_le (lo hi y : ℝ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) :
    |clampAt lo hi y| ≤ hi - lo := by
  have h1 := clampAt_le lo hi y (le_trans hlo hhi)
  have h2 := le_clampAt lo hi y
  rcases le_total 0 (clampAt lo hi y) with h3 | h3
  · rw [abs_of_nonneg h3]; linarith
  · rw [abs_of_nonpos h3]; linarith

theorem measurable_clampAt (lo hi : ℝ) : Measurable (clampAt lo hi) :=
  (measurable_id.min measurable_const).max measurable_const

/-- `G(0,z)/G(0,0)\leq1`. -/
theorem greenRatioWeight_le_one (hd : 5 ≤ d) (z : Sandpile.Site d) :
    greenRatioWeight d z ≤ 1 := by
  rw [greenRatioWeight, greenRatio_eq_hitProb (by omega) z]
  exact LatticeProb.srwHitProb_le_one (by omega) z

/-- **The deviation estimate of `sandpile.tex:5364-5372`.**  A functional of the field that
reads only the box, moves by at most `\ell_z` when the scenery at `z` moves by one, and has
`\ell_z\leq G(0,z)/G(0,0)`, satisfies at the field truncated from below at `-t/c_z` a
Bernstein bound whose linear term is the truncation level and whose quadratic term is the
variance of the scenery times the square sum of the coefficients. -/
theorem measure_trunc_le_of_mean (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsqν : Integrable (fun y : ℝ => y ^ 2) ν)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    (n : ℕ) (Φ : (Sandpile.Site d → ℝ) → ℝ) (hΦm : Measurable Φ)
    (hΦbox : ∀ ζ η : Sandpile.Site d → ℝ,
      (∀ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1), ζ z = η z) → Φ ζ = Φ η)
    (ℓ : Sandpile.Site d → ℝ) (hℓ0 : ∀ z, 0 ≤ ℓ z)
    (hℓc : ∀ z, ℓ z ≤ greenRatioWeight d z)
    (hΦlip : ∀ (ζ : Sandpile.Site d → ℝ) (z : Sandpile.Site d) (v : ℝ),
      |Φ ζ - Φ (Function.update ζ z v)| ≤ ℓ z * |ζ z - v|)
    (S : ℝ) (hS : ∑ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1), ℓ z ^ 2 ≤ S)
    (t lam ρ r : ℝ) (ht : 0 < t) (hlam : 0 < lam) (hlb : lam * (hi + t) < 3)
    (hΦint : Integrable Φ (LatticeProb.iidLaw d ν))
    (hmono : ∀ ζ, Φ ζ ≤ Φ (truncScenery (greenRatioWeight d) t ζ))
    (hmean : ρ + r ≤ ∫ ζ, Φ ζ ∂(LatticeProb.iidLaw d ν)) :
    (LatticeProb.iidLaw d ν)
        {ζ | Φ (truncScenery (greenRatioWeight d) t ζ) ≤ ρ}
      ≤ ENNReal.ofReal (Real.exp (-(lam * r) +
          lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * ((∫ y, y ^ 2 ∂ν) * S))) := by
  classical
  have hd1 : 1 ≤ d := by omega
  set c : Sandpile.Site d → ℝ := greenRatioWeight d with hcdef
  have hcnn : ∀ z, 0 ≤ c z := greenRatioWeight_nonneg hd
  have hc1 : ∀ z, c z ≤ 1 := greenRatioWeight_le_one hd
  set sB : Finset (Sandpile.Site d) := Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)
    with hsBdef
  set e : Fin sB.card → Sandpile.Site d := Sandpile.siteEnum sB with hedef
  have hein : Function.Injective e := Sandpile.siteEnum_injective sB
  set lo : Fin sB.card → ℝ := fun i => -(t / c (e i)) with hlodef
  have hlo0 : ∀ i, lo i ≤ 0 := by
    intro i
    rw [hlodef, neg_nonpos]
    exact div_nonneg ht.le (hcnn _)
  set b : ℝ := hi + t with hbdef
  have hb0 : (0 : ℝ) ≤ b := by rw [hbdef]; linarith
  -- the oscillation of one coordinate is at most `b`
  have hosc0 : ∀ i, ℓ (e i) * (hi - lo i) ≤ b := by
    intro i
    have hl := hℓ0 (e i)
    have hlc := hℓc (e i)
    by_cases hc0 : c (e i) = 0
    · have : ℓ (e i) = 0 := le_antisymm (by rw [← hc0]; exact hlc) hl
      rw [this, zero_mul, hbdef]
      linarith
    · have hcpos : 0 < c (e i) := lt_of_le_of_ne (hcnn _) (Ne.symm hc0)
      have h1 : ℓ (e i) * hi ≤ hi := by
        have : ℓ (e i) ≤ 1 := le_trans hlc (hc1 _)
        nlinarith
      have h2 : ℓ (e i) * (t / c (e i)) ≤ t := by
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hcpos]
        nlinarith
      rw [hlodef]
      simp only [sub_neg_eq_add, mul_add, hbdef]
      linarith
  -- the finite-coordinate functional
  set G : (Fin sB.card → ℝ) → ℝ := fun ξ => Φ (Sandpile.siteExtend sB ξ) with hGdef
  have hGm : Measurable G := hΦm.comp (Sandpile.measurable_siteExtend sB)
  have hev : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card),
      Sandpile.siteExtend sB ξ (e i) = ξ i := by
    intro ξ i
    simp [Sandpile.siteExtend, Sandpile.siteEnum, hedef]
  have hGlip : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card) (v : ℝ),
      |G ξ - G (Function.update ξ i v)| ≤ ℓ (e i) * |ξ i - v| := by
    intro ξ i v
    rw [hGdef]
    simp only
    rw [Sandpile.siteExtend_update]
    have h := hΦlip (Sandpile.siteExtend sB ξ) (e i) v
    rw [hev ξ i] at h
    exact h
  set F : (Fin sB.card → ℝ) → ℝ := fun ξ => G (fun i => clampAt (lo i) hi (ξ i)) with hFdef
  have hclampupd : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card) (v : ℝ),
      (fun j => clampAt (lo j) hi (Function.update ξ i v j))
        = Function.update (fun j => clampAt (lo j) hi (ξ j)) i (clampAt (lo i) hi v) := by
    intro ξ i v
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have hFm : Measurable F :=
    hGm.comp (measurable_pi_lambda _ fun i => (measurable_clampAt _ _).comp (measurable_pi_apply i))
  have hFlip : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card) (v : ℝ),
      |F ξ - F (Function.update ξ i v)| ≤ ℓ (e i) * |ξ i - v| := by
    intro ξ i v
    rw [hFdef]
    simp only
    rw [hclampupd ξ i v]
    refine le_trans (hGlip _ i _) ?_
    exact mul_le_mul_of_nonneg_left (abs_clampAt_sub_le _ _ _ _) (hℓ0 _)
  have hFosc : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card) (v : ℝ),
      |F ξ - F (Function.update ξ i v)| ≤ b := by
    intro ξ i v
    rw [hFdef]
    simp only
    rw [hclampupd ξ i v]
    refine le_trans (hGlip _ i _) (le_trans ?_ (hosc0 i))
    exact mul_le_mul_of_nonneg_left
      (abs_clampAt_sub_le_range _ _ _ _ (le_trans (hlo0 i) hhi)) (hℓ0 _)
  have hFbd : ∀ ξ, |F ξ| ≤ |G fun _ => 0| + (sB.card : ℝ) * b := by
    intro ξ
    have hsum := LatticeProb.abs_sub_le_sum_lip G (fun i => ℓ (e i)) hGlip
      (fun i => clampAt (lo i) hi (ξ i)) (fun _ => 0)
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin sB.card)),
        ℓ (e i) * |clampAt (lo i) hi (ξ i) - 0| ≤ b := by
      intro i _
      rw [sub_zero]
      refine le_trans ?_ (hosc0 i)
      exact mul_le_mul_of_nonneg_left (abs_clampAt_le _ _ _ (hlo0 i) hhi) (hℓ0 _)
    have hcard : ∑ _i : Fin sB.card, b = (sB.card : ℝ) * b := by
      simp [mul_comm]
    have h2 : |F ξ - G fun _ => 0| ≤ (sB.card : ℝ) * b :=
      le_trans hsum (le_trans (Finset.sum_le_sum hterm) (le_of_eq hcard))
    have h3 : |F ξ| ≤ |F ξ - G fun _ => 0| + |G fun _ => 0| := by
      have := abs_add_le (F ξ - G fun _ => 0) (G fun _ => 0)
      simpa using this
    linarith
  -- the scenery is almost surely below the upper level on the box
  have hnull : ∀ z : Sandpile.Site d,
      (LatticeProb.iidLaw d ν) {ζ : Sandpile.Site d → ℝ | hi < ζ z} = 0 := by
    intro z
    have hmapz : (LatticeProb.iidLaw d ν).map (fun ζ : Sandpile.Site d → ℝ => ζ z) = ν :=
      MeasureTheory.Measure.infinitePi_map_eval (fun _ : Sandpile.Site d => ν) z
    have hset : {ζ : Sandpile.Site d → ℝ | hi < ζ z}
        = (fun ζ : Sandpile.Site d → ℝ => ζ z) ⁻¹' (Set.Ioi hi) := rfl
    rw [hset, ← MeasureTheory.Measure.map_apply (measurable_pi_apply z) measurableSet_Ioi,
      hmapz]
    exact hνhi
  set Bset : Set (Sandpile.Site d → ℝ) := {ζ | ∀ z ∈ sB, ζ z ≤ hi} with hBdef
  have hBnull : (LatticeProb.iidLaw d ν) Bsetᶜ = 0 := by
    have hsubs : Bsetᶜ ⊆ ⋃ z ∈ sB, {ζ : Sandpile.Site d → ℝ | hi < ζ z} := by
      intro ζ hζ
      simp only [hBdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hζ
      obtain ⟨z, hz, hlt⟩ := hζ
      exact Set.mem_biUnion hz (by simpa using lt_of_not_ge hlt)
    have hle : (LatticeProb.iidLaw d ν) Bsetᶜ ≤ 0 := by
      refine le_trans (measure_mono hsubs) ?_
      refine le_trans (measure_biUnion_finset_le sB _) ?_
      simp [hnull]
    exact nonpos_iff_eq_zero.mp hle
  -- on that event the clamped functional is the truncated one
  have hkey : ∀ ζ : Sandpile.Site d → ℝ, (∀ z ∈ sB, ζ z ≤ hi) →
      F (fun i => ζ (e i)) = Φ (truncScenery c t ζ) := by
    intro ζ hζ
    have h1 : G (fun i => truncScenery c t ζ (e i)) = Φ (truncScenery c t ζ) := by
      rw [hGdef]
      exact hΦbox _ _ fun z hz => Sandpile.siteExtend_siteEnum sB _ hz
    rw [← h1, hFdef]
    simp only
    have hz : ∀ i : Fin sB.card,
        clampAt (lo i) hi (ζ (e i)) = truncScenery c t ζ (e i) ∨ ℓ (e i) = 0 := by
      intro i
      by_cases hc0 : c (e i) = 0
      · right
        exact le_antisymm (by rw [← hc0]; exact hℓc _) (hℓ0 _)
      · left
        rw [clampAt_eq_max _ _ _ (hζ _ (Sandpile.siteEnum_mem sB i)), truncScenery,
          if_neg hc0, hlodef]
    have hsum := LatticeProb.abs_sub_le_sum_lip G (fun i => ℓ (e i)) hGlip
      (fun i => clampAt (lo i) hi (ζ (e i))) (fun i => truncScenery c t ζ (e i))
    have hzero : ∑ i : Fin sB.card, ℓ (e i) *
        |clampAt (lo i) hi (ζ (e i)) - truncScenery c t ζ (e i)| = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hz i with h | h
      · rw [h, sub_self, abs_zero, mul_zero]
      · rw [h, zero_mul]
    rw [hzero] at hsum
    have hge := abs_nonneg (G (fun i => clampAt (lo i) hi (ζ (e i)))
      - G fun i => truncScenery c t ζ (e i))
    have heq := abs_eq_zero.mp (le_antisymm hsum hge)
    linarith
  have hmp := LatticeProb.measurePreserving_pick _ ν e hein
  have hmeas1 : MeasurableSet {ξ : Fin sB.card → ℝ | F ξ ≤ ρ} :=
    measurableSet_le hFm measurable_const
  have htrans : (LatticeProb.iidLaw d ν) {ζ | Φ (truncScenery c t ζ) ≤ ρ}
      ≤ (Measure.pi fun _ : Fin sB.card => ν) {ξ : Fin sB.card → ℝ | F ξ ≤ ρ} := by
    have hsub2 : {ζ : Sandpile.Site d → ℝ | Φ (truncScenery c t ζ) ≤ ρ}
        ⊆ ((fun ζ : Sandpile.Site d → ℝ => fun i => ζ (e i)) ⁻¹'
            {ξ : Fin sB.card → ℝ | F ξ ≤ ρ}) ∪ Bsetᶜ := by
      intro ζ hζ
      by_cases hB : ζ ∈ Bset
      · left
        show F (fun i => ζ (e i)) ≤ ρ
        rw [hkey ζ hB]
        exact hζ
      · right; exact hB
    refine le_trans (measure_mono hsub2) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hBnull, add_zero, hmp.measure_preimage hmeas1.nullMeasurableSet]
  have hae : ∀ᵐ ζ ∂(LatticeProb.iidLaw d ν), ζ ∈ Bset := by
    rw [ae_iff]
    exact hBnull
  have hFpickint : Integrable (fun ζ : Sandpile.Site d → ℝ => F fun i => ζ (e i))
      (LatticeProb.iidLaw d ν) :=
    Integrable.mono' (integrable_const (|G fun _ => 0| + (sB.card : ℝ) * b))
      ((hFm.comp hmp.measurable)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs]; exact hFbd _)
  have hmeanF : ∫ ζ, Φ ζ ∂(LatticeProb.iidLaw d ν)
      ≤ ∫ ξ, F ξ ∂(Measure.pi fun _ : Fin sB.card => ν) := by
    rw [← Sandpile.integral_pick ν e hein F hFm.aestronglyMeasurable]
    refine integral_mono_ae hΦint hFpickint ?_
    filter_upwards [hae] with ζ hζ
    rw [hkey ζ hζ]
    exact hmono ζ
  have hsub3 : {ξ : Fin sB.card → ℝ | F ξ ≤ ρ}
      ⊆ {ξ | F ξ ≤ (∫ η, F η ∂(Measure.pi fun _ : Fin sB.card => ν)) - r} := by
    intro ξ hξ
    have hm2 : ρ + r ≤ ∫ η, F η ∂(Measure.pi fun _ : Fin sB.card => ν) :=
      le_trans hmean hmeanF
    have hx : F ξ ≤ ρ := hξ
    show F ξ ≤ _
    linarith
  refine le_trans (le_trans htrans (measure_mono hsub3)) ?_
  refine le_trans (measure_le_mean_sub ν hsqν b lam hlam hb0 hlb sB.card F hFm
      (|G fun _ => 0| + (sB.card : ℝ) * b) hFbd (fun i => ℓ (e i)) (fun i => hℓ0 _)
      hFlip hFosc r) ?_
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have hden : (0:ℝ) < 1 - lam * b / 3 := by linarith
  have hcoef : (0:ℝ) ≤ lam ^ 2 / (2 * (1 - lam * b / 3)) := by positivity
  have hsumeq : ∑ i : Fin sB.card, ℓ (e i) ^ 2 = ∑ z ∈ sB, ℓ z ^ 2 :=
    Sandpile.sum_siteEnum sB fun z => ℓ z ^ 2
  have hnn : (0:ℝ) ≤ ∫ y, y ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg y
  rw [hsumeq]
  have hmul : (∫ y, y ^ 2 ∂ν) * (∑ z ∈ sB, ℓ z ^ 2) ≤ (∫ y, y ^ 2 ∂ν) * S :=
    mul_le_mul_of_nonneg_left hS hnn
  nlinarith [hcoef, hmul]

/-- `Pw_n(0)` is integrable when the scenery has a first moment. -/
theorem integrable_avg_originOdometer (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (habs : Integrable (fun y : ℝ => |y|) ν) (n : ℕ) :
    Integrable (fun ζ : Sandpile.Site d → ℝ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
      (LatticeProb.iidLaw d ν) := by
  have hIpi : Integrable (Sandpile.boxOriginAverage (d := d) n)
      (Measure.pi fun _ : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).card => ν) :=
    LatticeProb.integrable_of_lip ν habs _ (Sandpile.measurable_boxOriginAverage hd n)
      (fun i => Sandpile.originInfluence
        (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)) i))
      (Sandpile.abs_boxOriginAverage_update_le hd n)
  have hmp := LatticeProb.measurePreserving_pick _ ν
    (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)))
    (Sandpile.siteEnum_injective _)
  have h := hmp.integrable_comp_of_integrable hIpi
  exact h.congr (Filter.Eventually.of_forall fun ζ => by
    simpa using Sandpile.boxOriginAverage_pick hd n ζ)

/-- The deviation estimate at the neighbour average of the odometer killed at the origin. -/
theorem measure_truncOriginAverage_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsqν : Integrable (fun y : ℝ => y ^ 2) ν)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    (n : ℕ) (t lam ρ r : ℝ) (ht : 0 < t) (hlam : 0 < lam) (hlb : lam * (hi + t) < 3)
    (hmean : ρ + r ≤ meanOriginAverage d ν n) :
    (LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer
          (truncScenery (greenRatioWeight d) t ζ) n) 0 ≤ ρ}
      ≤ ENNReal.ofReal (Real.exp (-(lam * r) +
          lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) *
            ((∫ y, y ^ 2 ∂ν) *
              ∑' z : Sandpile.Site d, Sandpile.originInfluence z ^ 2))) := by
  have hd1 : 1 ≤ d := by omega
  exact measure_trunc_le_of_mean hd ν hsqν hi hhi hνhi n
    (fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (Sandpile.measurable_avg_originOdometer hd1 n)
    (fun ζ η h => Sandpile.avg_originOdometer_congr_box hd1 n ζ η h)
    Sandpile.originInfluence (fun z => Sandpile.originInfluence_nonneg z)
    (fun z => Sandpile.originInfluence_le_green_ratio (by omega) z)
    (fun ζ z v => Sandpile.abs_avg_originOdometer_update_le hd1 ζ z v n)
    (∑' z : Sandpile.Site d, Sandpile.originInfluence z ^ 2)
    ((Sandpile.summable_originInfluence_sq hGH hd).sum_le_tsum _ fun _ _ => sq_nonneg _)
    t lam ρ r ht hlam hlb
    (integrable_avg_originOdometer hd1 ν (integrable_abs_of_sq ν hsqν) n)
    (fun ζ => avg_originOdometer_le_trunc hd1 n (greenRatioWeight d) t ζ)
    hmean

/-- The truncation level `\eta_n\E Pw_n(0)` tends to infinity. -/
theorem tendsto_originLevel_atTop (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun n : ℕ => originLevel d ν K n) atTop atTop := by
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmeanν hvar hvar'
  refine tendsto_atTop.mpr fun M => ?_
  have hz : Tendsto (fun x : ℝ => Real.log x ^ (1 : ℝ) * x ^ (-(1 : ℝ))) atTop (𝓝 0) :=
    tendsto_log_rpow_mul_rpow_neg_atTop (q := 1) (by norm_num)
  have hpos : (0 : ℝ) < 1 / (|M| * K + 1) := by positivity
  have hlt := (hz.comp hainf).eventually (gt_mem_nhds hpos)
  filter_upwards [hlt, hainf.eventually_ge_atTop (Real.exp 1)] with n hn hge
  have hx0 : (0 : ℝ) < meanOriginAverage d ν n := lt_of_lt_of_le (Real.exp_pos 1) hge
  have hL : (1 : ℝ) ≤ Real.log (meanOriginAverage d ν n) := by
    have h := Real.log_le_log (Real.exp_pos 1) hge
    rwa [Real.log_exp] at h
  have hL0 : (0 : ℝ) < Real.log (meanOriginAverage d ν n) := lt_of_lt_of_le one_pos hL
  have hKL : (0 : ℝ) < K * Real.log (meanOriginAverage d ν n) := by positivity
  have hn' : Real.log (meanOriginAverage d ν n) * (meanOriginAverage d ν n)⁻¹
      < 1 / (|M| * K + 1) := by
    have he : ((fun x : ℝ => Real.log x ^ (1 : ℝ) * x ^ (-(1 : ℝ))) ∘ meanOriginAverage d ν) n
        = Real.log (meanOriginAverage d ν n) * (meanOriginAverage d ν n)⁻¹ := by
      simp [Real.rpow_neg hx0.le]
    rw [he] at hn
    exact hn
  have hkey : (|M| * K + 1) * Real.log (meanOriginAverage d ν n) < meanOriginAverage d ν n := by
    rw [lt_div_iff₀ (by positivity), mul_comm] at hn'
    calc (|M| * K + 1) * Real.log (meanOriginAverage d ν n)
        = (|M| * K + 1) * (Real.log (meanOriginAverage d ν n)
            * (meanOriginAverage d ν n)⁻¹) * meanOriginAverage d ν n := by
          field_simp
      _ < 1 * meanOriginAverage d ν n := by
          refine mul_lt_mul_of_pos_right ?_ hx0
          nlinarith [hn', hpos]
      _ = meanOriginAverage d ν n := one_mul _
  have hMle : M ≤ |M| := le_abs_self M
  rw [originLevel, le_div_iff₀ hKL]
  nlinarith [hkey, hL0, hMle, hL]

/-- The arithmetic of `sandpile.tex:5372`.  With the Chernoff parameter `1/t`, the increment
bound `hi + t` and a deviation `r=\theta a` from the mean, the Bernstein exponent is at most
`-\theta K\log a + 3\beta/2`, and `\theta K\geq3\beta` makes that at most `-\beta\log a`. -/
theorem exp_exponent_le (hi a t r s2 S β θ K : ℝ)
    (hLa : 1 ≤ Real.log a)
    (ht1 : 1 ≤ t) (hthi : hi ≤ t) (hsS : s2 * S ≤ t * β)
    (hs20 : 0 ≤ s2) (hS0 : 0 ≤ S) (hβ : 0 < β)
    (hat : t * (K * Real.log a) = a) (hr : r = θ * a) (hθK : 3 * β ≤ θ * K) :
    -(1 / t * r) + (1 / t) ^ 2 / (2 * (1 - 1 / t * (hi + t) / 3)) * (s2 * S)
      ≤ -(β * Real.log a) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hlam2 : 1 / t * (hi + t) ≤ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
    linarith
  have hden : (0 : ℝ) < 1 - 1 / t * (hi + t) / 3 := by linarith
  have hCle : (1 / t) ^ 2 / (2 * (1 - 1 / t * (hi + t) / 3)) ≤ 3 / (2 * t ^ 2) := by
    have h1 : (1 / t) ^ 2 / (2 * (1 - 1 / t * (hi + t) / 3)) ≤ (1 / t) ^ 2 / (2 / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have h2 : (1 / t) ^ 2 / (2 / 3 : ℝ) = 3 / (2 * t ^ 2) := by field_simp
    linarith [h1, h2.le, h2.ge]
  have hprod : (1 / t) ^ 2 / (2 * (1 - 1 / t * (hi + t) / 3)) * (s2 * S)
      ≤ 3 / (2 * t ^ 2) * (t * β) :=
    mul_le_mul hCle hsS (by positivity) (by positivity)
  have hquot : 3 / (2 * t ^ 2) * (t * β) ≤ 3 * β / 2 := by
    have heq : 3 / (2 * t ^ 2) * (t * β) = 3 * β / (2 * t) := by field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hgen : ∀ L : ℝ, t * L = a → 1 / t * (θ * a) = θ * L := by
    intro L hL
    rw [← hL]
    field_simp
  have hlinr : 1 / t * r = θ * (K * Real.log a) := by
    rw [hr]
    exact hgen _ hat
  rw [hlinr]
  nlinarith [hprod, hquot, hθK, hLa, hβ]

/-- **The first clause of `TruncatedOriginDeviation`** (`sandpile.tex:5356-5360` and
`sandpile.tex:5372`).  At the truncation level `\eta_n\E Pw_n(0)` and with the Chernoff
parameter `1/t_n`, the increment bound is `2t_n`, the quadratic term is `O(t_n^{-2})`, and
the Bernstein exponent is `5K\log\E Pw_n(0)/6`, which beats `\beta\log\E Pw_n(0)` as soon as
`K\geq3\beta`. -/
theorem eventually_measure_truncOriginAverage_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    {K β : ℝ} (hβ : 0 < β) (hK : 18 * β ≤ K) :
    ∀ᶠ n : ℕ in atTop,
      (LatticeProb.iidLaw d ν)
          {ζ | truncOriginAverage d ν K n ζ ≤ meanOriginAverage d ν n / 6}
        ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) := by
  have hd1 : 1 ≤ d := by omega
  have hK0 : (0 : ℝ) < K := by linarith
  have hsqν : Integrable (fun y : ℝ => y ^ 2) ν := by
    have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
      (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
    exact hLp.integrable_sq
  set s2 : ℝ := ∫ y, y ^ 2 ∂ν with hs2def
  set S : ℝ := ∑' z : Sandpile.Site d, Sandpile.originInfluence z ^ 2 with hSdef
  have hs20 : (0 : ℝ) ≤ s2 := integral_nonneg fun y => sq_nonneg y
  have hS0 : (0 : ℝ) ≤ S := tsum_nonneg fun z => sq_nonneg _
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmeanν hvar hvar'
  have htinf : Tendsto (fun n : ℕ => originLevel d ν K n) atTop atTop :=
    tendsto_originLevel_atTop hGH hd ν hatom hmeanν hvar hvar' hK0
  filter_upwards [hainf.eventually_ge_atTop (Real.exp 1),
    htinf.eventually_ge_atTop (max (max hi 1) (s2 * S / β))] with n hge htge
  set a : ℝ := meanOriginAverage d ν n with hadef
  set t : ℝ := originLevel d ν K n with htdef
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (Real.exp_pos 1) hge
  have hLa : (1 : ℝ) ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos 1) hge
    rwa [Real.log_exp] at h
  have hLa0 : (0 : ℝ) < Real.log a := lt_of_lt_of_le one_pos hLa
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_trans (le_max_right hi 1) (le_max_left _ _)) htge
  have hthi : hi ≤ t := le_trans (le_trans (le_max_left hi 1) (le_max_left _ _)) htge
  have htS : s2 * S / β ≤ t := le_trans (le_max_right _ _) htge
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  set lam : ℝ := 1 / t with hlamdef
  have hlam0 : (0 : ℝ) < lam := by rw [hlamdef]; positivity
  have hlam2 : lam * (hi + t) ≤ 2 := by
    rw [hlamdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
    linarith
  have hlb : lam * (hi + t) < 3 := by linarith
  have hat : t * (K * Real.log a) = a := by
    rw [htdef, originLevel, ← hadef]
    field_simp
  have hsS : s2 * S ≤ t * β := by
    rw [div_le_iff₀ hβ] at htS
    exact htS
  have hfin : -(lam * (5 * a / 6)) + lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * (s2 * S)
      ≤ -(β * Real.log a) := by
    rw [hlamdef]
    exact exp_exponent_le hi a t (5 * a / 6) s2 S β (5 / 6) K hLa ht1 hthi hsS hs20 hS0
      hβ hat (by ring) (by linarith)
  have hset : {ζ : Sandpile.Site d → ℝ | truncOriginAverage d ν K n ζ ≤ a / 6}
      = {ζ : Sandpile.Site d → ℝ | Sandpile.avg (Sandpile.originOdometer
          (truncScenery (greenRatioWeight d) t ζ) n) 0 ≤ a / 6} := rfl
  rw [hset]
  refine le_trans (measure_truncOriginAverage_le hGH hd ν hsqν hi hhi hνhi n t lam (a / 6)
    (5 * a / 6) ht0 hlam0 hlb (by rw [← hadef]; linarith)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-(lam * (5 * a / 6)) +
        lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * (s2 * S))
      ≤ Real.exp (-(β * Real.log a)) := Real.exp_le_exp.mpr hfin
    _ = a ^ (-β) := by
        rw [Real.rpow_def_of_pos ha0]
        congr 1
        ring

/-- A functional that reads only the box and is coordinatewise Lipschitz is integrable when
the scenery has a first moment. -/
theorem integrable_of_box_lip (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (habs : Integrable (fun y : ℝ => |y|) ν) (n : ℕ)
    (Φ : (Sandpile.Site d → ℝ) → ℝ) (hΦm : Measurable Φ)
    (hΦbox : ∀ ζ η : Sandpile.Site d → ℝ,
      (∀ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1), ζ z = η z) → Φ ζ = Φ η)
    (ℓ : Sandpile.Site d → ℝ)
    (hΦlip : ∀ (ζ : Sandpile.Site d → ℝ) (z : Sandpile.Site d) (v : ℝ),
      |Φ ζ - Φ (Function.update ζ z v)| ≤ ℓ z * |ζ z - v|) :
    Integrable Φ (LatticeProb.iidLaw d ν) := by
  classical
  set sB : Finset (Sandpile.Site d) := Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)
    with hsBdef
  set e : Fin sB.card → Sandpile.Site d := Sandpile.siteEnum sB with hedef
  have hev : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card),
      Sandpile.siteExtend sB ξ (e i) = ξ i := by
    intro ξ i
    simp [Sandpile.siteExtend, Sandpile.siteEnum, hedef]
  set G : (Fin sB.card → ℝ) → ℝ := fun ξ => Φ (Sandpile.siteExtend sB ξ) with hGdef
  have hGm : Measurable G := hΦm.comp (Sandpile.measurable_siteExtend sB)
  have hGlip : ∀ (ξ : Fin sB.card → ℝ) (i : Fin sB.card) (v : ℝ),
      |G ξ - G (Function.update ξ i v)| ≤ ℓ (e i) * |ξ i - v| := by
    intro ξ i v
    rw [hGdef]
    simp only
    rw [Sandpile.siteExtend_update]
    have h := hΦlip (Sandpile.siteExtend sB ξ) (e i) v
    rw [hev ξ i] at h
    exact h
  have hIpi := LatticeProb.integrable_of_lip ν habs G hGm (fun i => ℓ (e i)) hGlip
  have hmp := LatticeProb.measurePreserving_pick _ ν e (Sandpile.siteEnum_injective sB)
  have h := hmp.integrable_comp_of_integrable hIpi
  refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
  show G (fun i => ζ (e i)) = Φ ζ
  rw [hGdef]
  exact hΦbox _ _ fun z hz => Sandpile.siteExtend_siteEnum sB ζ hz

/-- What `sandpile.tex:5369-5371` asserts about the odometer killed at the origin and at one
further site: its neighbour average at the origin has mean at least a third of `\E Pw_n(0)`,
uniformly in the killed site.  The paper gets this from `lem:localization-killing` averaged
over the neighbours of the origin, together with the probability
`(G(x,0)+G(x,z_0))/(G(0,0)+G(0,z_0))` that the walk from `x` hits the two-point set. -/
def PairKilledMeanLower (d : ℕ) (ν : Measure ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ z₀ : Sandpile.Site d,
    meanOriginAverage d ν n / 3
      ≤ ∫ ζ, Sandpile.avg (pairOdometer z₀ ζ n) 0 ∂(LatticeProb.iidLaw d ν)

/-- The deviation estimate at the neighbour average of the odometer killed at `\{0,z_0\}`. -/
theorem measure_truncPairAverage_le (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsqν : Integrable (fun y : ℝ => y ^ 2) ν)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    (n : ℕ) (z₀ : Sandpile.Site d)
    (ℓ : Sandpile.Site d → ℝ) (hℓ0 : ∀ z, 0 ≤ ℓ z) (hℓc : ∀ z, ℓ z ≤ greenRatioWeight d z)
    (hlip : ∀ (ζ : Sandpile.Site d → ℝ) (z : Sandpile.Site d) (v : ℝ),
      |Sandpile.avg (pairOdometer z₀ ζ n) 0
        - Sandpile.avg (pairOdometer z₀ (Function.update ζ z v) n) 0| ≤ ℓ z * |ζ z - v|)
    (S : ℝ) (hS : ∑ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1), ℓ z ^ 2 ≤ S)
    (t lam ρ r : ℝ) (ht : 0 < t) (hlam : 0 < lam) (hlb : lam * (hi + t) < 3)
    (hmean : ρ + r ≤ ∫ ζ, Sandpile.avg (pairOdometer z₀ ζ n) 0 ∂(LatticeProb.iidLaw d ν)) :
    (LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (pairOdometer z₀ (truncScenery (greenRatioWeight d) t ζ) n) 0 ≤ ρ}
      ≤ ENNReal.ofReal (Real.exp (-(lam * r) +
          lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * ((∫ y, y ^ 2 ∂ν) * S))) := by
  have hd1 : 1 ≤ d := by omega
  exact measure_trunc_le_of_mean hd ν hsqν hi hhi hνhi n
    (fun ζ => Sandpile.avg (pairOdometer z₀ ζ n) 0)
    (measurable_avg_localizedOdometer hd1 _ n)
    (fun ζ η h => avg_localizedOdometer_congr_box hd1 _ n ζ η h)
    ℓ hℓ0 hℓc hlip S hS t lam ρ r ht hlam hlb
    (integrable_of_box_lip ν (integrable_abs_of_sq ν hsqν) n _
      (measurable_avg_localizedOdometer hd1 _ n)
      (fun ζ η h => avg_localizedOdometer_congr_box hd1 _ n ζ η h) ℓ hlip)
    (fun ζ => Sandpile.avg_mono_le
      (fun y => localizedOdometer_mono hd1 _ n y (le_truncScenery (greenRatioWeight d) t ζ)) 0)
    hmean

/-- **The second clause of `TruncatedOriginDeviation`** (`sandpile.tex:5361-5372`), from the
two facts of `PairKilledMeanLower`. -/
theorem eventually_measure_truncPairAverage_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    {K β : ℝ} (hβ : 0 < β) (hK : 18 * β ≤ K) (hpair : PairKilledMeanLower d ν) :
    ∀ᶠ n : ℕ in atTop, ∀ z₀ : Sandpile.Site d,
      (LatticeProb.iidLaw d ν)
          {ζ | truncPairAverage d ν K n z₀ ζ ≤ meanOriginAverage d ν n / 6}
        ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) := by
  have hmeanp : PairKilledMeanLower d ν := hpair
  have hd1 : 1 ≤ d := by omega
  set S : ℝ := ∑' z : Sandpile.Site d, Sandpile.originInfluence z ^ 2 with hSdef
  have hSsum : ∀ (z₀ : Sandpile.Site d) (m : ℕ),
      ∑ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (m + 1),
        Sandpile.originInfluence z ^ 2 ≤ S :=
    fun _ _ => (Sandpile.summable_originInfluence_sq hGH hd).sum_le_tsum _ fun _ _ => sq_nonneg _
  have hlip : ∀ (z₀ : Sandpile.Site d) (m : ℕ) (ζ : Sandpile.Site d → ℝ)
      (z : Sandpile.Site d) (v : ℝ),
      |Sandpile.avg (pairOdometer z₀ ζ m) 0
        - Sandpile.avg (pairOdometer z₀ (Function.update ζ z v) m) 0|
        ≤ Sandpile.originInfluence z * |ζ z - v| :=
    fun z₀ m ζ z v =>
      abs_avg_localizedOdometer_update_le hd1 (fun w hw => hw.1) ζ z v m
  have hK0 : (0 : ℝ) < K := by linarith
  have hsqν : Integrable (fun y : ℝ => y ^ 2) ν := by
    have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
      (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
    exact hLp.integrable_sq
  set s2 : ℝ := ∫ y, y ^ 2 ∂ν with hs2def
  have hs20 : (0 : ℝ) ≤ s2 := integral_nonneg fun y => sq_nonneg y
  have hS0 : (0 : ℝ) ≤ S := tsum_nonneg fun z => sq_nonneg _
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmeanν hvar hvar'
  have htinf : Tendsto (fun n : ℕ => originLevel d ν K n) atTop atTop :=
    tendsto_originLevel_atTop hGH hd ν hatom hmeanν hvar hvar' hK0
  filter_upwards [hainf.eventually_ge_atTop (Real.exp 1),
    htinf.eventually_ge_atTop (max (max hi 1) (s2 * S / β)), hmeanp] with n hge htge hmn
  intro z₀
  set a : ℝ := meanOriginAverage d ν n with hadef
  set t : ℝ := originLevel d ν K n with htdef
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le (Real.exp_pos 1) hge
  have hLa : (1 : ℝ) ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos 1) hge
    rwa [Real.log_exp] at h
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_trans (le_max_right hi 1) (le_max_left _ _)) htge
  have hthi : hi ≤ t := le_trans (le_trans (le_max_left hi 1) (le_max_left _ _)) htge
  have htS : s2 * S / β ≤ t := le_trans (le_max_right _ _) htge
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  set lam : ℝ := 1 / t with hlamdef
  have hlam0 : (0 : ℝ) < lam := by rw [hlamdef]; positivity
  have hlam2 : lam * (hi + t) ≤ 2 := by
    rw [hlamdef, div_mul_eq_mul_div, one_mul, div_le_iff₀ ht0]
    linarith
  have hlb : lam * (hi + t) < 3 := by linarith
  have hat : t * (K * Real.log a) = a := by
    rw [htdef, originLevel, ← hadef]
    field_simp
  have hsS : s2 * S ≤ t * β := by
    rw [div_le_iff₀ hβ] at htS
    exact htS
  have hfin : -(lam * (a / 6)) + lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * (s2 * S)
      ≤ -(β * Real.log a) := by
    rw [hlamdef]
    exact exp_exponent_le hi a t (a / 6) s2 S β (1 / 6) K hLa ht1 hthi hsS hs20 hS0
      hβ hat (by ring) (by linarith)
  have hset : {ζ : Sandpile.Site d → ℝ | truncPairAverage d ν K n z₀ ζ ≤ a / 6}
      = {ζ : Sandpile.Site d → ℝ | Sandpile.avg (pairOdometer z₀
          (truncScenery (greenRatioWeight d) t ζ) n) 0 ≤ a / 6} := rfl
  rw [hset]
  refine le_trans (measure_truncPairAverage_le hd ν hsqν hi hhi hνhi n z₀
    Sandpile.originInfluence (fun z => Sandpile.originInfluence_nonneg z)
    (fun z => Sandpile.originInfluence_le_green_ratio (by omega) z) (hlip z₀ n)
    S (hSsum z₀ n) t lam (a / 6) (a / 6) ht0 hlam0 hlb
    (by linarith [hmn z₀])) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-(lam * (a / 6)) +
        lam ^ 2 / (2 * (1 - lam * (hi + t) / 3)) * (s2 * S))
      ≤ Real.exp (-(β * Real.log a)) := Real.exp_le_exp.mpr hfin
    _ = a ^ (-β) := by
        rw [Real.rpow_def_of_pos ha0]
        congr 1
        ring

/-- **`Sandpile.TruncatedOriginDeviation` from `PairKilledMeanLower`.**  Both clauses of the
residual of the first step of the heavy-tailed case follow from the Bernstein inequality once
the odometer killed at two sites is known to be coordinatewise Lipschitz with square summable
coefficients and to have mean at least `\E Pw_n(0)/3`. -/
theorem truncatedOriginDeviation_of_pairKilled
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (hi : ℝ) (hhi : 0 ≤ hi) (hνhi : ν (Set.Ioi hi) = 0)
    {K β : ℝ} (hβ : 0 < β) (hK : 18 * β ≤ K) (hpair : PairKilledMeanLower d ν) :
    TruncatedOriginDeviation d ν K β := by
  filter_upwards [eventually_measure_truncOriginAverage_le hGH hd ν hatom hmeanν hvar hvar'
      hi hhi hνhi hβ hK,
    eventually_measure_truncPairAverage_le hGH hd ν hatom hmeanν hvar hvar'
      hi hhi hνhi hβ hK hpair] with n h1 h2
  exact ⟨h1, h2⟩

/-- **Case (b) of `prop:dgt4-contact-asymptotics` from `PairKilledMeanLower`.**  Everything of
`sandpile.tex:5301-5412` is proved except the two facts about the odometer killed at two
sites. -/
theorem caseThresholdField_linear_of_pairKilled
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmeanν : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p : ℝ} (hα : 1 < α) (hp : 0 < p) (hpα : α < 2 * p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d => greenRatioWeight d z ^ p)
    (Mb : ℝ) (hMb : ν (Set.Ioi Mb) = 0) (hpair : PairKilledMeanLower d ν) :
    CaseThresholdField d ν (1 - 1 / α) := by
  have hβ : (0 : ℝ) < α + 1 := by linarith
  have hhi : (0 : ℝ) ≤ max Mb 0 := le_max_right _ _
  have hνhi : ν (Set.Ioi (max Mb 0)) = 0 :=
    nonpos_iff_eq_zero.mp
      (le_trans (measure_mono (Set.Ioi_subset_Ioi (le_max_left _ _))) hMb.le)
  exact caseThresholdField_linear_of_truncated hGH hd ν hatom hmeanν hvar hvar'
    hα hp hpα (by positivity : (0 : ℝ) < 18 * (α + 1)) (by linarith : α < α + 1)
    hmom hrv hsumc
    (truncatedOriginDeviation_of_pairKilled hGH hd ν hatom hmeanν hvar hvar'
      (max Mb 0) hhi hνhi hβ le_rfl hpair)

end Sandpile
