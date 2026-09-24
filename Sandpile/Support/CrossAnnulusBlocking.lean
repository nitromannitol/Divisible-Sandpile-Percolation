/- Positive-arm exclusion by annular crossings and the uniform power bound. -/
import Sandpile.Support.CrossRectangleWalk
import Sandpile.Support.CrossAnnuli
import Sandpile.Support.CrossPathContact
import Mathlib.Topology.Connected.LocallyPathConnected

open Set MeasureTheory Filter
open scoped ENNReal
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings Sandpile.Support.CrossPathContact

theorem joinedIn_positive_of_connected {f : Space 2 → ℝ} (hf : Continuous f)
    {Γ : Set (Space 2)} (hc : IsConnected Γ) (hΓ : Γ ⊆ {u | 0 < f u})
    {x y : Space 2} (hx : x ∈ Γ) (hy : y ∈ Γ) : JoinedIn {u | 0 < f u} x y := by
  have ho : IsOpen {u | 0 < f u} := isOpen_lt continuous_const hf
  have hp := (ho.connectedComponentIn).isConnected_iff_isPathConnected.mp
    (isConnected_connectedComponentIn_iff.mpr (hΓ hx))
  exact (hp.joinedIn x (mem_connectedComponentIn (hΓ hx)) y
    (hc.isPreconnected.subset_connectedComponentIn hx hΓ hy)).mono
    (connectedComponentIn_subset _ _)

/-- The outward coordinate on each of the four sides of a square annulus. -/
def annulusCoord (j : Fin 4) (x u : Space 2) : ℝ :=
  ![u 1 - x 1, x 1 - u 1, u 0 - x 0, x 0 - u 0] j

theorem annulusCoord_le_norm (j : Fin 4) (x u : Space 2) :
    annulusCoord j x u ≤ ‖u - x‖ := by
  have h0 := PiLp.norm_apply_le (p := 2) (u - x) 0
  have h1 := PiLp.norm_apply_le (p := 2) (u - x) 1
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at h0 h1
  have := abs_le.mp h0
  have := abs_le.mp h1
  fin_cases j <;> simp [annulusCoord] <;> linarith

theorem annulusCoord_continuous (j : Fin 4) (x : Space 2) : Continuous (annulusCoord j x) := by
  change Continuous (fun u => annulusCoord j x u)
  fin_cases j <;> dsimp [annulusCoord] <;> fun_prop

theorem annulus_strip_crossing {γ : ℝ → Space 2} (hγ : Continuous γ)
    {a b r : ℝ} (hab : a ≤ b) {x : Space 2} {j : Fin 4} {S : Set (Space 2)}
    (hS : ∀ t ∈ Icc a b, γ t ∈ S)
    (hbox : ∀ t ∈ Icc a b, ∀ i : Fin 2, |γ t i - x i| ≤ 2 * r)
    (hcoord : ∀ t ∈ Icc a b, r ≤ annulusCoord j x (γ t))
    (ha : annulusCoord j x (γ a) = r) (hb : annulusCoord j x (γ b) = 2 * r) :
    Crosses (annulusLo x r j) (annulusHi x r j) (swapIdx (annulusSideDir j)) S := by
  have hrect : γ '' Icc a b ⊆ S ∩ rectSet (annulusLo x r j) (annulusHi x r j) := by
    rintro z ⟨t, ht, rfl⟩
    refine ⟨hS t ht, ?_⟩
    have h0 := abs_le.mp (hbox t ht 0)
    have h1 := abs_le.mp (hbox t ht 1)
    have h := hcoord t ht
    intro i
    fin_cases j <;> fin_cases i <;> dsimp only at h ⊢ <;>
      norm_num [annulusLo, annulusHi, annulusSideLo, annulusSideHi, annulusCoord] at h ⊢ <;>
      constructor <;> linarith!
  refine ⟨γ '' Icc a b, hrect, isCompact_Icc.image hγ,
    (isConnected_Icc hab).image _ hγ.continuousOn, ?_⟩
  have hga : γ a ∈ γ '' Icc a b := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hgb : γ b ∈ γ '' Icc a b := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  fin_cases j
  · change (∃ p ∈ γ '' Icc a b, p 1 = x 1 + r * 1) ∧
      ∃ p ∈ γ '' Icc a b, p 1 = x 1 + r * 2
    change γ a 1 - x 1 = r at ha
    change γ b 1 - x 1 = 2 * r at hb
    exact ⟨⟨γ a, hga, by linarith⟩, ⟨γ b, hgb, by linarith⟩⟩
  · change (∃ p ∈ γ '' Icc a b, p 1 = x 1 + r * (-2)) ∧
      ∃ p ∈ γ '' Icc a b, p 1 = x 1 + r * (-1)
    change x 1 - γ a 1 = r at ha
    change x 1 - γ b 1 = 2 * r at hb
    exact ⟨⟨γ b, hgb, by linarith⟩, ⟨γ a, hga, by linarith⟩⟩
  · change (∃ p ∈ γ '' Icc a b, p 0 = x 0 + r * 1) ∧
      ∃ p ∈ γ '' Icc a b, p 0 = x 0 + r * 2
    change γ a 0 - x 0 = r at ha
    change γ b 0 - x 0 = 2 * r at hb
    exact ⟨⟨γ a, hga, by linarith⟩, ⟨γ b, hgb, by linarith⟩⟩
  · change (∃ p ∈ γ '' Icc a b, p 0 = x 0 + r * (-2)) ∧
      ∃ p ∈ γ '' Icc a b, p 0 = x 0 + r * (-1)
    change x 0 - γ a 0 = r at ha
    change x 0 - γ b 0 = 2 * r at hb
    exact ⟨⟨γ b, hgb, by linarith⟩, ⟨γ a, hga, by linarith⟩⟩

/-- A path leaving the outer ball crosses one side of the square annulus
in its short direction. -/
theorem exists_annulus_strip_of_path {γ : ℝ → Space 2} (hγ : Continuous γ)
    {x : Space 2} {r : ℝ} (hr : 0 < r) {S : Set (Space 2)}
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S)
    (hstart : ‖γ 0 - x‖ ≤ r) (hend : 3 * r ≤ ‖γ 1 - x‖) :
    ∃ j : Fin 4, Crosses (annulusLo x r j) (annulusHi x r j)
      (swapIdx (annulusSideDir j)) S := by
  let F (t : ℝ) := max |γ t 0 - x 0| |γ t 1 - x 1|
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hcoord (t : ℝ) (i : Fin 2) : |γ t i - x i| ≤ ‖γ t - x‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (p := 2) (γ t - x) i
  have hF0 : F 0 ≤ 2 * r := by
    exact (max_le ((hcoord 0 0).trans hstart) ((hcoord 0 1).trans hstart)).trans (by linarith)
  have hF1 : 2 * r ≤ F 1 := by
    by_contra h
    have hh : F 1 < 2 * r := lt_of_not_ge h
    have h0 : |γ 1 0 - x 0| < 2 * r := (le_max_left _ _).trans_lt hh
    have h1 : |γ 1 1 - x 1| < 2 * r := (le_max_right _ _).trans_lt hh
    have hs : ‖γ 1 - x‖ ^ 2 = (γ 1 0 - x 0) ^ 2 + (γ 1 1 - x 1) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    have h0s : (γ 1 0 - x 0) ^ 2 < (2 * r) ^ 2 := by nlinarith [abs_nonneg (γ 1 0 - x 0), sq_abs (γ 1 0 - x 0)]
    have h1s : (γ 1 1 - x 1) ^ 2 < (2 * r) ^ 2 := by nlinarith [abs_nonneg (γ 1 1 - x 1), sq_abs (γ 1 1 - x 1)]
    nlinarith [sq_nonneg r]
  obtain ⟨b, hb, hbe, hbefore⟩ := exists_first_contact hF (by norm_num) hF0 hF1
  have hbox : ∀ t ∈ Icc 0 b, ∀ i : Fin 2, |γ t i - x i| ≤ 2 * r := by
    intro t ht i
    have h := hbefore t ht
    fin_cases i
    · exact (le_max_left _ _).trans h
    · exact (le_max_right _ _).trans h
  have hj : ∃ j : Fin 4, annulusCoord j x (γ b) = 2 * r := by
    dsimp [F] at hbe
    rcases max_choice |γ b 0 - x 0| |γ b 1 - x 1| with he | he
    · rw [he] at hbe
      rcases le_total 0 (γ b 0 - x 0) with h | h
      · exact ⟨2, by simpa [annulusCoord, abs_of_nonneg h] using hbe⟩
      · refine ⟨3, ?_⟩
        simp only [abs_of_nonpos h] at hbe
        dsimp [annulusCoord]; linarith
    · rw [he] at hbe
      rcases le_total 0 (γ b 1 - x 1) with h | h
      · exact ⟨0, by simpa [annulusCoord, abs_of_nonneg h] using hbe⟩
      · refine ⟨1, ?_⟩
        simp only [abs_of_nonpos h] at hbe
        dsimp [annulusCoord]; linarith
  obtain ⟨j, hj⟩ := hj
  obtain ⟨a, ha, hae, hafter⟩ := exists_last_contact ((annulusCoord_continuous j x).comp hγ)
    hb.1 ((annulusCoord_le_norm j x (γ 0)).trans hstart) (by rw [hj]; linarith : r ≤ annulusCoord j x (γ b))
  exact ⟨j, annulus_strip_crossing hγ ha.2
    (fun t ht => hS t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
    (fun t ht => hbox t ⟨ha.1.trans ht.1, ht.2⟩) hafter hae hj⟩

/-- A positive arm joins the inner closed ball to the outside of the outer
open ball by a compact connected subset of the positive set. -/
def PositiveArm (f : Space 2 → ℝ) (x : Space 2) (r R : ℝ) : Prop :=
  ∃ Γ : Set (Space 2), IsCompact Γ ∧ IsConnected Γ ∧ Γ ⊆ {u | 0 < f u} ∧
    (∃ u ∈ Γ, ‖u - x‖ ≤ r) ∧ (∃ v ∈ Γ, R ≤ ‖v - x‖)

/-- Four nonpositive long crossings exclude a positive arm through the
annulus. The path used in the proof comes from the open positive component. -/
theorem positiveArm_avoids_annulus {f : Space 2 → ℝ} (hf : Continuous f)
    {x : Space 2} {r R ρ : ℝ} (hρ : 0 < ρ) (hr : r ≤ ρ) (hR : 3 * ρ ≤ R)
    (harm : PositiveArm f x r R) :
    ¬ ∀ j : Fin 4, Crosses (annulusLo x ρ j) (annulusHi x ρ j)
      (annulusSideDir j) {u | f u ≤ 0} := by
  intro hall
  obtain ⟨Γ, _, hΓn, hΓ, ⟨u, hu, hur⟩, ⟨v, hv, hvR⟩⟩ := harm
  obtain ⟨p, hp⟩ := joinedIn_positive_of_connected hf hΓn hΓ hu hv
  obtain ⟨j, hj⟩ := exists_annulus_strip_of_path p.continuous_extend hρ
    (fun t ht => by rw [p.extend_apply ht]; exact hp _)
    (by simpa using hur.trans hr) (by simpa using hR.trans hvR)
  have hn := hall j
  have hab := annulus_nondegenerate x hρ j
  have hint : ({u | 0 < f u} ∩ {u | f u ≤ 0}).Nonempty := by
    rcases (show annulusSideDir j = 0 ∨ annulusSideDir j = 1 by
      fin_cases j <;> simp [annulusSideDir]) with hd | hd
    · rw [hd] at hj hn
      have he : swapIdx 0 = 1 := rfl
      rw [he] at hj
      obtain ⟨z, hz, hz'⟩ := rectangle_crossings_intersect hab hn hj
      exact ⟨z, hz', hz⟩
    · rw [hd] at hj hn
      have he : swapIdx 1 = 0 := rfl
      rw [he] at hj
      exact rectangle_crossings_intersect hab hj hn
  obtain ⟨z, hz, hz'⟩ := hint
  exact (not_lt_of_ge (show f z ≤ 0 from hz')) (show 0 < f z from hz)

/-- The actual positive-arm event has geometrically decreasing probability
across separated annuli. All field, independence, and geometric conditions are
discharged for the unit ball field. -/
theorem uniform_positiveArm_geometric (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (W : (Space d → ℝ) → Ω → ℝ),
        IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω) →
      ∀ (x : Space 2) (r R : ℝ), 2 ≤ r → ∀ n : ℕ,
        (∀ i < n, 3 * (8 ^ i * r) ≤ R) →
        P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r R} ≤
          ENNReal.ofReal ((1 - q) ^ n) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := uniform_nonpositive_annulus_avoidance hRSW hPitt
  refine ⟨q, hq0, hq1, ?_⟩
  intro d hd Ω _ P _ W hW hc x r R hr n hfit
  apply le_trans _ (hbound d hd Ω P W hW hc x r hr n)
  apply MeasureTheory.measure_mono_ae
  filter_upwards [hc] with ω hω
  intro harm i hi
  have hri : r ≤ 8 ^ i * r := by
    have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) (n := i)
    nlinarith
  exact positiveArm_avoids_annulus hω (by linarith : 0 < 8 ^ i * r) hri (hfit i hi) harm

/-- The positive-arm power bound at inner radii at least two. -/
theorem uniform_positiveArm_power_two (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) :
    ∃ C α : ℝ, 1 ≤ C ∧ 0 < α ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω) →
      ∀ (x : Space 2) (r R : ℝ), 2 ≤ r → r ≤ R →
        P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r R} ≤
          ENNReal.ofReal (C * (r / R) ^ α) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := uniform_positiveArm_geometric hRSW hPitt
  have hqm : 0 < 1 - q := by linarith
  refine ⟨(1 - q)⁻¹, armExponent q 8, ?_, armExponent_pos hq0 hq1 (by norm_num), ?_⟩
  · exact (one_le_inv₀ hqm).mpr (by linarith)
  intro d hd Ω _ P _ W hW hc x r R hr hrR
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have ht : 1 ≤ R / r := (one_le_div hr0).mpr hrR
  obtain ⟨n, hn, hfit⟩ := exists_scale_split (by norm_num : (4 : ℝ) ≤ 8) ht
  have hfit' (i : ℕ) (hi : i < n) : 3 * (8 ^ i * r) ≤ R := by
    have h := (le_div_iff₀ hr0).mp (hfit i hi)
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 8) i
    nlinarith
  have hg := hbound d hd Ω P W hW hc x r R hr n hfit'
  have hp := geometric_to_power 8 hqm (by linarith : 1 - q < 1) ht n
    (log_le_of_pow (by norm_num : (1 : ℝ) < 8) ht n hn)
  have he : (R / r) ^ (-(armExponent q 8)) = (r / R) ^ armExponent q 8 := by
    rw [Real.rpow_neg (div_pos hR0 hr0).le, ← Real.inv_rpow (div_pos hR0 hr0).le, inv_div]
  change (1 - q) ^ n ≤ (1 - q)⁻¹ * (R / r) ^ (-(armExponent q 8)) at hp
  rw [he] at hp
  exact hg.trans (ENNReal.ofReal_le_ofReal hp)

/-- The arm estimate of `sandpile.tex:2221-2227`, with constants chosen before
the dimension, realization, center, and radii. -/
theorem uniform_positiveArm_power (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ (d : ℕ), d = 2 ∨ d = 3 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ᵐ ω ∂P, Continuous fun u => ballField d W 1 u ω) →
      ∀ (x : Space 2) (r R : ℝ), 1 ≤ r → r ≤ R →
        P {ω | PositiveArm (fun u => ballField d W 1 u ω) x r R} ≤
          ENNReal.ofReal (C * (r / R) ^ α) := by
  obtain ⟨C, α, hC, hα, hbound⟩ := uniform_positiveArm_power_two hRSW hPitt
  refine ⟨C * 2 ^ α, α, mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _), hα, ?_⟩
  intro d hd Ω _ P _ W hW hc x r R hr hrR
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := hr0.trans_le hrR
  have he : C * 2 ^ α * (r / R) ^ α = C * (2 * r / R) ^ α := by
    rw [mul_assoc, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (div_pos hr0 hR0).le]
    congr 2
    ring
  rw [he]
  by_cases hR : 2 * r ≤ R
  · apply le_trans _ (hbound d hd Ω P W hW hc x (2 * r) R (by linarith) hR)
    apply measure_mono
    rintro ω ⟨Γ, hΓc, hΓn, hΓ, ⟨u, hu, hur⟩, hv⟩
    exact ⟨Γ, hΓc, hΓn, hΓ, ⟨u, hu, by linarith⟩, hv⟩
  · have hratio : 1 ≤ 2 * r / R := (one_le_div hR0).mpr (by linarith)
    have hpow : 1 ≤ (2 * r / R) ^ α := Real.one_le_rpow hratio hα.le
    have hone : (1 : ℝ) ≤ C * (2 * r / R) ^ α := by nlinarith
    exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hone)

end Sandpile.Support
