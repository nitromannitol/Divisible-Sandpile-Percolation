/-
The near-far reduction for ball Green crossings, combining small
near-low components with local far-field oscillation.
-/
import Sandpile.Support.NearCluster
import Sandpile.Support.FarOscillation

open MeasureTheory Set Filter
open scoped Topology

namespace Sandpile

lemma ballRect_eq_image_planeRectangle {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4) :
    ballRect ϑ r x = planeTranslate x '' (planeRectangle ⌊ϑ * r⌋₊ r : Set (Site 2)) := by
  have hf : (⌊ϑ * r⌋₊ : ℤ) = ⌊ϑ * r⌋ := Int.natCast_floor_eq_floor (mul_nonneg hϑ (Nat.cast_nonneg r))
  ext z
  constructor
  · intro hz
    obtain ⟨h0, h0u, h1, h1u, hp⟩ := hz
    let u : Site 2 := ![z 0 - x 0, z 1 - x 1]
    refine ⟨u, (mem_planeRectangle _ _ _).mpr ⟨h0, ?_, h1, h1u⟩, ?_⟩
    · change z 0 - x 0 ≤ (⌊ϑ * r⌋₊ : ℤ)
      rwa [hf]
    · funext i
      fin_cases i
      · change x 0 + (z 0 - x 0) = z 0
        abel
      · change x 1 + (z 1 - x 1) = z 1
        abel
      · exact (hp 2 (by decide)).symm
      · exact (hp 3 (by decide)).symm
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨h0, h0u, h1, h1u⟩ := (mem_planeRectangle _ _ _).mp hu
    change 0 ≤ x 0 + u 0 - x 0 ∧ x 0 + u 0 - x 0 ≤ ⌊ϑ * r⌋ ∧
      0 ≤ x 1 + u 1 - x 1 ∧ x 1 + u 1 - x 1 ≤ (r : ℤ) ∧ _
    refine ⟨by omega, by omega, by omega, by omega, ?_⟩
    intro i hi
    fin_cases i <;> simp_all [planeTranslate]

lemma planeTranslate_coord_dist_le (x : Site 4) (z w : Site 2) (i : Fin 2) :
    |(w i : ℝ) - (z i : ℝ)| ≤ dist (planeTranslate x z) (planeTranslate x w) := by
  let j := Fin.castLE (by decide : 2 ≤ 4) i
  calc
    _ = dist ((planeTranslate x z) j) ((planeTranslate x w) j) := by
      fin_cases i <;> simp [j, planeTranslate, Int.dist_eq, abs_sub_comm]
    _ ≤ _ := dist_le_pi_dist _ _ j

lemma oscillation_on_ballRect {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (r : ℕ) (x : Site 4)
    (H : Site 4 → ℝ) (R η : ℝ)
    (hosc : ∀ z w : planeRectangle ⌊ϑ * r⌋₊ r,
      (∀ i : Fin 2, |((w : Site 2) i : ℝ) - ((z : Site 2) i : ℝ)| ≤ R) →
        |H (planeTranslate x z) - H (planeTranslate x w)| ≤ η) :
    ∀ z ∈ ballRect ϑ r x, ∀ w ∈ ballRect ϑ r x, dist z w ≤ R → |H z - H w| ≤ η := by
  intro z hz w hw hd
  rw [ballRect_eq_image_planeRectangle hϑ r x] at hz hw
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨v, hv, rfl⟩ := hw
  exact hosc ⟨u, hu⟩ ⟨v, hv⟩ (fun i => (planeTranslate_coord_dist_le x u v i).trans hd)

lemma eventually_mesoscopic_gap {α M : ℝ} (hα1 : α < 1) (hM : 0 < M) :
    ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ M * (⌊(r : ℝ) ^ α⌋₊ : ℝ) < (r : ℝ) := by
  have hlim : Tendsto (fun r : ℕ => M * (r : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α)).comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, mul_zero, neg_sub] using hh.const_mul M
  filter_upwards [eventually_ge_atTop 2, (tendsto_order.mp hlim).2 1 (by norm_num)] with r hr hh
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have he : M * (r : ℝ) ^ (α - 1) = (M * (r : ℝ) ^ α) / (r : ℝ) := by
    rw [Real.rpow_sub hrpos, Real.rpow_one]
    ring
  rw [he] at hh
  have hlt : M * (r : ℝ) ^ α < (r : ℝ) := by
    have hs := (div_lt_iff₀ hrpos).mp hh
    simpa only [one_mul] using hs
  exact ⟨hr, (mul_le_mul_of_nonneg_left (Nat.floor_le (Real.rpow_nonneg hrpos.le α)) hM.le).trans_lt hlt⟩

lemma exists_near_far_crossing_reduction (hBall : External.BallGreenBounds)
    (θ K η p ϑ : ℝ) (hθ : 0 < θ) (hη : 0 < η) (hp : 0 < p) (hϑ : 1 ≤ ϑ) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧ ∃ r₀ : ℕ,
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ (x : Site 4) (level : ℝ),
          (LatticeProb.iidLaw 4 μ) {ζ | HasStarTopBottomCrossing ϑ r x {z | ballGreenField r ζ z ≤ level}} ≤
            (LatticeProb.iidLaw 4 μ) {ζ | HasStarTopBottomCrossing ϑ r x {z |
              finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ z ≤
                level + 2 * η * Real.log r}} + ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  obtain ⟨α, M, C₁, hα, hα1, hM, hC₁, r₁, hr₁, hcluster⟩ :=
    exists_near_component_diameter_bound hBall θ K η p ϑ hθ hη hp hϑ
  obtain ⟨C₂, hC₂, r₂, hosc⟩ := exists_aspect_rectangle_far_oscillation_box hBall θ K (M + 1) α η p ϑ
    hθ (by linarith) hα hη hϑ
  obtain ⟨r₃, hgap⟩ := (eventually_mesoscopic_gap hα1 (by linarith : 0 < M)).exists_forall_of_atTop
  refine ⟨α, C₁ + C₂, hα, hα1, add_pos hC₁ hC₂, max (max r₁ r₂) r₃, ?_⟩
  intro μ hμ hexp hK hmean r hr x level
  have hr1 : r₁ ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hr2 : r₂ ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hr3 : r₃ ≤ r := (le_max_right _ _).trans hr
  have hrge : 2 ≤ r := hr₁.trans hr1
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  let L : ℕ := ⌊(r : ℝ) ^ α⌋₊
  have hL : (1 : ℝ) ≤ L := by
    have hh : 1 ≤ L := (Nat.le_floor_iff (Real.rpow_nonneg hrpos.le α)).mpr
      (by simpa using Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ r)) hα.le)
    exact_mod_cast hh
  let δ := η * Real.log r
  have hδ : 0 ≤ δ := mul_nonneg hη.le (Real.log_natCast_nonneg r)
  let H (ζ : Site 4 → ℝ) (z : Site 4) := finiteKernelField (External.BallGreen.cutField r L farCutoff) ζ z
  let N (ζ : Site 4 → ℝ) (z : Site 4) := finiteKernelField (nearKernel r L farCutoff) ζ z
  let Ecl := {ζ : Site 4 → ℝ | ∃ a b : nearLowSites ϑ r L farCutoff x (-η * Real.log r) ζ,
    (starGraph.induce (nearLowSites ϑ r L farCutoff x (-η * Real.log r) ζ)).Reachable a b ∧
      M * L < dist (a : Site 4) (b : Site 4)}
  let Eosc := {ζ : Site 4 → ℝ | ∃ z w : planeRectangle ⌊ϑ * r⌋₊ r,
    (∀ i : Fin 2, |((w : Site 2) i : ℝ) - ((z : Site 2) i : ℝ)| ≤ (M + 1) * L) ∧
      δ < |H ζ (planeTranslate x z) - H ζ (planeTranslate x w)|}
  let Efar := {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x {z | H ζ z ≤ level + 2 * η * Real.log r}}
  let Eball := {ζ : Site 4 → ℝ | HasStarTopBottomCrossing ϑ r x {z | ballGreenField r ζ z ≤ level}}
  have hcprob : (LatticeProb.iidLaw 4 μ) Ecl ≤ ENNReal.ofReal (C₁ * (r : ℝ) ^ (-p)) :=
    hcluster μ hμ hexp hK hmean r hr1 farCutoff isCutoff_farCutoff x
  have hoprob : (LatticeProb.iidLaw 4 μ) Eosc ≤ ENNReal.ofReal (C₂ * (r : ℝ) ^ (-p)) :=
    hosc μ hμ hexp hK hmean r hr2 x
  have hsub : Eball ⊆ Efar ∪ (Ecl ∪ Eosc) := by
    intro ζ hball
    by_cases hc : ζ ∈ Ecl
    · exact Or.inr (Or.inl hc)
    by_cases ho : ζ ∈ Eosc
    · exact Or.inr (Or.inr ho)
    apply Or.inl
    have hdiam : ∀ a b : {z | z ∈ ballRect ϑ r x ∧ N ζ z ≤ -δ},
        (starGraph.induce {z | z ∈ ballRect ϑ r x ∧ N ζ z ≤ -δ}).Reachable a b →
          dist (a : Site 4) (b : Site 4) ≤ M * L := by
      have hh : ∀ a b : nearLowSites ϑ r L farCutoff x (-η * Real.log r) ζ,
          (starGraph.induce (nearLowSites ϑ r L farCutoff x (-η * Real.log r) ζ)).Reachable a b →
            dist (a : Site 4) (b : Site 4) ≤ M * L := by
        intro a b hab
        exact le_of_not_gt (fun hfar => hc ⟨a, b, hab, hfar⟩)
      have hlevel : -η * Real.log r = -δ := by dsimp [δ]; ring
      rw [hlevel] at hh
      simpa only [nearLowSites, N] using hh
    have hos : ∀ z ∈ ballRect ϑ r x, ∀ w ∈ ballRect ϑ r x,
        dist z w ≤ M * L + 1 → |H ζ z - H ζ w| ≤ δ := by
      have hh := oscillation_on_ballRect (by linarith : 0 ≤ ϑ) r x (H ζ) ((M + 1) * L) δ
        (fun z w hcoords => le_of_not_gt (fun hlarge => ho ⟨z, w, hcoords, hlarge⟩))
      intro z hz w hw hd
      exact hh z hz w hw (hd.trans (by nlinarith))
    have hinput : HasStarTopBottomCrossing ϑ r x {z | ballGreenField r ζ z ≤ (level + δ) - δ} := by
      simpa only [Eball, mem_setOf_eq, add_sub_cancel_right] using hball
    have hh := star_crossing_field_split (fun z => ballGreenField r ζ z) (H ζ) (N ζ)
      (fun z => ballGreenField_eq_far_add_near r L farCutoff ζ z) hδ
      ((hgap r hr3).2) hdiam hos hinput
    change HasStarTopBottomCrossing ϑ r x {z | H ζ z ≤ level + 2 * η * Real.log r}
    have he : (level + δ) + δ = level + 2 * η * Real.log r := by dsimp [δ]; ring
    simpa only [he] using hh
  change (LatticeProb.iidLaw 4 μ) Eball ≤ (LatticeProb.iidLaw 4 μ) Efar + _
  calc
    _ ≤ (LatticeProb.iidLaw 4 μ) (Efar ∪ (Ecl ∪ Eosc)) := measure_mono hsub
    _ ≤ (LatticeProb.iidLaw 4 μ) Efar + (LatticeProb.iidLaw 4 μ) (Ecl ∪ Eosc) := measure_union_le _ _
    _ ≤ (LatticeProb.iidLaw 4 μ) Efar + ((LatticeProb.iidLaw 4 μ) Ecl + (LatticeProb.iidLaw 4 μ) Eosc) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ ≤ (LatticeProb.iidLaw 4 μ) Efar +
        (ENNReal.ofReal (C₁ * (r : ℝ) ^ (-p)) + ENNReal.ofReal (C₂ * (r : ℝ) ^ (-p))) :=
      add_le_add le_rfl (add_le_add hcprob hoprob)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

end Sandpile
