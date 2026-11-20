import Sandpile.External.RSW.Association
import Sandpile.External.RSW.Homeomorphisms
import Sandpile.Support.RectangleMonotonicity

/-!
# Uniform crossing bounds on bounded scales

For bounded scales, positive association and translation invariance control a crossing by
one-point superlevel probabilities. This gives a single comparison function for all scales
below a fixed bound.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- The superlevel event at one lattice site. -/
def siteSuperlevel (z : Site 2) (level : ℝ) : Set (Site 2 → ℝ) :=
  {F | level ≤ F z}

/-- A one-site superlevel event is increasing. -/
theorem isUpperSet_siteSuperlevel (z : Site 2) (level : ℝ) :
    IsUpperSet (siteSuperlevel z level) := by
  intro F G hFG hF
  exact hF.trans (hFG z)

/-- A one-site superlevel event is measurable. -/
theorem measurableSet_siteSuperlevel (z : Site 2) (level : ℝ) :
    MeasurableSet (siteSuperlevel z level) :=
  measurableSet_le measurable_const (measurable_pi_apply z)

/-- Translation-invariant laws have the same one-site superlevel probability everywhere. -/
theorem measureReal_siteSuperlevel_eq (μ : Measure (Site 2 → ℝ))
    (hμ : IsSymmetricPlanarLaw μ) (z : Site 2) (level : ℝ) :
    μ.real (siteSuperlevel z level) = μ.real (siteSuperlevel 0 level) := by
  have he : (planarFieldShift z) ⁻¹' siteSuperlevel 0 level = siteSuperlevel z level := by
    ext F
    simp only [siteSuperlevel, mem_preimage, mem_ofPred_eq, planarFieldShift, zero_add]
  rw [← he]
  exact (hμ.1 z).measureReal_preimage (measurableSet_siteSuperlevel 0 level).nullMeasurableSet

/-- A crossing contains a superlevel site in its rectangle. -/
theorem planarCrossingEvent_subset_iUnion_siteSuperlevel (w h : ℕ) (level : ℝ) :
    planarCrossingEvent w h level ⊆ ⋃ z : planeRectangle w h, siteSuperlevel z level := by
  intro F hF
  obtain ⟨a, b, p, ha, hb, hp⟩ :=
    (le_crossingValue_iff_exists_walk (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) (fun z => F z) level).mp hF
  exact mem_iUnion.mpr ⟨a, hp a p.start_mem_support⟩

/-- If every site of a rectangle is above the level, the rectangle is crossed. -/
theorem iInter_siteSuperlevel_subset_planarCrossingEvent (w h : ℕ) (level : ℝ) :
    (⋂ z : planeRectangle w h, siteSuperlevel z level) ⊆ planarCrossingEvent w h level := by
  intro F hF
  obtain ⟨a, b, p, _, ha, hb, _⟩ :=
    (crossingValue_spec (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h) (fun z => F z)).2
  apply le_crossingValue_of_walk (isLatticeRectangle_planeRectangle w h) p ha hb
  intro z hz
  exact mem_iInter.mp hF z

/-- On a fixed finite box, one increasing isomorphism compares the crossing probabilities
of any two rectangles contained in that box. -/
theorem finite_box_crossing_comparison (W H : ℕ) :
    ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
        IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
        ∀ w h w' h' : ℕ, w ≤ W → h ≤ H → w' ≤ W → h' ≤ H → ∀ level : ℝ,
          (ψ (probabilityInUnitInterval μ (planarCrossingEvent w h level)) : ℝ) ≤
            μ.real (planarCrossingEvent w' h' level) := by
  let Q := planeRectangle W H
  let : Nonempty Q := ⟨⟨_, (planeRectangle_nonempty W H).choose_spec⟩⟩
  let K := Fintype.card Q
  have hK : 0 < K := Fintype.card_pos
  refine ⟨crossingComparisonIso (K : ℝ) (by exact_mod_cast hK), ?_⟩
  intro μ _ hsym hass w h w' h' hw hh hw' hh' level
  let A : Q → Set (Site 2 → ℝ) := fun z => siteSuperlevel z level
  let U := ⋃ z, A z
  let I := ⋂ z, A z
  let p := μ.real (siteSuperlevel 0 level)
  have hcover : planarCrossingEvent w h level ⊆ U := by
    intro F hF
    obtain ⟨z, hz⟩ := mem_iUnion.mp
      (planarCrossingEvent_subset_iUnion_siteSuperlevel w h level hF)
    have hzQ : (z : Site 2) ∈ Q := by
      have hz' := (mem_planeRectangle w h z).mp z.property
      apply (mem_planeRectangle W H z).mpr
      omega
    exact mem_iUnion.mpr ⟨⟨z, hzQ⟩, hz⟩
  have hinter : I ⊆ planarCrossingEvent w' h' level := by
    intro F hF
    apply iInter_siteSuperlevel_subset_planarCrossingEvent w' h' level
    apply mem_iInter.mpr
    intro z
    have hzQ : (z : Site 2) ∈ Q := by
      have hz' := (mem_planeRectangle w' h' z).mp z.property
      apply (mem_planeRectangle W H z).mpr
      omega
    exact mem_iInter.mp hF ⟨z, hzQ⟩
  have hU := measureReal_mono (μ := μ) hcover (measure_ne_top μ U)
  obtain ⟨z, hz⟩ := exists_measureReal_ge_sqrt_union μ hass A
    (fun z => isUpperSet_siteSuperlevel z level)
    (fun z => measurableSet_siteSuperlevel z level)
  have hsite : μ.real (A z) = p := measureReal_siteSuperlevel_eq μ hsym z level
  rw [hsite] at hz
  have hprod := prod_measureReal_le_biInter_of_upper μ hass A
    (fun z => isUpperSet_siteSuperlevel z level)
    (fun z => measurableSet_siteSuperlevel z level) Finset.univ
  have hp' (z : Q) : μ.real (A z) = p := measureReal_siteSuperlevel_eq μ hsym z level
  simp_rw [hp'] at hprod
  have hprod' : p ^ K ≤ μ.real I := by
    simpa only [Finset.mem_univ, iInter_true, Finset.prod_const, Finset.card_univ] using hprod
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hroot : (1 - μ.real U) ^ (1 / (K : ℝ)) ≤
      (1 - μ.real (planarCrossingEvent w h level)) ^ (1 / (K : ℝ)) :=
    Real.rpow_le_rpow (sub_nonneg.mpr measureReal_le_one) (by linarith) (by positivity)
  have hlower : 1 - (1 - μ.real (planarCrossingEvent w h level)) ^ (1 / (K : ℝ)) ≤ p := by
    linarith
  have hbase : 0 ≤ 1 - (1 - μ.real (planarCrossingEvent w h level)) ^ (1 / (K : ℝ)) := by
    apply sub_nonneg.mpr
    have hnonneg : 0 ≤ μ.real (planarCrossingEvent w h level) := measureReal_nonneg
    exact Real.rpow_le_one (sub_nonneg.mpr measureReal_le_one) (by linarith) (by positivity)
  have hpow := pow_le_pow_left₀ hbase hlower K
  have hi := measureReal_mono (μ := μ) hinter (measure_ne_top μ _)
  change (1 - (1 - μ.real (planarCrossingEvent w h level)) ^ (K : ℝ)⁻¹) ^ (K : ℝ) ≤ _
  rw [Real.rpow_natCast]
  simpa only [one_div] using hpow.trans (hprod'.trans hi)

/-- A single comparison function works for all aspect-two crossings at bounded scales. -/
theorem bounded_scale_crossing_comparison (M : ℕ) :
    ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
      ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
        IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
        ∀ n : ℕ, n ≤ M → ∀ level : ℝ,
          (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
            μ.real (planarCrossingEvent (4 * n) (2 * n) level) := by
  obtain ⟨ψ, hψ⟩ := finite_box_crossing_comparison (4 * M) (4 * M)
  refine ⟨ψ, ?_⟩
  intro μ _ hsym hass n hn level
  exact hψ μ hsym hass _ _ _ _ (by omega) (by omega) (by omega) (by omega) level

end Sandpile.External.RSW
