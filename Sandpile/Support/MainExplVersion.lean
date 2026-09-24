/-
Versions of the field coupling and the deterministic growth bound for a
CONTINUOUS VERSION of the Gaussian heat potential.

The binder `hZmod` of `thm:main-explosion`(i)(b) only identifies the field `Z`
with the Gaussian potential `gaussianPotential` almost surely at each point, and
the binders `hZcont` and `hZgrow` are about `Z` itself.  The coupling
`Sandpile.Continuum.heat_field_coupling` and the growth bound
`Sandpile.Support.exists_deterministic_growth_ae` ask for continuity and
measurability of the Gaussian potential, which a modification does not have:
they are redone here with the almost-surely-continuous field `Z` itself, whose
point evaluations are only almost-everywhere measurable.  The
finite-dimensional convergence is transported from the Gaussian potential to
`Z` by the almost sure equality at each of the finitely many points, and the
growth events are only null measurable, which suffices for the decreasing
intersection argument.
-/
import Sandpile.Support.KillFieldCoupling
import Sandpile.Support.MainExplGrowth
import Sandpile.Support.ContBMSquare

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- **The field coupling at a continuous version of the Gaussian potential.**
This is `Sandpile.Continuum.heat_field_coupling` with the conclusion evaluated
at the version `Z` instead of the Gaussian potential itself: the version is
almost surely equal to the potential at each point, so the finite-dimensional
convergence transports, and continuity on the strip is a hypothesis on `Z`. -/
theorem Sandpile.Continuum.heat_field_coupling_of_version
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (ΩW : Type*) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (T : ℝ) (_hT : 0 < T)
    (hZcont : ∀ᵐ ω ∂PW, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d =>
        Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Sandpile.Continuum.Space d),
        (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
        TendstoInDistribution
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (i : Fin m) =>
            Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
              (Sandpile.scenery d σ) (r i) (w i))
          atTop
          (fun (ω : ΩW) (i : Fin m) =>
            Sandpile.Continuum.gaussianPotential d (variance id ν) W (r i) (w i) ω)
          (fun _ => Sandpile.centeredMassLaw d ν) PW)
    (htight : ∀ K : Set (ℝ × Sandpile.Continuum.Space d), IsCompact K →
        K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) →
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, M < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                (Sandpile.scenery d σ) p.1 p.2|} ≤ ENNReal.ofReal ε) ∧
        (∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 1 ≤ R →
          (Sandpile.centeredMassLaw d ν)
              {σ | ∃ p ∈ K, ∃ q ∈ K, dist p q < δ ∧
                η < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) p.1 p.2 -
                  Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                    (Sandpile.scenery d σ) q.1 q.2|} ≤ ENNReal.ofReal ε))
    (K : Set (ℝ × Sandpile.Continuum.Space d)) (hK : IsCompact K)
    (hKT : K ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d ν ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ q ∈ K,
            ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
                  (Sandpile.scenery d p.1) q.1 q.2 - Z q.1 q.2 p.2|}
          ≤ ENNReal.ofReal δ := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  set f : ℝ → (Sandpile.Site d → ℝ) → K → ℝ := fun R σ q =>
    Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) q.1.1 q.1.2
    with hfdef
  set g : ΩW → K → ℝ := fun ω q => Z q.1.1 q.1.2 ω with hgdef
  have hgaussmeas : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d), 0 ≤ t →
      Measurable (fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω) := by
    intro t x ht
    exact measurable_const.mul
      (hW.meas _ (Sandpile.Support.memLp_greenTimeBM hd hd3 ht x))
  have hfd : ∀ (m : ℕ) (x : Fin m → K), TendstoInDistribution
      (fun R σ i => f R σ (x i)) atTop (fun ω i => g ω (x i))
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
    intro m x
    have hbase := hfdd m (fun i => (x i).1.1) (fun i => (x i).1.2)
      (fun i => (hKT (x i).property).1)
    refine hbase.congr (fun R => Filter.EventuallyEq.rfl) ?_
    have hpts : ∀ i, (fun ω => Sandpile.Continuum.gaussianPotential d (variance id ν) W
        ((x i).1.1) ((x i).1.2) ω) =ᵐ[PW] (fun ω => Z (x i).1.1 (x i).1.2 ω) :=
      fun i => (hZmod (x i).1.1 (x i).1.2).symm
    filter_upwards [ae_all_iff.mpr hpts] with ω hω
    funext i
    exact hω i
  have hgm : ∀ q : K, AEMeasurable (fun ω => g ω q) PW := by
    intro q
    exact (hgaussmeas q.1.1 q.1.2 (hKT q.property).1.1).aemeasurable.congr
      (hZmod q.1.1 q.1.2).symm
  have hgc : ∀ᵐ ω ∂PW, Continuous (g ω) := by
    filter_upwards [hZcont] with ω hω
    exact hω.comp_continuous continuous_subtype_val (fun q => hKT q.property)
  have heq : ∀ a b : ℝ, 0 < a → 0 < b → ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ R : ℝ in atTop,
      (Sandpile.centeredMassLaw d ν)
        {σ | ∃ x y : K, dist x y < ρ ∧ b < |f R σ x - f R σ y|} ≤ ENNReal.ofReal a := by
    intro a b ha hb
    obtain ⟨ρ, hρ, hr⟩ := (htight K hK hKT).2 a b ha hb
    refine ⟨ρ, hρ, (eventually_ge_atTop (1 : ℝ)).mono fun R hR => ?_⟩
    apply le_trans (measure_mono ?_) (hr R hR)
    rintro σ ⟨x, y, hxy, hv⟩
    exact ⟨x.1, x.property, y.1, y.property, hxy, hv⟩
  have h := Sandpile.Continuum.exists_field_coupling_on_compact
    (fun _ : ℝ => Sandpile.centeredMassLaw d ν) PW f g hgm hgc atTop hfd heq ε δ hε hδ
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 h
  refine ⟨max 1 R₀, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR
  obtain ⟨P, hP, hPf, hPs, hbad⟩ := hR₀ R ((le_max_right _ _).trans hR)
  refine ⟨P, hP, hPf, hPs, ?_⟩
  have he : {p : (Sandpile.Site d → ℝ) × ΩW | ∃ q ∈ K,
      ε < |Sandpile.Frozen.HeatPotentialInvariance.linInterp d R
        (Sandpile.scenery d p.1) q.1 q.2 - Z q.1 q.2 p.2|} =
      {p | ∃ q : K, ε < |f R p.1 q - g p.2 q|} := by
    ext p
    simp only [mem_setOf_eq, Subtype.exists, hfdef, hgdef]
    constructor <;> rintro ⟨q, hq, hv⟩ <;> exact ⟨q, hq, hv⟩
  rw [he]
  exact hbad

namespace Sandpile.Support

variable {d : ℕ}

/-- **The strip level event of a field with almost-everywhere measurable point
evaluations is null measurable** when the field is almost surely continuous on the
strip: off the null set where continuity fails, the event is the countable union
over a dense subset of the strip of level sets of the point evaluations. -/
theorem nullMeasurableSet_exists_strip_lt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hmeas : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      AEMeasurable (Z q.1 q.2) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (L : ℝ × Sandpile.Continuum.Space d → ℝ) (hL : Continuous L) :
    NullMeasurableSet {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ
        (Set.univ : Set (Sandpile.Continuum.Space d)),
      L q < |Z q.1 q.2 ω|} P := by
  classical
  obtain ⟨D, hDc, hDd⟩ :=
    TopologicalSpace.exists_countable_dense (ℝ × Sandpile.Continuum.Space d)
  set E : Set (ℝ × Sandpile.Continuum.Space d) := stripClamp T '' D with hE
  have hEc : E.Countable := hDc.image _
  have hEsub : E ⊆ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)) := by
    rintro _ ⟨x, -, rfl⟩; exact stripClamp_mem hT x
  have hEdense : Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))
      ⊆ closure E := by
    intro q hq
    have h2 : stripClamp T '' closure D ⊆ closure E :=
      image_closure_subset_closure_image (continuous_stripClamp T)
    rw [hDd.closure_eq] at h2
    have h3 : stripClamp T q ∈ closure E := h2 ⟨q, Set.mem_univ q, rfl⟩
    rwa [stripClamp_eq hq] at h3
  have hlev : ∀ q ∈ E, NullMeasurableSet {ω | L q < |Z q.1 q.2 ω|} P := by
    intro q hq
    have hset : MeasurableSet {ω | L q < |(hmeas q (hEsub hq)).mk (Z q.1 q.2) ω|} :=
      measurableSet_lt measurable_const (hmeas q (hEsub hq)).measurable_mk.abs
    refine NullMeasurableSet.congr hset.nullMeasurableSet ?_
    filter_upwards [(hmeas q (hEsub hq)).ae_eq_mk] with ω hω
    change (L q < |(hmeas q (hEsub hq)).mk (Z q.1 q.2) ω|) = (L q < |Z q.1 q.2 ω|)
    rw [hω]
  refine NullMeasurableSet.congr (NullMeasurableSet.biUnion hEc hlev) ?_
  filter_upwards [hcont] with ω hω
  have hiff : (ω ∈ ⋃ q ∈ E, {v | L q < |Z q.1 q.2 v|}) ↔
      (∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        L q < |Z q.1 q.2 ω|) := by
    constructor
    · intro h
      obtain ⟨q, hq, hlt⟩ := Set.mem_iUnion₂.mp h
      exact ⟨q, hEsub hq, hlt⟩
    · rintro ⟨q, hq, hlt⟩
      have hcw : ContinuousWithinAt
          (fun v : ℝ × Sandpile.Continuum.Space d => |Z v.1 v.2 ω| - L v)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) q :=
        (hω.abs.sub hL.continuousOn) q hq
      have hpos : 0 < |Z q.1 q.2 ω| - L q := by linarith
      have hev : ∀ᶠ v in nhdsWithin q
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))),
          0 < |Z v.1 v.2 ω| - L v := hcw.eventually (eventually_gt_nhds hpos)
      have hle : nhdsWithin q E ≤ nhdsWithin q
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) :=
        nhdsWithin_mono q hEsub
      haveI hne : (nhdsWithin q E).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (hEdense hq)
      have h1 : ∀ᶠ v in nhdsWithin q E, 0 < |Z v.1 v.2 ω| - L v := hev.filter_mono hle
      have h2 : ∀ᶠ v in nhdsWithin q E, v ∈ E := self_mem_nhdsWithin
      obtain ⟨v, hv⟩ := (h1.and h2).exists
      exact Set.mem_iUnion₂.mpr ⟨v, hv.2, by
        show L v < |Z v.1 v.2 ω|; linarith [hv.1]⟩
  exact propext hiff

/-- **One amplitude and one degree for a continuous version of the Gaussian
potential, valid off a measurable event of prescribed probability.**  This is
`Sandpile.Support.exists_deterministic_growth_ae` with almost-everywhere
measurable point evaluations instead of measurable ones: the growth events are
then only null measurable, which the decreasing intersection accepts, and the
bad event is taken through `toMeasurable`. -/
theorem exists_deterministic_growth_of_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (hmeas : ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      AEMeasurable (Z q.1 q.2) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun q : ℝ × Sandpile.Continuum.Space d => Z q.1 q.2 ω)
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∀ᵐ ω ∂P, ∃ C k : ℝ,
      ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z q.1 q.2 ω| ≤ C * (1 + ‖q.2‖) ^ k)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (N : Set Ω), MeasurableSet N ∧ P N ≤ ENNReal.ofReal δ ∧
      ∀ ω ∉ N, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Sandpile.Continuum.Space d,
        |Z s y ω| ≤ (m : ℝ) * (1 + ‖y‖) ^ m := by
  classical
  set Ev : ℕ → Set Ω := fun n =>
    {ω | ∃ q ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
      (n : ℝ) * (1 + ‖q.2‖) ^ n < |Z q.1 q.2 ω|} with hEv
  have hlevel : ∀ n : ℕ, Continuous
      (fun q : ℝ × Sandpile.Continuum.Space d => (n : ℝ) * (1 + ‖q.2‖) ^ n) := by
    intro n
    exact continuous_const.mul ((continuous_const.add continuous_snd.norm).pow n)
  have hEvn : ∀ n, NullMeasurableSet (Ev n) P := fun n =>
    nullMeasurableSet_exists_strip_lt P Z T hT hmeas hcont _ (hlevel n)
  have hanti : Antitone Ev := by
    intro n m hnm ω hω
    obtain ⟨q, hq, hlt⟩ := hω
    refine ⟨q, hq, lt_of_le_of_lt ?_ hlt⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
    have h2 : (1 + ‖q.2‖) ^ n ≤ (1 + ‖q.2‖) ^ m := pow_le_pow_right₀ h1 hnm
    have h3 : ((n : ℝ)) ≤ (m : ℝ) := by exact_mod_cast hnm
    have h4 : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ n := by positivity
    nlinarith [pow_nonneg (le_trans zero_le_one h1) m]
  have hnull : P (⋂ n, Ev n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hgrow)
    intro ω hω
    simp only [Set.mem_iInter, hEv, Set.mem_setOf_eq] at hω
    intro hgood
    obtain ⟨C, k, hCk⟩ := hgood
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (max k 1))
    obtain ⟨q, hq, hlt⟩ := hω n
    have hC : C ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
    have hk : k ≤ (n : ℝ) := le_of_lt (lt_of_le_of_lt
      (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
    have h1 : (1 : ℝ) ≤ 1 + ‖q.2‖ := by linarith [norm_nonneg q.2]
    have hrp : (1 + ‖q.2‖) ^ k ≤ (1 + ‖q.2‖) ^ ((n : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 hk
    have hnat : (1 + ‖q.2‖) ^ ((n : ℕ) : ℝ) = (1 + ‖q.2‖) ^ (n : ℕ) :=
      Real.rpow_natCast _ _
    have hb := hCk q hq
    have hpos : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ (n : ℕ) := by positivity
    have hCn : C * (1 + ‖q.2‖) ^ k ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := by
      rw [hnat] at hrp
      have hC0 : (0 : ℝ) ≤ C ∨ C < 0 := le_or_gt 0 C
      rcases hC0 with hC0 | hC0
      · calc C * (1 + ‖q.2‖) ^ k ≤ C * (1 + ‖q.2‖) ^ (n : ℕ) :=
              mul_le_mul_of_nonneg_left hrp hC0
          _ ≤ (n : ℝ) * (1 + ‖q.2‖) ^ (n : ℕ) := mul_le_mul_of_nonneg_right hC hpos
      · have hrk : (0 : ℝ) ≤ (1 + ‖q.2‖) ^ k := Real.rpow_nonneg (by positivity) k
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
    linarith
  have hten : Filter.Tendsto (fun n => P (Ev n)) Filter.atTop (nhds (P (⋂ n, Ev n))) :=
    tendsto_measure_iInter_atTop hEvn hanti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hten
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  obtain ⟨m, hm⟩ := (hten.eventually_lt_const hpos).exists
  refine ⟨m, toMeasurable P (Ev m), measurableSet_toMeasurable _ _, ?_, ?_⟩
  · rw [measure_toMeasurable]
    exact hm.le
  · intro ω hω s hs y
    have hnm : ω ∉ Ev m := fun h => hω (subset_toMeasurable _ _ h)
    have hlt : ¬ ((m : ℝ) * (1 + ‖y‖) ^ m < |Z s y ω|) :=
      fun h => hnm ⟨(s, y), ⟨hs, Set.mem_univ y⟩, h⟩
    exact not_lt.mp hlt

end Sandpile.Support
