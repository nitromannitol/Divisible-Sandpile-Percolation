/-
Stochastic Fubini for the actual continuous Gaussian heat potential.

Coordinatewise modifications of a field do not determine values at random
parameters. Almost-sure continuity on a separable time-space domain supplies a
joint representative agreeing at every parameter on one common event. The
continuity clauses on positive time strips supply that event on all nonnegative
times. This transfers white-noise Fubini to the continuous field itself.

For a bounded measurable stopping time, continuity and measurability of the
motion make the stopped time-space parameter measurable. The Green-kernel L2
bound then discharges Bochner integrability, so the resulting identity concerns
the actual stopped continuous field. Its almost-sure event is for each fixed
stopping time; an event uniform over all stopping times requires a further
semigroup or martingale argument.
-/
import Sandpile.Support.ExplNoiseFubini
import Sandpile.Support.ExplKernelFamily

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

theorem exists_joint_version_of_ae_continuous {E Ω : Type*}
    [Nonempty E] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) (Z : E → Ω → ℝ)
    (hm : ∀ x, AEMeasurable (Z x) P)
    (hc : ∀ᵐ ω ∂P, Continuous fun x => Z x ω) :
    ∃ G : E → Ω → ℝ, StronglyMeasurable (Function.uncurry G) ∧
      ∀ᵐ ω ∂P, ∀ x, G x ω = Z x ω := by
  classical
  have hid : StronglyMeasurable (id : E → E) := stronglyMeasurable_id
  let s := hid.approx
  let Z0 (x : E) : Ω → ℝ := (hm x).mk (Z x)
  have hZ0 (x : E) : Measurable (Z0 x) := (hm x).measurable_mk
  let a (n : ℕ) (p : E × Ω) : ℝ := Z0 (s n p.1) p.2
  have ha (n : ℕ) : Measurable (a n) :=
    ((s n).comp Prod.fst measurable_fst).measurable_bind
      (fun x p => Z0 x p.2) (fun x => (hZ0 x).comp measurable_snd)
  have he (n : ℕ) : ∀ᵐ ω ∂P, ∀ x : (s n).range, Z0 x ω = Z x ω :=
    ae_all_iff.mpr (fun x => (hm x).ae_eq_mk.symm)
  have hall : ∀ᵐ ω ∂P, ∀ n, ∀ x : (s n).range, Z0 x ω = Z x ω :=
    ae_all_iff.mpr he
  refine ⟨fun x ω => limsup (fun n => a n (x, ω)) atTop,
    (Measurable.limsup ha).stronglyMeasurable, ?_⟩
  filter_upwards [hall, hc] with ω hω hcω
  intro x
  have ht : Tendsto (fun n => a n (x, ω)) atTop (𝓝 (Z x ω)) := by
    have hh := (hcω.tendsto x).comp (hid.tendsto_approx x)
    convert! hh using 1
    funext n
    exact hω n ⟨s n x, (s n).mem_range_self x⟩
  exact ht.limsup_eq


end Sandpile.Support

namespace Sandpile.Continuum

open Sandpile.Support

theorem whiteNoise_integral_comm_continuous {E Ω U : Type*}
    [Nonempty E] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω] [MeasurableSpace U]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (K : E → Space d → ℝ) (hK : ∀ x, MemLp (K x) 2 volume)
    (Z : E → Ω → ℝ) (hmod : ∀ x, Z x =ᵐ[P] W (K x))
    (hc : ∀ᵐ ω ∂P, Continuous fun x => Z x ω)
    (μ : Measure U) [SigmaFinite μ] (q : U → E) (hq : Measurable q)
    (hint : Integrable (fun u => (hK (q u)).toLp (K (q u))) μ) :
    (∀ᵐ ω ∂P, Integrable (fun u => Z (q u) ω) μ) ∧
      W (fun y => (∫ u, (hK (q u)).toLp (K (q u)) ∂μ) y) =ᵐ[P]
        fun ω => ∫ u, Z (q u) ω ∂μ := by
  obtain ⟨G, hGm, hG⟩ := exists_joint_version_of_ae_continuous P Z
    (fun x => (hW.meas _ (hK x)).aemeasurable.congr (hmod x).symm) hc
  have hgm : StronglyMeasurable (fun p : U × Ω => G (q p.1) p.2) :=
    hGm.comp_measurable ((hq.comp measurable_fst).prodMk measurable_snd)
  have hgeZ (u : U) : G (q u) =ᵐ[P] Z (q u) :=
    hG.mono fun ω hω => hω (q u)
  have hge (u : U) : G (q u) =ᵐ[P] W (K (q u)) :=
    (hgeZ u).trans (hmod (q u))
  have hi := whiteNoise_integral_comm_of_version hW μ (fun u => K (q u))
    (fun u => hK (q u)) hint (fun u ω => G (q u) ω) hgm hge
  constructor
  · filter_upwards [hi.1.prod_left_ae, hG] with ω hiω hGω
    exact hiω.congr (Eventually.of_forall fun u => hGω (q u))
  · exact hi.2.trans (hG.mono fun ω hω => integral_congr_ae
      (Eventually.of_forall fun u => hω (q u)))


theorem ae_continuous_nonneg_of_time_strips {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → Space d → Ω → ℝ)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) :
    ∀ᵐ ω ∂P, Continuous (fun p : ℝ≥0 × Space d => Z p.1 p.2 ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
        (Set.Icc 0 (n + 1 : ℝ) ×ˢ Set.univ) :=
    ae_all_iff.mpr fun n => hc (n + 1) (by positivity)
  filter_upwards [hall] with ω hω
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨n, hn⟩ := exists_nat_gt (p.1 : ℝ)
  have hn' : (p.1 : ℝ) < (n + 1 : ℝ) := by linarith
  have hcut : Continuous (fun q : ℝ≥0 × Space d => Z (min (q.1 : ℝ) (n + 1 : ℝ)) q.2 ω) := by
    apply (hω n).comp_continuous (f := fun q : ℝ≥0 × Space d =>
      (min (q.1 : ℝ) (n + 1 : ℝ), q.2))
    · fun_prop
    · intro q
      exact ⟨⟨le_min q.1.property (by positivity), min_le_right _ _⟩, Set.mem_univ _⟩
  apply hcut.continuousAt.congr_of_eventuallyEq
  have ht : ∀ᶠ q : ℝ≥0 × Space d in 𝓝 p, (q.1 : ℝ) < (n + 1 : ℝ) :=
    (show ContinuousAt (fun q : ℝ≥0 × Space d => (q.1 : ℝ)) p from by fun_prop).eventually
      (gt_mem_nhds hn')
  filter_upwards [ht] with q hq
  rw [min_eq_left hq.le]


theorem gaussian_whiteNoise_integral_comm_continuous {Ω U : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (μ : Measure U) [IsFiniteMeasure μ] (q : U → ℝ≥0 × Space d) (hq : Measurable q)
    (T : ℝ≥0) (hT : ∀ u, (q u).1 ≤ T) :
    (∀ᵐ ω ∂P, Integrable (fun u => Z (q u).1 (q u).2 ω) μ) ∧
      W (fun y => (∫ u, Real.sqrt ν2 •
        (memLp_greenTimeBM hd hd3 (q u).1.property (q u).2).toLp
          (greenTimeBM d (q u).1 (q u).2) ∂μ) y) =ᵐ[P]
        fun ω => ∫ u, Z (q u).1 (q u).2 ω ∂μ := by
  let K (p : ℝ≥0 × Space d) : Space d → ℝ := Real.sqrt ν2 • greenTimeBM d p.1 p.2
  have hK (p : ℝ≥0 × Space d) : MemLp (K p) 2 volume :=
    (memLp_greenTimeBM hd hd3 p.1.property p.2).const_smul (Real.sqrt ν2)
  have hZ (p : ℝ≥0 × Space d) : Z p.1 p.2 =ᵐ[P] W (K p) :=
    (hmod p.1 p.1.property p.2).trans
      (hW.smul (Real.sqrt ν2) _ (memLp_greenTimeBM hd hd3 p.1.property p.2)).symm
  have hint : Integrable (fun u => (hK (q u)).toLp (K (q u))) μ :=
    (integrable_greenTimeBM_toLp_of_bounded_time μ hd hd3 q hq T hT).smul (Real.sqrt ν2)
  exact whiteNoise_integral_comm_continuous hW K hK (fun p => Z p.1 p.2) hZ
    (ae_continuous_nonneg_of_time_strips P Z hc) μ q hq hint

theorem measurable_stopped_spaceTime {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ t, StronglyMeasurable (B t)) (τ : Ω → ℝ≥0) (hτm : Measurable τ)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    Measurable (fun ω => (⟨(T : ℝ) - τ ω, sub_nonneg.mpr (hτT ω)⟩, B (τ ω) ω) :
      Ω → ℝ≥0 × Space d) := by
  have hj : StronglyMeasurable (Function.uncurry B) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hBc hBm
  have ht : Measurable (fun ω => (⟨(T : ℝ) - τ ω, sub_nonneg.mpr (hτT ω)⟩ : ℝ≥0)) :=
    (measurable_const.sub hτm.subtype_val).subtype_mk
  exact ht.prodMk (hj.measurable.comp (hτm.prodMk measurable_id))

theorem gaussianPotential_stopped_integral_comm {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, StronglyMeasurable (B t))
    (τ : ΩB → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∀ᵐ ω ∂PW, Integrable (fun b => Z ((T : ℝ) - τ b) (B (τ b) b) ω) PB) ∧
      W (fun y => (∫ b, Real.sqrt ν2 •
        (memLp_greenTimeBM hd hd3 (sub_nonneg.mpr (hτT b)) (B (τ b) b)).toLp
          (greenTimeBM d ((T : ℝ) - τ b) (B (τ b) b)) ∂PB) y) =ᵐ[PW]
        fun ω => ∫ b, Z ((T : ℝ) - τ b) (B (τ b) b) ω ∂PB := by
  let q (b : ΩB) : ℝ≥0 × Space d :=
    (⟨(T : ℝ) - τ b, sub_nonneg.mpr (hτT b)⟩, B (τ b) b)
  have hq : Measurable q := measurable_stopped_spaceTime B hBc hBm τ hτm T hτT
  exact gaussian_whiteNoise_integral_comm_continuous hd hd3 hW ν2 Z hmod hc PB q hq T
    (fun b => show (T : ℝ) - τ b ≤ T from sub_le_self _ (τ b).property)

end Sandpile.Continuum
