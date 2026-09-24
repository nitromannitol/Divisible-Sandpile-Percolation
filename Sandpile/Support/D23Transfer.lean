/-
The probability transfer in `sandpile.tex:2645-2663`. Continuous crossings
produce eventual sampled good blocks. Continuity of measure for the measurable
finite-grid events controls their failure probability, and the coupling error
pays for the remaining level margin. The discrete laws may vary with the scale.
-/
import Sandpile.Support.D23Rectangle
import Sandpile.Support.D4CritBlock
import Sandpile.Support.CrossingContinuity

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- Coordinate measurability suffices for the finite good-block event. -/
theorem measurableSet_blockGood_field {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω → Site 2 → ℝ) (hF : ∀ z, Measurable (fun ω => F ω z))
    (R : ℕ) (l : ℝ) (z : Site 2) :
    MeasurableSet {ω | BlockGood R (F ω) l z} := by
  have hm (w h : ℕ) (f : planeRectangle w h → Site 2) :
      Measurable (fun ω => crossingValue (planeRectangle w h) (fun v => F ω (f v))) :=
    (measurable_crossingValue (isLatticeRectangle_planeRectangle w h)
      (planeRectangle_nonempty w h)).comp (measurable_pi_lambda _ (fun v => hF (f v)))
  exact (measurableSet_le measurable_const (hm _ _ _)).inter
    ((measurableSet_le measurable_const (hm _ _ _)).inter
      ((measurableSet_le measurable_const (hm _ _ _)).inter
        (measurableSet_le measurable_const (hm _ _ _))))

/-- Under a coupling, a bad discrete block requires a bad sampled limit block
or a uniform error exceeding the level margin. -/
theorem measure_bad_block_le_of_coupling
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (P : Measure (Ω × Ω'))
    (hfst : P.map Prod.fst = μ) (hsnd : P.map Prod.snd = ν)
    (F : Ω → Site 2 → ℝ) (G : Ω' → Site 2 → ℝ)
    (hF : ∀ z, Measurable (fun ω => F ω z))
    (hG : ∀ z, Measurable (fun ω => G ω z))
    (R : ℕ) (l η : ℝ) :
    μ {ω | ¬ BlockGood R (F ω) (l - η) 0} ≤
      ν {ω | ¬ BlockGood R (G ω) l 0} +
        P {p | ∃ z ∈ planeRectangle (4 * R) (4 * R), η < |F p.1 z - G p.2 z|} := by
  have hbadF : MeasurableSet {ω | ¬ BlockGood R (F ω) (l - η) 0} := (measurableSet_blockGood_field F hF R (l - η) 0).compl
  have hbadG : MeasurableSet {ω | ¬ BlockGood R (G ω) l 0} := (measurableSet_blockGood_field G hG R l 0).compl
  rw [← hfst, Measure.map_apply measurable_fst hbadF]
  rw [← hsnd, Measure.map_apply measurable_snd hbadG]
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  intro p hp
  by_cases hbad : ¬ BlockGood R (G p.2) l 0
  · exact Or.inl hbad
  right
  by_contra herr
  apply hp
  apply blockGood_mono_on R (G p.2) (F p.1) l (l - η) 0 _ (not_not.mp hbad)
  intro z hz hval
  have hshift : blockShift R 0 z = z := by
    funext i
    fin_cases i <;> simp [blockShift]
  rw [hshift] at hval ⊢
  have he : |F p.1 z - G p.2 z| ≤ η := le_of_not_gt (fun h => herr ⟨z, hz, h⟩)
  have := (abs_le.mp he).1
  linarith

/-- On any event carrying the four continuous crossings, the probabilities
of bad sampled blocks eventually lie below any strict upper bound on the
probability of the complementary event. -/
theorem eventually_measure_bad_sampled_block_lt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Space 2 → ℝ) (hXm : ∀ u, Measurable (fun ω => X ω u))
    (E : Set Ω) {l η : ℝ} (hη : 0 < η)
    (hE : ∀ ω ∈ E, Continuous (X ω) ∧
      Crosses ![0, 0] ![2, 2] 0 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 2] 1 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![4, 2] 0 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 4] 1 {u | l ≤ X ω u})
    (ε : ℝ≥0∞) (hε : P Eᶜ < ε) :
    ∀ᶠ R : ℕ in atTop,
      P {ω | ¬ BlockGood R (fun z => X ω (gridPt (1 / (R : ℝ)) z)) (l - η) 0} < ε := by
  let bad (R : ℕ) : Set Ω :=
    {ω | ¬ BlockGood R (fun z => X ω (gridPt (1 / (R : ℝ)) z)) (l - η) 0}
  have hbad (R : ℕ) : MeasurableSet (bad R) :=
    (measurableSet_blockGood_field _ (fun z => hXm _) R (l - η) 0).compl
  let tail (n : ℕ) : Set Ω := ⋃ R ≥ n, bad R
  have htail (n : ℕ) : MeasurableSet (tail n) := MeasurableSet.iUnion fun R =>
    MeasurableSet.iUnion fun _ => hbad R
  have hanti : Antitone tail := by
    intro n m hnm ω hω
    obtain ⟨R, hRm, hR⟩ := mem_iUnion₂.mp hω
    exact mem_iUnion₂.mpr ⟨R, hnm.trans hRm, hR⟩
  have hsub : (⋂ n, tail n) ⊆ Eᶜ := by
    intro ω hω hωE
    obtain ⟨hc, h₁, h₂, h₃, h₄⟩ := hE ω hωE
    obtain ⟨R₀, _, hR₀⟩ := blockGood_of_continuum_crossings hc hη h₁ h₂ h₃ h₄
    obtain ⟨R, hR, hbadR⟩ := mem_iUnion₂.mp (mem_iInter.mp hω R₀)
    exact hbadR (hR₀ R hR _ (l - η) (fun z _ hz => hz.le))
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun n => (htail n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hsmall : P (⋂ n, tail n) < ε := (measure_mono hsub).trans_lt hε
  filter_upwards [hlim.eventually (gt_mem_nhds hsmall)] with R hR
  apply lt_of_le_of_lt (measure_mono ?_) hR
  intro ω hω
  exact mem_iUnion₂.mpr ⟨R, le_rfl, hω⟩

/-- The continuum crossing event and a vanishing coupling error exclude bad
blocks along a diverging sequence of scales, allowing the discrete law to vary. -/
theorem eventually_measure_bad_block_lt_of_couplings
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (laws : ℕ → Measure Ω) (P : Measure Ω') [IsProbabilityMeasure P]
    (Rs : ℕ → ℕ) (hRs : Tendsto Rs atTop atTop)
    (F : ℕ → Ω → Site 2 → ℝ) (hF : ∀ n z, Measurable (fun ω => F n ω z))
    (X : Ω' → Space 2 → ℝ) (hXm : ∀ u, Measurable (fun ω => X ω u))
    (E : Set Ω') {l η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hE : ∀ ω ∈ E, Continuous (X ω) ∧
      Crosses ![0, 0] ![2, 2] 0 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 2] 1 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![4, 2] 0 {u | l ≤ X ω u} ∧
      Crosses ![0, 0] ![2, 4] 1 {u | l ≤ X ω u})
    (hprob : P Eᶜ < ENNReal.ofReal (δ / 2))
    (hcoup : ∀ᶠ n : ℕ in atTop, ∃ Q : Measure (Ω × Ω'),
      Q.map Prod.fst = laws n ∧ Q.map Prod.snd = P ∧
      Q {p | ∃ z ∈ planeRectangle (4 * Rs n) (4 * Rs n),
        η < |F n p.1 z - X p.2 (gridPt (1 / (Rs n : ℝ)) z)|} ≤ ENNReal.ofReal (δ / 2)) :
    ∀ᶠ n : ℕ in atTop,
      laws n {ω | ¬ BlockGood (Rs n) (F n ω) (l - 2 * η) 0} < ENNReal.ofReal δ := by
  have hsample := eventually_measure_bad_sampled_block_lt P X hXm E hη hE
    (ENNReal.ofReal (δ / 2)) hprob
  filter_upwards [hRs.eventually hsample, hcoup] with n hn hc
  obtain ⟨Q, hQf, hQs, hQerr⟩ := hc
  have hbound := measure_bad_block_le_of_coupling (laws n) P Q hQf hQs (F n)
    (fun ω z => X ω (gridPt (1 / (Rs n : ℝ)) z)) (hF n) (fun z => hXm _)
    (Rs n) (l - η) η
  rw [show l - η - η = l - 2 * η by ring] at hbound
  apply hbound.trans_lt
  calc
    _ < ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
      ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hQerr) hn hQerr
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Sandpile.Support
