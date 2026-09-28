import Sandpile.Support.OdometerLocalization
import Sandpile.Frozen.DGT4Localization
import Mathlib.Data.Set.Finite.Powerset

/-!
# Decoupling odometer sublevel events on separated finite sets

Decoupling finite sublevel events through conditional odometers. The event
`sublevelWitnessEvent Q W F s` records that some subset `T ⊆ Q` satisfying a fixed property
`W` witnesses `F ω y ≤ -s` at every `y ∈ T`; it is measurable when `Q` is finite
(`measurableSet_sublevelWitnessEvent`), and it shifts by at most the sup-error between two
fields on `Q` (`sublevelWitnessEvent_shift`). For the recentred odometer field
`F = fun ω y => odometerOf ω t y - m` on two finite sets `K₁, K₂` whose `r`-thickenings are
disjoint, replacing `F` by its conditional expectation `G` given the coordinates on the
thickening makes the sublevel events independent (`coordAlg_inter_eq_mul`), while the tail
bound `Frozen.dgt4_localization` controls the resulting approximation error. Combining these
through the general two-set bound `measure_inter_le_sq_add_errors` gives the main result
`odometer_sublevel_decoupling`: if the sublevel events of `F` on `K₁` and `K₂` each have
probability at most `p`, their intersection has probability at most `p ^ 2` plus an explicit
error, exponentially small in `a` and `r` and linear in `|K₁| + |K₂|`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile

/-- The event that some subset `T ⊆ Q` satisfying the property `W` witnesses `F ω y ≤ -s` for
every `y ∈ T`: the sublevel event for `F` on `Q`, keyed by a witnessing sub-collection. -/
def sublevelWitnessEvent {V Ω : Type*} (Q : Set V) (W : Set V → Prop)
    (F : Ω → V → ℝ) (s : ℝ) : Set Ω :=
  {ω | ∃ T ⊆ Q, W T ∧ ∀ y ∈ T, F ω y ≤ -s}

/-- `sublevelWitnessEvent Q W F s` is measurable when `Q` is finite and each `F · y` is
measurable, by writing it as a countable union over finite subsets `T ⊆ Q` of the
finite intersection `⋂ y ∈ T, {ω | F ω y ≤ -s}`. -/
lemma measurableSet_sublevelWitnessEvent {V Ω : Type*} [MeasurableSpace Ω]
    (Q : Set V) (hQ : Q.Finite) (W : Set V → Prop) (F : Ω → V → ℝ)
    (hF : ∀ y, Measurable (fun ω => F ω y)) (s : ℝ) :
    MeasurableSet (sublevelWitnessEvent Q W F s) := by
  classical
  have he : sublevelWitnessEvent Q W F s =
      ⋃ T ∈ {T : Set V | T ⊆ Q}, {ω | W T ∧ ∀ y ∈ T, F ω y ≤ -s} := by
    ext ω
    simp only [sublevelWitnessEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor <;> rintro ⟨T, hT, hW, hval⟩ <;> exact ⟨T, hT, hW, hval⟩
  rw [he]
  refine MeasurableSet.biUnion hQ.finite_subsets.countable (fun T hT => ?_)
  by_cases hW : W T
  · simp only [hW, true_and]
    have heT : {ω | ∀ y ∈ T, F ω y ≤ -s} = ⋂ y ∈ T, {ω | F ω y ≤ -s} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heT]
    exact MeasurableSet.biInter (hQ.subset hT).countable (fun y _ =>
      measurableSet_le (hF y) measurable_const)
  · simp only [hW, false_and, Set.setOf_false, MeasurableSet.empty]

/-- If `F` and `G` differ by at most `a` in absolute value on `Q` at the point `ω`, then `ω`
lying in the level-`s` sublevel event of `F` puts it in the level-`(s - a)` sublevel event of
`G`, via the same witness set `T`. -/
lemma sublevelWitnessEvent_shift {V Ω : Type*} (Q : Set V) (W : Set V → Prop)
    (F G : Ω → V → ℝ) (s a : ℝ) (ω : Ω)
    (h : ∀ y ∈ Q, |F ω y - G ω y| ≤ a) :
    ω ∈ sublevelWitnessEvent Q W F s → ω ∈ sublevelWitnessEvent Q W G (s - a) := by
  rintro ⟨T, hT, hW, hval⟩
  refine ⟨T, hT, hW, fun y hy => ?_⟩
  have hdiff := (abs_le.mp (h y (hT hy))).1
  have hv := hval y hy
  linarith

/-- Events measurable with respect to the coordinate `σ`-algebras of two disjoint sets `S`,
`T` are independent under the i.i.d. product measure `Measure.infinitePi`, proved by pulling
the intersection back through the coordinate-recombination map `LatticeProb.comb` and using
`LatticeProb.measurePreserving_comb` together with `Measure.prod_prod`. -/
lemma coordAlg_inter_eq_mul {V : Type*} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (S T : Set V) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hST : Disjoint S T) {A B : Set (V → ℝ)}
    (hA : MeasurableSet[LatticeProb.coordAlg S] A)
    (hB : MeasurableSet[LatticeProb.coordAlg T] B) :
    (Measure.infinitePi fun _ : V => ν) (A ∩ B) =
      (Measure.infinitePi fun _ : V => ν) A * (Measure.infinitePi fun _ : V => ν) B := by
  classical
  have hAm : MeasurableSet A := (LatticeProb.coordAlg_le S) A hA
  have hBm : MeasurableSet B := (LatticeProb.coordAlg_le T) B hB
  have hpre : (fun p : (V → ℝ) × (V → ℝ) => LatticeProb.comb S p.1 p.2) ⁻¹'
      (A ∩ B) = A ×ˢ B := by
    ext p
    have hfirst := LatticeProb.mem_of_coordAlg hA p.1 p.2
    have hsecond := LatticeProb.mem_of_coordAlg hB (LatticeProb.comb S p.1 p.2) p.2
    have he : LatticeProb.comb T (LatticeProb.comb S p.1 p.2) p.2 = p.2 := by
      funext i
      by_cases hi : i ∈ T
      · have hn : i ∉ S := fun hs => Set.disjoint_left.mp hST hs hi
        simp [LatticeProb.comb, hi, hn]
      · simp [LatticeProb.comb, hi]
    rw [he] at hsecond
    change (LatticeProb.comb S p.1 p.2 ∈ A ∧ LatticeProb.comb S p.1 p.2 ∈ B) ↔
      (p.1 ∈ A ∧ p.2 ∈ B)
    rw [hfirst, ← hsecond]
  have hp := (LatticeProb.measurePreserving_comb (fun _ : V => ν) S).measure_preimage
    (hAm.inter hBm).nullMeasurableSet
  rw [hpre, Measure.prod_prod] at hp
  exact hp.symm

/-- If each `Aᵢ` is sandwiched between an approximating event `Bᵢ` and an error `Dᵢ`, `Bᵢ` is
in turn sandwiched between a tail event `Cᵢ` of measure at most `p ≤ 1` and `Dᵢ`, and `B₁`,
`B₂` are independent, then `μ (A₁ ∩ A₂) ≤ p ^ 2 + 2 * (μ D₁ + μ D₂)`; proved by bounding
`μ B₁ * μ B₂` termwise and covering `A₁ ∩ A₂` by `(B₁ ∩ B₂) ∪ (D₁ ∪ D₂)`. -/
lemma measure_inter_le_sq_add_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Set Ω)
    (hA₁ : A₁ ⊆ B₁ ∪ D₁) (hA₂ : A₂ ⊆ B₂ ∪ D₂)
    (hB₁ : B₁ ⊆ C₁ ∪ D₁) (hB₂ : B₂ ⊆ C₂ ∪ D₂)
    (hind : μ (B₁ ∩ B₂) = μ B₁ * μ B₂)
    (p : ℝ≥0∞) (hp : p ≤ 1) (hC₁ : μ C₁ ≤ p) (hC₂ : μ C₂ ≤ p) :
    μ (A₁ ∩ A₂) ≤ p ^ 2 + 2 * (μ D₁ + μ D₂) := by
  have hb₁ : μ B₁ ≤ p + μ D₁ := (measure_mono hB₁).trans
    ((measure_union_le C₁ D₁).trans (add_le_add hC₁ le_rfl))
  have hb₂ : μ B₂ ≤ p + μ D₂ := (measure_mono hB₂).trans
    ((measure_union_le C₂ D₂).trans (add_le_add hC₂ le_rfl))
  have hprod : μ B₁ * μ B₂ ≤ p ^ 2 + μ D₁ + μ D₂ := by
    calc
      _ ≤ (p + μ D₁) * μ B₂ := mul_le_mul' hb₁ le_rfl
      _ = p * μ B₂ + μ D₁ * μ B₂ := add_mul _ _ _
      _ ≤ p * (p + μ D₂) + μ D₁ * 1 :=
        add_le_add (mul_le_mul' le_rfl hb₂) (mul_le_mul' le_rfl (prob_le_one))
      _ = p ^ 2 + p * μ D₂ + μ D₁ := by ring
      _ ≤ p ^ 2 + 1 * μ D₂ + μ D₁ :=
        add_le_add (add_le_add le_rfl (mul_le_mul' hp le_rfl)) le_rfl
      _ = p ^ 2 + μ D₁ + μ D₂ := by ring
  have hsub : A₁ ∩ A₂ ⊆ (B₁ ∩ B₂) ∪ (D₁ ∪ D₂) := by
    intro ω hω
    rcases hA₁ hω.1 with h₁ | h₁
    · rcases hA₂ hω.2 with h₂ | h₂
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr (Or.inr h₂)
    · exact Or.inr (Or.inl h₁)
  calc
    _ ≤ μ ((B₁ ∩ B₂) ∪ (D₁ ∪ D₂)) := measure_mono hsub
    _ ≤ μ (B₁ ∩ B₂) + μ (D₁ ∪ D₂) := measure_union_le _ _
    _ ≤ μ (B₁ ∩ B₂) + (μ D₁ + μ D₂) :=
      add_le_add le_rfl (measure_union_le _ _)
    _ = μ B₁ * μ B₂ + (μ D₁ + μ D₂) := by rw [hind]
    _ ≤ (p ^ 2 + μ D₁ + μ D₂) + (μ D₁ + μ D₂) := add_le_add hprod le_rfl
    _ = p ^ 2 + 2 * (μ D₁ + μ D₂) := by ring

/-- **Decoupling of odometer sublevel events on separated sets.** In dimension `d ≥ 5`, for
finite sets `K₁, K₂` whose `r`-thickenings (`Frozen.DGT4Localization.thickening`) are
disjoint, if the `(s - 2 * a)`-sublevel events of the recentred odometer
`fun ω y => odometerOf ω t y - m` on `K₁` and `K₂` each have probability at most `p`, then the
level-`s` sublevel events on `K₁` and `K₂` satisfy `μ (event₁ ∩ event₂) ≤ p ^ 2 + error`,
where `error` is exponentially small in `a` and `r` with the rate and constant `c` coming
from `Frozen.dgt4_localization`. The proof replaces the odometer by its conditional
expectation given the thickening's coordinates, which forces independence across the two
disjoint thickenings via `coordAlg_inter_eq_mul`, then folds the two approximation errors
into `measure_inter_le_sq_add_errors`. -/
lemma odometer_sublevel_decoupling (_hGH : External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => Real.exp (θ * |z|)) ν →
      ∫ z, Real.exp (θ * |z|) ∂ν ≤ K →
      ∀ (K₁ K₂ : Finset (Site d)) (r a : ℝ), 1 ≤ r → 0 < a →
        Disjoint (Frozen.DGT4Localization.thickening K₁ r)
          (Frozen.DGT4Localization.thickening K₂ r) →
      ∀ (t : ℕ) (m : ℝ) (W₁ W₂ : Set (Site d) → Prop) (s : ℝ) (p : ℝ≥0∞),
        p ≤ 1 →
        (LatticeProb.iidLaw d ν) (sublevelWitnessEvent (K₁ : Set (Site d)) W₁
          (fun ω y => odometerOf ω t y - m) (s - 2 * a)) ≤ p →
        (LatticeProb.iidLaw d ν) (sublevelWitnessEvent (K₂ : Set (Site d)) W₂
          (fun ω y => odometerOf ω t y - m) (s - 2 * a)) ≤ p →
        (LatticeProb.iidLaw d ν)
          (sublevelWitnessEvent (K₁ : Set (Site d)) W₁ (fun ω y => odometerOf ω t y - m) s ∩
            sublevelWitnessEvent (K₂ : Set (Site d)) W₂ (fun ω y => odometerOf ω t y - m) s) ≤
          p ^ 2 + ENNReal.ofReal (4 * ((K₁.card : ℝ) + K₂.card) *
            Real.exp (-(c * min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2))))) := by
  classical
  obtain ⟨c, hc, htail⟩ := Frozen.dgt4_localization d hd θ K hθ
  refine ⟨c, hc, ?_⟩
  intro ν hν hmean hvp hvf hexp hK K₁ K₂ r a hr ha hdisj t m W₁ W₂ s p hp hC₁ hC₂
  haveI := hν
  let F := fun (ω : Site d → ℝ) y => odometerOf ω t y - m
  let S := fun (J : Finset (Site d)) => Frozen.DGT4Localization.thickening J r
  let G := fun (J : Finset (Site d)) (ω : Site d → ℝ) (y : Site d) =>
    (MeasureTheory.condExp
      (MeasurableSpace.comap (fun ω : Site d → ℝ => fun z : S J => ω z) inferInstance)
      (LatticeProb.iidLaw d ν) (fun ω => odometerOf ω t y)) ω - m
  let D := fun (J : Finset (Site d)) => {ω : Site d → ℝ | ∃ y ∈ J, a < |F ω y - G J ω y|}
  let B := fun (J : Finset (Site d)) W => sublevelWitnessEvent (J : Set (Site d)) W (G J) (s - a)
  have hgood (J : Finset (Site d)) (ω : Site d → ℝ) (hω : ω ∉ D J) :
      ∀ y ∈ (J : Set (Site d)), |F ω y - G J ω y| ≤ a := by
    intro y hy
    exact not_lt.mp (fun h => hω ⟨y, hy, h⟩)
  have hforward (J : Finset (Site d)) W :
      sublevelWitnessEvent (J : Set (Site d)) W F s ⊆ B J W ∪ D J := by
    intro ω hω
    by_cases he : ω ∈ D J
    · exact Or.inr he
    · exact Or.inl (sublevelWitnessEvent_shift _ W F (G J) s a ω (hgood J ω he) hω)
  have hback (J : Finset (Site d)) W :
      B J W ⊆ sublevelWitnessEvent (J : Set (Site d)) W F (s - 2 * a) ∪ D J := by
    intro ω hω
    by_cases he : ω ∈ D J
    · exact Or.inr he
    · have hg : ∀ y ∈ (J : Set (Site d)), |G J ω y - F ω y| ≤ a := by
        intro y hy
        rw [abs_sub_comm]
        exact hgood J ω he y hy
      have hh := sublevelWitnessEvent_shift _ W (G J) F (s - a) a ω hg hω
      rw [show s - a - a = s - 2 * a by ring] at hh
      exact Or.inl hh
  have hBm (J : Finset (Site d)) W :
      MeasurableSet[LatticeProb.coordAlg (S J)] (B J W) := by
    apply @measurableSet_sublevelWitnessEvent (Site d) (Site d → ℝ)
      (LatticeProb.coordAlg (S J)) _ J.finite_toSet W (G J) _ (s - a)
    intro y
    have hg : Measurable[LatticeProb.coordAlg (S J)]
        (fun ω => (MeasureTheory.condExp
          (MeasurableSpace.comap (fun ω : Site d → ℝ => fun z : S J => ω z) inferInstance)
          (LatticeProb.iidLaw d ν) (fun ω => odometerOf ω t y)) ω) := by
      rw [coordAlg_eq_restriction]
      exact stronglyMeasurable_condExp.measurable
    exact hg.sub measurable_const
  have hind : (LatticeProb.iidLaw d ν) (B K₁ W₁ ∩ B K₂ W₂) =
      (LatticeProb.iidLaw d ν) (B K₁ W₁) * (LatticeProb.iidLaw d ν) (B K₂ W₂) :=
    coordAlg_inter_eq_mul ν (S K₁) (S K₂) hdisj (hBm K₁ W₁) (hBm K₂ W₂)
  have he := measure_inter_le_sq_add_errors (LatticeProb.iidLaw d ν)
    (sublevelWitnessEvent (K₁ : Set (Site d)) W₁ F s)
    (sublevelWitnessEvent (K₂ : Set (Site d)) W₂ F s)
    (B K₁ W₁) (B K₂ W₂)
    (sublevelWitnessEvent (K₁ : Set (Site d)) W₁ F (s - 2 * a))
    (sublevelWitnessEvent (K₂ : Set (Site d)) W₂ F (s - 2 * a)) (D K₁) (D K₂)
    (hforward K₁ W₁) (hforward K₂ W₂) (hback K₁ W₁) (hback K₂ W₂) hind p hp hC₁ hC₂
  let e := Real.exp (-(c * min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2))))
  have hepos : 0 ≤ e := (Real.exp_pos _).le
  have hD (J : Finset (Site d)) :
      (LatticeProb.iidLaw d ν) (D J) ≤ ENNReal.ofReal (2 * (J.card : ℝ) * e) := by
    simpa only [D, F, G, S, sub_sub_sub_cancel_right] using
      htail ν hν hmean hvp hvf hexp hK J r a hr ha t
  refine he.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ 2 * (ENNReal.ofReal (2 * (K₁.card : ℝ) * e) +
        ENNReal.ofReal (2 * (K₂.card : ℝ) * e)) :=
      mul_le_mul' le_rfl (add_le_add (hD K₁) (hD K₂))
    _ = ENNReal.ofReal (4 * ((K₁.card : ℝ) + K₂.card) * e) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end Sandpile
