import Sandpile.Support.Barrier
import Sandpile.Support.Increment
import Sandpile.Support.Smoothed
import Sandpile.Support.Concentration
import Sandpile.Support.SceneryBridge
import LatticeProb.Prob.HarrisVariants

/-!
# The increment bound from a finite negative ball

The increment bound from a finite negative ball, `eq:dgt4-increment-finite-ball`
of `sandpile.tex:4187-4230`, in the scenery language.

Three ingredients.  The mean increment equals the mean of the reflected part, the
scenery form of `eq:dgt4-height-increment`.  Harris' inequality for a finite
family of decreasing events bounds below the probability of the event that the
scenery is very negative on a box and the odometer is at most twice its mean on
that box.  And on that event the parabolic barrier forces the neighbour average
at the origin below half the negative level, so the reflected part is at least
that half.  Counting the box gives the stretched exponential with exponent
`d/2`.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### Events of the scenery that are decreasing -/

/-- The sublevel event `{ζ | odometerOf ζ t z ≤ c}` is a lower set in the pointwise order on
scenery: since `odometerOf` is monotone in the scenery (`odometerOf_mono`), a scenery
pointwise below one whose odometer already clears the bound `c` clears it as well. -/
theorem isLowerSet_odometerOf_le (t : ℕ) (z : Site d) (c : ℝ) :
    IsLowerSet {ζ : Site d → ℝ | odometerOf ζ t z ≤ c} := by
  intro a b hle ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  exact le_trans (odometerOf_mono t z fun w => hle w) ha

/-- The coordinate sublevel event `{ζ | ζ z ≤ c}` is a lower set, since a pointwise-smaller
scenery has a pointwise-smaller value at `z`. -/
theorem isLowerSet_coord_le (z : Site d) (c : ℝ) :
    IsLowerSet {ζ : Site d → ℝ | ζ z ≤ c} := by
  intro a b hle ha
  simp only [Set.mem_setOf_eq] at ha ⊢
  exact le_trans (hle z) ha

/-- The sublevel event `{ζ | odometerOf ζ t z ≤ c}` is measurable, as the preimage of
`Set.Iic c` under the measurable function `odometerOf · t z`. -/
theorem measurableSet_odometerOf_le (t : ℕ) (z : Site d) (c : ℝ) :
    MeasurableSet {ζ : Site d → ℝ | odometerOf ζ t z ≤ c} :=
  measurableSet_le (measurable_odometerOf t z) measurable_const

/-- The coordinate sublevel event `{ζ | ζ z ≤ c}` is measurable, since evaluation at the
fixed site `z` is a measurable function. -/
theorem measurableSet_coord_le (z : Site d) (c : ℝ) :
    MeasurableSet {ζ : Site d → ℝ | ζ z ≤ c} :=
  measurableSet_le (measurable_pi_apply z) measurable_const

/-- **Harris for a finite family of decreasing events.** -/
theorem harris_biInter (ν : Measure ℝ) [IsProbabilityMeasure ν] {ι : Type*} [DecidableEq ι]
    (A : ι → Set (Site d → ℝ)) (hlow : ∀ i, IsLowerSet (A i))
    (hmeas : ∀ i, MeasurableSet (A i)) (s : Finset ι) :
    ∏ i ∈ s, (LatticeProb.iidLaw d ν).real (A i)
      ≤ (LatticeProb.iidLaw d ν).real (⋂ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hins : (⋂ i ∈ insert a s, A i) = A a ∩ ⋂ i ∈ s, A i := by
        ext u
        simp only [Finset.mem_insert, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨h a (Or.inl rfl), fun i hi => h i (Or.inr hi)⟩
        · rintro ⟨h1, h2⟩ i (rfl | hi)
          · exact h1
          · exact h2 i hi
      rw [Finset.prod_insert ha, hins]
      have hlowS : IsLowerSet (⋂ i ∈ s, A i) := by
        intro u v huv hu
        simp only [Set.mem_iInter] at hu ⊢
        exact fun i hi => hlow i huv (hu i hi)
      have hmeasS : MeasurableSet (⋂ i ∈ s, A i) :=
        MeasurableSet.biInter s.countable_toSet fun i _ => hmeas i
      have hharris := LatticeProb.infinitePi_harris_lower (fun _ : Site d => ν)
        (hlow a) hlowS (hmeas a) hmeasS
      refine le_trans ?_ hharris
      exact mul_le_mul_of_nonneg_left ih (measureReal_nonneg)

/-! ### The mean increment -/

/-- The coordinate at a site has the one-site law. -/
theorem integral_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν)
    (z : Site d) : ∫ ζ, ζ z ∂(LatticeProb.iidLaw d ν) = ∫ w, w ∂ν := by
  have hcoord : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ z) = ν :=
    Measure.infinitePi_map_eval _ z
  have h := integral_map (μ := LatticeProb.iidLaw d ν) (φ := fun ζ : Site d → ℝ => ζ z)
    (f := fun w : ℝ => w) (measurable_pi_apply z).aemeasurable
    (by rw [hcoord]; exact hint.aestronglyMeasurable)
  rw [hcoord] at h
  exact h.symm

/-- The coordinate map `ζ ↦ ζ z` is integrable under the i.i.d. law `LatticeProb.iidLaw d ν`
whenever the identity is integrable under `ν`, transported through the pushforward identity
`Measure.infinitePi_map_eval`. -/
theorem integrable_coord (ν : Measure ℝ) [IsProbabilityMeasure ν] (hint : Integrable id ν)
    (z : Site d) : Integrable (fun ζ : Site d → ℝ => ζ z) (LatticeProb.iidLaw d ν) := by
  have hcoord : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ z) = ν :=
    Measure.infinitePi_map_eval _ z
  have hasm : AEStronglyMeasurable (fun w : ℝ => w)
      ((LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ z)) := by
    rw [hcoord]; exact hint.aestronglyMeasurable
  refine (integrable_map_measure hasm (measurable_pi_apply z).aemeasurable).mp ?_
  rw [hcoord]; exact hint

/-- The neighbour average `avg (odometerOf ζ t) 0` of the odometer at the origin is
integrable under `LatticeProb.iidLaw d ν` whenever the positive part of `ν` is integrable,
being a finite sum of `2d` integrable odometer values (`integrable_odometerOf`) divided by a
constant. -/
theorem integrable_avg_odometerOf' (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) :
    Integrable (fun ζ : Site d → ℝ => avg (odometerOf ζ t) 0) (LatticeProb.iidLaw d ν) := by
  have hform : (fun ζ : Site d → ℝ => avg (odometerOf ζ t) 0)
      = fun ζ : Site d → ℝ =>
        (∑ i : Fin d, (odometerOf ζ t ((0 : Site d) + unit i)
          + odometerOf ζ t ((0 : Site d) - unit i))) / (2 * (d : ℝ)) := rfl
  rw [hform]
  refine Integrable.div_const ?_ _
  exact integrable_finsetSum _ fun i _ =>
    (integrable_odometerOf d ν hpos t _).add (integrable_odometerOf d ν hpos t _)

/-- The odometer recursion at the origin, `odometerOf ζ (t + 1) 0 = max 0 (ζ 0 + avg
(odometerOf ζ t) 0)`, rewrites via `max_zero_eq` as the raw update `ζ 0 + avg (odometerOf ζ
t) 0` plus its reflected (nonnegative) part `max 0 (-(ζ 0) - avg (odometerOf ζ t) 0)`. -/
theorem max_zero_reflected (ζ : Site d → ℝ) (t : ℕ) :
    odometerOf ζ (t + 1) 0
      = (ζ 0 + avg (odometerOf ζ t) 0) + max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) := by
  show max 0 (ζ 0 + avg (odometerOf ζ t) 0)
      = (ζ 0 + avg (odometerOf ζ t) 0) + max 0 (-(ζ 0) - avg (odometerOf ζ t) 0)
  rw [max_zero_eq (ζ 0 + avg (odometerOf ζ t) 0)]
  congr 2
  ring

/-- The reflected part `max 0 (-(ζ 0) - avg (odometerOf ζ t) 0)` of the odometer step at the
origin is integrable under `LatticeProb.iidLaw d ν`, obtained via `max_zero_reflected` as the
difference of the integrable odometer value at time `t + 1` and the integrable raw update at
time `t`. -/
theorem integrable_reflected (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) :
    Integrable (fun ζ : Site d → ℝ => max 0 (-(ζ 0) - avg (odometerOf ζ t) 0))
      (LatticeProb.iidLaw d ν) := by
  have h1 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (t + 1) 0) (LatticeProb.iidLaw d ν) :=
    integrable_odometerOf d ν hpos (t + 1) 0
  have hsum2 : Integrable (fun ζ : Site d → ℝ => ζ 0 + avg (odometerOf ζ t) 0)
      (LatticeProb.iidLaw d ν) :=
    (integrable_coord ν hint 0).add (integrable_avg_odometerOf' ν hpos t)
  refine (h1.sub hsum2).congr (Filter.Eventually.of_forall fun ζ => ?_)
  show odometerOf ζ (t + 1) 0 - (ζ 0 + avg (odometerOf ζ t) 0)
      = max 0 (-(ζ 0) - avg (odometerOf ζ t) 0)
  rw [max_zero_reflected ζ t]
  ring

/-- **The mean increment is the mean of the reflected part**, the scenery form of
`eq:dgt4-height-increment` of `sandpile.tex:4106-4110`. -/
theorem meanOdometerOf_succ_sub (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) :
    (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) ∂(LatticeProb.iidLaw d ν) := by
  set P := LatticeProb.iidLaw d ν with hP
  have havgint := integrable_avg_odometerOf' (d := d) ν hpos t
  have hsum2 : Integrable (fun ζ : Site d → ℝ => ζ 0 + avg (odometerOf ζ t) 0) P :=
    (integrable_coord ν hint 0).add havgint
  have hrefint := integrable_reflected (d := d) ν hint hpos t
  have havgmean : ∫ ζ, avg (odometerOf ζ t) 0 ∂P = ∫ ζ, odometerOf ζ t 0 ∂P := by
    have h := integral_avg_odometerOf (d := d) hd ν hpos 1 t 0
    simpa [Function.iterate_one] using h
  have hI : ∫ ζ, odometerOf ζ (t + 1) 0 ∂P
      = (∫ ζ, (ζ 0 + avg (odometerOf ζ t) 0) ∂P)
        + ∫ ζ, max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) ∂P := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ => max_zero_reflected ζ t)]
    exact integral_add hsum2 hrefint
  have hI2 : ∫ ζ, (ζ 0 + avg (odometerOf ζ t) 0) ∂P = ∫ ζ, odometerOf ζ t 0 ∂P := by
    rw [integral_add (integrable_coord ν hint 0) havgint, integral_coord ν hint 0, hmean,
      havgmean, zero_add]
  rw [hI, hI2]
  ring

/-! ### The cardinality of a box -/

/-- The finite box `boxFinset x r` of sites within sup-distance `r` of `x` has `(2r + 1) ^ d`
elements, by a product over coordinates of the cardinality of each integer interval
`Finset.Icc (x i - r) (x i + r)`. -/
theorem card_boxFinset (x : Site d) (r : ℕ) : (boxFinset x r).card = (2 * r + 1) ^ d := by
  classical
  rw [boxFinset, Fintype.card_piFinset]
  have hfac : ∀ i : Fin d, (Finset.Icc (x i - r) (x i + r)).card = 2 * r + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ### Markov's inequality for the odometer -/

/-- Markov's inequality for the odometer: the event that `odometerOf ζ t z` is at most
twice its mean plus one has probability at least `1/2`, since the complementary event that
it exceeds that threshold has probability at most `1/2` by
`mul_meas_ge_le_integral_of_nonneg`. -/
theorem half_le_measure_odometerOf_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) (z : Site d) :
    (1 : ℝ) / 2 ≤ (LatticeProb.iidLaw d ν).real
      {ζ : Site d → ℝ | odometerOf ζ t z ≤
        2 * (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw d ν)) + 1} := by
  set P := LatticeProb.iidLaw d ν with hP
  set m : ℝ := ∫ η, odometerOf η t 0 ∂P with hm
  have hm0 : 0 ≤ m := integral_odometerOf_nonneg d ν t 0
  set c : ℝ := 2 * m + 1 with hc
  have hc0 : (0 : ℝ) < c := by rw [hc]; linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ζ : Site d → ℝ => odometerOf ζ t z)
    (Filter.Eventually.of_forall fun ζ => odometerOf_nonneg ζ t z)
    (integrable_odometerOf d ν hpos t z) c
  rw [integral_odometerOf_eq d ν t z] at hmarkov
  have hge : P.real {ζ : Site d → ℝ | c ≤ odometerOf ζ t z} ≤ 1 / 2 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hmarkov, hm0]
  have hmeas : MeasurableSet {ζ : Site d → ℝ | odometerOf ζ t z ≤ c} :=
    measurableSet_odometerOf_le t z c
  have hcompl : {ζ : Site d → ℝ | odometerOf ζ t z ≤ c}ᶜ
      ⊆ {ζ : Site d → ℝ | c ≤ odometerOf ζ t z} := by
    intro ζ hζ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hζ
    exact le_of_lt hζ
  have hmono : P.real {ζ : Site d → ℝ | odometerOf ζ t z ≤ c}ᶜ ≤ 1 / 2 :=
    le_trans (measureReal_mono hcompl (measure_ne_top _ _)) hge
  rw [measureReal_compl hmeas] at hmono
  have : P.real Set.univ = 1 := by
    simp [hP]
  rw [this] at hmono
  linarith

/-! ### The increment from a finite negative ball -/

/-- **One step of the increment bound from a finite negative ball.**  If the
scenery is at most `-a` with probability at least `q` at every site, and the
radius `R` is large enough that the parabola `a|z|^2/2` clears twice the mean at
the sphere, then the mean increment is at least `a/2` times the probability that
the scenery is that negative on the whole box while the odometer stays at most
twice its mean there. -/
theorem increment_ball_step (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hcoord : ∀ z : Site d, q ≤ (LatticeProb.iidLaw d ν).real {ζ : Site d → ℝ | ζ z ≤ -a})
    (t R : ℕ) (hR1 : 1 ≤ R)
    (hRsq : 2 * (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) + 1
      ≤ a / 2 * (R : ℝ) ^ 2) :
    a / 2 * (q / 2) ^ (boxFinset (0 : Site d) R).card
      ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  set P := LatticeProb.iidLaw d ν with hP
  set m : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hm
  have hm0 : 0 ≤ m := integral_odometerOf_nonneg d ν t 0
  -- the events
  set c : ℝ := 2 * m + 1 with hc
  set A : Site d × Bool → Set (Site d → ℝ) := fun p =>
    if p.2 then {ζ : Site d → ℝ | odometerOf ζ t p.1 ≤ c} else {ζ : Site d → ℝ | ζ p.1 ≤ -a}
    with hA
  have hAlow : ∀ p, IsLowerSet (A p) := by
    intro p
    rw [hA]
    by_cases hb : p.2
    · simp only [hb, if_true]
      exact isLowerSet_odometerOf_le t p.1 c
    · simp only [hb]
      exact isLowerSet_coord_le p.1 (-a)
  have hAmeas : ∀ p, MeasurableSet (A p) := by
    intro p
    rw [hA]
    by_cases hb : p.2
    · simp only [hb, if_true]
      exact measurableSet_odometerOf_le t p.1 c
    · simp only [hb]
      exact measurableSet_coord_le p.1 (-a)
  set s : Finset (Site d × Bool) := boxFinset (0 : Site d) R ×ˢ (Finset.univ : Finset Bool)
    with hs
  set E : Set (Site d → ℝ) := ⋂ p ∈ s, A p with hE
  -- the probability of the event
  have hprodlow : (q / 2) ^ (boxFinset (0 : Site d) R).card ≤ ∏ p ∈ s, P.real (A p) := by
    rw [hs, Finset.prod_product]
    have hz : ∀ z ∈ boxFinset (0 : Site d) R,
        q / 2 ≤ ∏ b : Bool, P.real (A (z, b)) := by
      intro z _
      rw [Fintype.prod_bool]
      have h1 : q ≤ P.real (A (z, false)) := by
        rw [hA]; simpa using hcoord z
      have h2 : (1 : ℝ) / 2 ≤ P.real (A (z, true)) := by
        rw [hA]
        simpa using half_le_measure_odometerOf_le ν hpos t z
      have h1n : 0 ≤ P.real (A (z, false)) := measureReal_nonneg
      nlinarith
    calc (q / 2) ^ (boxFinset (0 : Site d) R).card
        = ∏ _z ∈ boxFinset (0 : Site d) R, (q / 2) := by
          rw [Finset.prod_const]
      _ ≤ ∏ z ∈ boxFinset (0 : Site d) R, ∏ b : Bool, P.real (A (z, b)) :=
          Finset.prod_le_prod (fun z _ => by positivity) hz
  have hPE : (q / 2) ^ (boxFinset (0 : Site d) R).card ≤ P.real E := by
    refine le_trans hprodlow ?_
    rw [hE]
    exact harris_biInter ν A hAlow hAmeas s
  -- on the event the reflected increment is at least `a/2`
  have hmemS : ∀ (z : Site d) (b : Bool), boxDist 0 z ≤ R → (z, b) ∈ s := by
    intro z b hz
    rw [hs, Finset.mem_product]
    exact ⟨mem_boxFinset hz, Finset.mem_univ b⟩
  have hEsub : E ⊆ {ζ : Site d → ℝ | a / 2 ≤ max 0 (-(ζ 0) - avg (odometerOf ζ t) 0)} := by
    intro ζ hζ
    rw [hE] at hζ
    simp only [Set.mem_iInter] at hζ
    have hζneg : ∀ z : Site d, boxDist 0 z ≤ R → ζ z ≤ -a := by
      intro z hz
      have := hζ (z, false) (hmemS z false hz)
      rw [hA] at this
      simpa using this
    have hbnd : ∀ u : ℕ, u ≤ t → ∀ z : Site d, boxDist 0 z = R →
        odometerOf ζ u z ≤ a / 2 * sqNorm z := by
      intro u hu z hz
      have h1 : odometerOf ζ u z ≤ odometerOf ζ t z := odometerOf_mono_time ζ z hu
      have h2 : odometerOf ζ t z ≤ c := by
        have := hζ (z, true) (hmemS z true (le_of_eq hz))
        rw [hA] at this
        simpa using this
      have h3 : ((R : ℕ) : ℝ) ^ 2 ≤ sqNorm z := by
        have := sq_boxDist_le_sqNorm z
        rwa [hz] at this
      have h4 : a / 2 * ((R : ℕ) : ℝ) ^ 2 ≤ a / 2 * sqNorm z :=
        mul_le_mul_of_nonneg_left h3 (by linarith)
      have h5 : c ≤ a / 2 * ((R : ℕ) : ℝ) ^ 2 := by rw [hc]; exact hRsq
      linarith
    have hpar := odometerOf_le_parabola hd ζ a ha.le R t hζneg hbnd
    have havgle := avg_odometerOf_le_half hd ζ a ha.le R hR1 t (hpar t le_rfl)
    have hz0 : ζ 0 ≤ -a := hζneg 0 (by rw [boxDist_self]; omega)
    simp only [Set.mem_setOf_eq]
    have hkey : a / 2 ≤ -(ζ 0) - avg (odometerOf ζ t) 0 := by linarith
    exact le_trans hkey (le_max_right _ _)
  have hrefint := integrable_reflected (d := d) ν hint hpos t
  have hincr : a / 2 * P.real E ≤ ∫ ζ, max 0 (-(ζ 0) - avg (odometerOf ζ t) 0) ∂P := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
      (f := fun ζ : Site d → ℝ => max 0 (-(ζ 0) - avg (odometerOf ζ t) 0))
      (Filter.Eventually.of_forall fun ζ => le_max_left _ _) hrefint (a / 2)
    refine le_trans ?_ hmk
    exact mul_le_mul_of_nonneg_left (measureReal_mono hEsub (measure_ne_top _ _)) (by positivity)
  have hid := meanOdometerOf_succ_sub hd ν hint hmean hpos t
  have hchain : a / 2 * (q / 2) ^ (boxFinset (0 : Site d) R).card ≤ a / 2 * P.real E :=
    mul_le_mul_of_nonneg_left hPE (by positivity)
  linarith [hincr, hid, hchain]

/-- **The increment bound from a finite ball**, `eq:dgt4-increment-finite-ball` of
`sandpile.tex:4182-4186`, in the scenery language.  The mean increment is at least
a stretched exponential of the mean, with exponent `d/2`. -/
theorem increment_finite_ball (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hcoord : ∀ z : Site d, q ≤ (LatticeProb.iidLaw d ν).real {ζ : Site d → ℝ | ζ z ≤ -a}) :
    ∀ t : ℕ,
      a / 2 * Real.exp (-((5 + 2 * Real.sqrt (6 / a)) ^ d * Real.log (2 / q)
          * ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) + 1) ^ ((d : ℝ) / 2)))
        ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
            - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  set P := LatticeProb.iidLaw d ν with hP
  have hq1 : q ≤ 1 := le_trans (hcoord 0) (by
    have := measureReal_le_one (μ := P) (s := {ζ : Site d → ℝ | ζ 0 ≤ -a})
    exact this)
  set K : ℝ := 5 + 2 * Real.sqrt (6 / a) with hK
  have hK0 : (0 : ℝ) < K := by
    have : (0 : ℝ) ≤ Real.sqrt (6 / a) := Real.sqrt_nonneg _
    rw [hK]; linarith
  set L : ℝ := Real.log (2 / q) with hL
  have hL0 : 0 < L := by
    rw [hL]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hq]
    linarith
  show ∀ t : ℕ, a / 2 * Real.exp (-(K ^ d * L
      * ((∫ ζ, odometerOf ζ t 0 ∂P) + 1) ^ ((d : ℝ) / 2)))
      ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂P) - ∫ ζ, odometerOf ζ t 0 ∂P
  intro t
  set m : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hm
  have hm0 : 0 ≤ m := integral_odometerOf_nonneg d ν t 0
  -- the radius
  set R : ℕ := 1 + ⌈Real.sqrt ((4 * m + 2) / a)⌉₊ with hR
  have hR1 : 1 ≤ R := by rw [hR]; omega
  have hRge : Real.sqrt ((4 * m + 2) / a) ≤ (R : ℝ) := by
    have h1 : Real.sqrt ((4 * m + 2) / a) ≤ (⌈Real.sqrt ((4 * m + 2) / a)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ((⌈Real.sqrt ((4 * m + 2) / a)⌉₊ : ℕ) : ℝ) ≤ (R : ℝ) := by
      rw [hR]; push_cast; linarith
    linarith
  have hRsq : 2 * m + 1 ≤ a / 2 * (R : ℝ) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (4 * m + 2) / a := by positivity
    have hsq : (4 * m + 2) / a ≤ (R : ℝ) ^ 2 := by
      have := Real.sq_sqrt hnn
      nlinarith [hRge, Real.sqrt_nonneg ((4 * m + 2) / a)]
    rw [div_le_iff₀ ha] at hsq
    linarith
  have hstep := increment_ball_step hd ν hint hmean hpos a q ha hq hcoord t R hR1 hRsq
  -- the counting bound
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (m + 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m + 1 by linarith)
    simpa using h
  have hs_le : Real.sqrt ((4 * m + 2) / a) ≤ Real.sqrt (6 / a) * Real.sqrt (m + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
    linarith
  have hRle : 2 * (R : ℝ) + 1 ≤ K * Real.sqrt (m + 1) := by
    have hceil : (⌈Real.sqrt ((4 * m + 2) / a)⌉₊ : ℝ) ≤ Real.sqrt ((4 * m + 2) / a) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (Real.sqrt_nonneg _))
    have hRR : (R : ℝ) ≤ Real.sqrt ((4 * m + 2) / a) + 2 := by
      rw [hR]; push_cast; linarith
    have h6 : (0 : ℝ) ≤ Real.sqrt (6 / a) := Real.sqrt_nonneg _
    rw [hK]
    nlinarith [hs_le, hsqrt1, h6]
  have hcard : ((boxFinset (0 : Site d) R).card : ℝ) ≤ K ^ d * (m + 1) ^ ((d : ℝ) / 2) := by
    rw [card_boxFinset]
    have hcast : (((2 * R + 1) ^ d : ℕ) : ℝ) = (2 * (R : ℝ) + 1) ^ d := by push_cast; ring
    rw [hcast]
    have hpow : (2 * (R : ℝ) + 1) ^ d ≤ (K * Real.sqrt (m + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) hRle d
    refine le_trans hpow (le_of_eq ?_)
    rw [mul_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((m + 1) ^ ((1 : ℝ) / 2)) d,
      ← Real.rpow_mul (by linarith)]
    congr 1
    ring
  -- assemble
  have hqhalf : (0 : ℝ) < q / 2 := by linarith
  have hinv : q / 2 = (2 / q)⁻¹ := by field_simp
  have hlogq : Real.log (q / 2) = -L := by rw [hinv, Real.log_inv, hL]
  have hpowexp : (q / 2) ^ (boxFinset (0 : Site d) R).card
      = Real.exp (((boxFinset (0 : Site d) R).card : ℝ) * Real.log (q / 2)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hqhalf _)]
  have hexple : Real.exp (-(K ^ d * L * (m + 1) ^ ((d : ℝ) / 2)))
      ≤ (q / 2) ^ (boxFinset (0 : Site d) R).card := by
    rw [hpowexp, hlogq]
    refine Real.exp_le_exp.mpr ?_
    have hrw : ((boxFinset (0 : Site d) R).card : ℝ) * (-L)
        = -(((boxFinset (0 : Site d) R).card : ℝ) * L) := by ring
    rw [hrw]
    have := mul_le_mul_of_nonneg_right hcard hL0.le
    linarith
  have hchain : a / 2 * Real.exp (-(K ^ d * L * (m + 1) ^ ((d : ℝ) / 2)))
      ≤ a / 2 * (q / 2) ^ (boxFinset (0 : Site d) R).card :=
    mul_le_mul_of_nonneg_left hexple (by positivity)
  linarith [hstep, hchain]

/-- The increment bound of `increment_finite_ball` repackaged with a single explicit
constant `C = (5 + 2√(6/a)) ^ d * log (2/q)`, absorbing the dimension- and tail-dependent
factor into one existential witness. -/
theorem exists_increment_finite_ball (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (hcoord : ∀ z : Site d, q ≤ (LatticeProb.iidLaw d ν).real {ζ : Site d → ℝ | ζ z ≤ -a}) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ,
      a / 2 * Real.exp (-(C * ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) + 1)
          ^ ((d : ℝ) / 2)))
        ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
            - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  have hq1 : q ≤ 1 := le_trans (hcoord 0) measureReal_le_one
  have hK0 : (0 : ℝ) < 5 + 2 * Real.sqrt (6 / a) := by
    have : (0 : ℝ) ≤ Real.sqrt (6 / a) := Real.sqrt_nonneg _
    linarith
  have hL0 : 0 < Real.log (2 / q) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hq]
    linarith
  exact ⟨(5 + 2 * Real.sqrt (6 / a)) ^ d * Real.log (2 / q), by positivity,
    increment_finite_ball hd ν hint hmean hpos a q ha hq hcoord⟩

/-! ### The stretched branch and the growth of the mean -/

/-- An event of one coordinate has the probability of the one-site law. -/
theorem measureReal_coord_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : Site d) (c : ℝ) :
    (LatticeProb.iidLaw d ν).real {ζ : Site d → ℝ | ζ z ≤ c} = ν.real (Set.Iic c) := by
  have hcoord : (LatticeProb.iidLaw d ν).map (fun ζ : Site d → ℝ => ζ z) = ν :=
    Measure.infinitePi_map_eval _ z
  have hset : {ζ : Site d → ℝ | ζ z ≤ c} = (fun ζ : Site d → ℝ => ζ z) ⁻¹' Set.Iic c := rfl
  rw [Measure.real, Measure.real, hset,
    ← Measure.map_apply (measurable_pi_apply z) measurableSet_Iic, hcoord]

/-- **The increment bound in the stretched branch.**  A ball of radius one
suffices if the negative level is taken to grow with the mean, and then the
lower tail of the one-site law at that level is what the increment costs. -/
theorem increment_stretched_step (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν)
    (γ a₀ A s₀ : ℝ) (hγ : 0 < γ) (ha₀ : 0 < a₀) (hA : 0 < A)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ENNReal.ofReal (a₀ * Real.exp (-(A * s ^ γ))) ≤ ν (Set.Iic (-s)))
    (t : ℕ)
    (hbig : s₀ ≤ 4 * (∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) + 2) :
    (a₀ / 2) ^ (3 ^ d) * Real.exp (-((3 : ℝ) ^ d * A * 6 ^ γ *
        ((∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) + 1) ^ γ))
      ≤ (∫ ζ, odometerOf ζ (t + 1) 0 ∂(LatticeProb.iidLaw d ν))
          - ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  set P := LatticeProb.iidLaw d ν with hP
  set m : ℝ := ∫ ζ, odometerOf ζ t 0 ∂P with hm
  have hm0 : 0 ≤ m := integral_odometerOf_nonneg d ν t 0
  set a : ℝ := 4 * m + 2 with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  set q : ℝ := a₀ * Real.exp (-(A * a ^ γ)) with hqdef
  have hq : 0 < q := by rw [hqdef]; positivity
  have hcoord : ∀ z : Site d, q ≤ P.real {ζ : Site d → ℝ | ζ z ≤ -a} := by
    intro z
    rw [measureReal_coord_le ν z (-a)]
    have h := htail a hbig
    have hqe : ENNReal.ofReal q ≤ ν (Set.Iic (-a)) := h
    have hfin : ν (Set.Iic (-a)) ≠ ⊤ := measure_ne_top _ _
    rw [Measure.real]
    have := ENNReal.toReal_le_toReal (ENNReal.ofReal_ne_top) hfin |>.mpr hqe
    rwa [ENNReal.toReal_ofReal hq.le] at this
  have hcard : (boxFinset (0 : Site d) 1).card = 3 ^ d := by
    rw [card_boxFinset]
  have hRsq : 2 * m + 1 ≤ a / 2 * ((1 : ℕ) : ℝ) ^ 2 := by
    rw [hadef]; norm_num; linarith
  have hstep := increment_ball_step hd ν hint hmean hpos a q ha hq hcoord t 1 le_rfl hRsq
  rw [hcard] at hstep
  refine le_trans ?_ hstep
  -- compare the two lower bounds
  have hqa : q / 2 = (a₀ / 2) * Real.exp (-(A * a ^ γ)) := by rw [hqdef]; ring
  have hpow : (q / 2) ^ (3 ^ d)
      = (a₀ / 2) ^ (3 ^ d) * Real.exp (-((3 ^ d : ℕ) * (A * a ^ γ))) := by
    rw [hqa, mul_pow, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hage : a ^ γ ≤ 6 ^ γ * (m + 1) ^ γ := by
    have h1 : a ≤ 6 * (m + 1) := by rw [hadef]; linarith
    have h2 : a ^ γ ≤ (6 * (m + 1)) ^ γ :=
      Real.rpow_le_rpow (by linarith) h1 hγ.le
    rwa [Real.mul_rpow (by norm_num) (by linarith)] at h2
  have hexpcmp : Real.exp (-((3 : ℝ) ^ d * A * 6 ^ γ * (m + 1) ^ γ))
      ≤ Real.exp (-((3 ^ d : ℕ) * (A * a ^ γ))) := by
    refine Real.exp_le_exp.mpr ?_
    have h3 : ((3 ^ d : ℕ) : ℝ) = (3 : ℝ) ^ d := by push_cast; ring
    rw [h3]
    have h4 : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
    have h5 : A * a ^ γ ≤ A * (6 ^ γ * (m + 1) ^ γ) := mul_le_mul_of_nonneg_left hage hA.le
    have h6 : (3 : ℝ) ^ d * (A * a ^ γ) ≤ (3 : ℝ) ^ d * (A * (6 ^ γ * (m + 1) ^ γ)) :=
      mul_le_mul_of_nonneg_left h5 h4.le
    have h7 : (3 : ℝ) ^ d * A * 6 ^ γ * (m + 1) ^ γ
        = (3 : ℝ) ^ d * (A * (6 ^ γ * (m + 1) ^ γ)) := by ring
    linarith
  have hc0 : (0 : ℝ) < (a₀ / 2) ^ (3 ^ d) := by positivity
  have hnn : (0 : ℝ) ≤ (a₀ / 2) ^ (3 ^ d)
      * Real.exp (-((3 : ℝ) ^ d * A * 6 ^ γ * (m + 1) ^ γ)) := by positivity
  have hhalf : (1 : ℝ) ≤ a / 2 := by rw [hadef]; linarith
  calc (a₀ / 2) ^ (3 ^ d) * Real.exp (-((3 : ℝ) ^ d * A * 6 ^ γ * (m + 1) ^ γ))
      ≤ a / 2 * ((a₀ / 2) ^ (3 ^ d)
          * Real.exp (-((3 : ℝ) ^ d * A * 6 ^ γ * (m + 1) ^ γ))) := by nlinarith
    _ ≤ a / 2 * ((a₀ / 2) ^ (3 ^ d) * Real.exp (-((3 ^ d : ℕ) * (A * a ^ γ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexpcmp hc0.le) (by linarith)

/-! ### Nondegeneracy -/

/-- A probability law almost surely equal to a point is that point's Dirac mass. -/
theorem eq_dirac_of_ae_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ᵐ z ∂ν, z = 0) : ν = Measure.dirac 0 := by
  have hc : ν {z : ℝ | z ≠ 0} = 0 := by
    rw [← ae_iff]
    exact h
  have hcompl : ({(0 : ℝ)}ᶜ : Set ℝ) = {z : ℝ | z ≠ 0} := by ext x; simp
  have hone : ν {(0 : ℝ)} = 1 := by
    have h1 := measure_add_measure_compl (μ := ν) (measurableSet_singleton (0 : ℝ))
    rw [hcompl, hc, add_zero] at h1
    rw [h1, measure_univ]
  ext s hs'
  rw [Measure.dirac_apply' _ hs']
  by_cases h0 : (0 : ℝ) ∈ s
  · rw [Set.indicator_of_mem h0]
    refine le_antisymm prob_le_one ?_
    calc (1 : ℝ≥0∞) = ν {(0 : ℝ)} := hone.symm
      _ ≤ ν s := measure_mono (by simpa using h0)
  · rw [Set.indicator_of_notMem h0]
    refine le_antisymm ?_ zero_le
    have hsub : s ⊆ {z : ℝ | z ≠ 0} := by
      intro x hx
      simp only [Set.mem_setOf_eq]
      rintro rfl
      exact h0 hx
    exact le_trans (measure_mono hsub) (le_of_eq hc)

/-- A nondegenerate mean-zero law charges a half-line to the left of the origin. -/
theorem exists_left_tail_pos (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) :
    ∃ a : ℝ, 0 < a ∧ 0 < ν (Set.Iic (-a)) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ n : ℕ, ν (Set.Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
    intro n
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact le_antisymm (hcon _ hp) zero_le
  have hIio : ν (Set.Iio (0 : ℝ)) = 0 := by
    have hcover : Set.Iio (0 : ℝ) ⊆ ⋃ n : ℕ, Set.Iic (-(1 / ((n : ℝ) + 1))) := by
      intro x hx
      simp only [Set.mem_Iio] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -x by linarith)
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_Iic]; linarith⟩
    refine le_antisymm ?_ zero_le
    refine le_trans (measure_mono hcover) (le_trans (measure_iUnion_le _) ?_)
    have hz : ∀ n : ℕ, ν (Set.Iic (-((n : ℝ) + 1)⁻¹)) = 0 := by
      intro n
      have := hzero n
      rwa [one_div] at this
    simp [hz]
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[ν] (id : ℝ → ℝ) := by
    rw [Filter.EventuallyLE, ae_iff]
    have hset : {x : ℝ | ¬ (0 : ℝ → ℝ) x ≤ id x} = Set.Iio 0 := by
      ext x; simp [not_le]
    rw [hset]
    exact hIio
  have hz0 : (id : ℝ → ℝ) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hmean
  exact hnondeg 0 (eq_dirac_of_ae_eq_zero ν (by filter_upwards [hz0] with z hz using hz))

/-! ### The mean lower bound with uniform constants -/

/-- **The mean lower bound with constants written in the lower tail alone.**  The
uniform half of `cor:dgt4-mean-lower`, in the scenery language: the constant and
the time from which the bound holds depend on the dimension and on the pair
`(a, q)` of a lower-tail bound, and on nothing else about the law. -/
theorem exists_mean_lower_uniform (hd1 : 1 ≤ d) (hd2 : (0 : ℝ) < (d : ℝ) / 2)
    (a q : ℝ) (ha : 0 < a) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → Integrable id ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal q ≤ ν (Set.Iic (-a)) →
        ∀ t : ℕ, t₀ ≤ t →
          c * (Real.log t) ^ ((2 : ℝ) / d) ≤
            ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  classical
  have hexp : (1 : ℝ) / ((d : ℝ) / 2) = (2 : ℝ) / (d : ℝ) := by rw [one_div, inv_div]
  obtain ⟨C₁, hC₁def⟩ : ∃ C : ℝ, C = (5 + 2 * Real.sqrt (6 / a)) ^ d * Real.log (2 / q) :=
    ⟨_, rfl⟩
  have hK0 : (0 : ℝ) < 5 + 2 * Real.sqrt (6 / a) := by
    have : (0 : ℝ) ≤ Real.sqrt (6 / a) := Real.sqrt_nonneg _
    linarith
  have hL0 : 0 < Real.log (2 / q) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hq0]
    linarith
  have hC₁ : 0 < C₁ := by rw [hC₁def]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = a / 2 * Real.exp (-(C₁ * 2 ^ ((d : ℝ) / 2))) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨min 1 ((1 / (2 * C₁ * 2 ^ ((d : ℝ) / 2))) ^ ((2 : ℝ) / (d : ℝ))),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _),
    max (2 * ⌈1 / δ⌉₊ + 3)
      (⌈(2 * ((4 / ((d : ℝ) / 2)) ^ (1 / ((d : ℝ) / 2))) / δ) ^ 4⌉₊ + 1),
    fun ν hprob hintν hmean htail t ht => ?_⟩
  haveI := hprob
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hintν.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  have humono : Monotone fun n : ℕ =>
      ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    refine monotone_nat_of_le_succ fun n => ?_
    exact integral_mono (integrable_odometerOf d ν hpos n 0)
      (integrable_odometerOf d ν hpos (n + 1) 0)
      fun ζ => odometerOf_le_succ ζ n 0
  have hcoord : ∀ z : Site d,
      q ≤ (LatticeProb.iidLaw d ν).real {ζ : Site d → ℝ | ζ z ≤ -a} := by
    intro z
    rw [measureReal_coord_le ν z (-a), Measure.real]
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top ν _)).mpr htail
    rwa [ENNReal.toReal_ofReal hq0.le] at this
  have hincr : ∀ n : ℕ,
      a / 2 * Real.exp (-(C₁ *
          ((∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) + 1) ^ ((d : ℝ) / 2)))
        ≤ (∫ ζ, odometerOf ζ (n + 1) 0 ∂(LatticeProb.iidLaw d ν))
            - ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    rw [hC₁def]
    exact increment_finite_ball hd1 ν hintν hmean hpos a q ha hq0 hcoord
  have hun0 : ∀ n : ℕ, 0 ≤ ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) :=
    fun n => integral_odometerOf_nonneg d ν n 0
  have hstepδ : ∀ n : ℕ,
      (∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) < 1 →
        δ ≤ (∫ ζ, odometerOf ζ (n + 1) 0 ∂(LatticeProb.iidLaw d ν))
            - ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    intro n hn
    refine le_trans ?_ (hincr n)
    rw [hδdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
    have hle : ((∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) + 1)
        ^ ((d : ℝ) / 2) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith [hun0 n]) (by linarith) hd2.le
    nlinarith [hC₁.le]
  have hN1 : ∀ n : ℕ, ⌈1 / δ⌉₊ ≤ n →
      max (0 : ℝ) 1 ≤ ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    intro n hn
    have := one_le_of_increment
      (fun n => ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν))
      (by simp [odometerOf]) humono δ hδ hstepδ n hn
    simpa using this
  have hδle : δ ≤ a / 2 := by
    rw [hδdef]
    have h1 : Real.exp (-(C₁ * 2 ^ ((d : ℝ) / 2))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
      nlinarith [hC₁.le]
    nlinarith [Real.exp_pos (-(C₁ * 2 ^ ((d : ℝ) / 2)))]
  have hkey := log_lower_of_increment_explicit δ C₁ 0 ((d : ℝ) / 2) hδ hC₁ hd2
    (fun n => ∫ ζ, odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) humono ⌈1 / δ⌉₊
    hN1 (fun n _ => le_trans (mul_le_mul_of_nonneg_right hδle (Real.exp_nonneg _)) (hincr n))
    t ht
  rw [← hexp]
  exact hkey

end Sandpile
