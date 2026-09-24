/-
A countable measurable approximation to the infinite-scale crossing event
of `sandpile.tex:2431-2482`. Integer levels and rational scales give a
decreasing sequence of chain events. The crossing bracket gives its positive
probability, and continuity identifies its intersection with `ScaleCrossings`.
The final implication requires tail measurability explicitly.
-/
import Sandpile.Support.LimStepOne
open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum Sandpile.Support Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal
noncomputable def Sandpile.Support.scaleChainEvent {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (W : (Space d → ℝ) → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2)
    (n : ℕ) : Set Ω :=
  ⋃ s : ℚ, ⋃ _ : 0 < s ∧ (s : ℝ) < ((n : ℝ) + 1)⁻¹,
    crossApprox (ballField d W (s : ℝ)) a b i (((n : ℝ) + 1) * crossScale d (s : ℝ))

theorem Sandpile.Support.scaleCrossings_of_bounded_perturbation {Ω : Type*} {d : ℕ}
    {W W' : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {ω : Ω}
    {C : ℝ} (hC : 0 ≤ C)
    (hshift : ∀ s : ℚ, 0 < s → (s : ℝ) < 1 → ∀ u ∈ rectSet a b,
      |ballField d W (s : ℝ) u ω - ballField d W' (s : ℝ) u ω| ≤ C * crossScale d (s : ℝ))
    (h : ScaleCrossings d W a b i ω) : ScaleCrossings d W' a b i ω := by
  intro L hL m
  obtain ⟨s, hs, hsm, hcr⟩ := h (L + C) (by linarith) m
  have hcut : ((m : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
  refine ⟨s, hs, hsm, crosses_of_mem_on (fun u hu hmem => ?_) hcr⟩
  have he := (abs_le.mp (hshift s hs (hsm.trans_le hcut) u hu)).2
  change (L + C) * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω at hmem
  change L * crossScale d (s : ℝ) ≤ ballField d W' (s : ℝ) u ω
  nlinarith

theorem Sandpile.Support.scaleCrossings_iff_nat {Ω : Type*} {d : ℕ}
    {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {ω : Ω} :
    ScaleCrossings d W a b i ω ↔
      ∀ n m : ℕ, ∃ s : ℚ, 0 < s ∧ (s : ℝ) < ((m : ℝ) + 1)⁻¹ ∧
        Crosses a b i {u | ((n : ℝ) + 1) * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω} := by
  constructor
  · intro h n m
    exact h ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]) m
  · intro h L _ m
    obtain ⟨n, hn⟩ := exists_nat_gt L
    obtain ⟨s, hs, hsm, hcr⟩ := h n m
    refine ⟨s, hs, hsm, crosses_level_mono ?_ hcr⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (crossScale_pos (by exact_mod_cast hs)).le

theorem Sandpile.Support.measurableSet_scaleChainEvent {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {W : (Space d → ℝ) → Ω → ℝ}
    (hm : ∀ s : ℚ, 0 < s → ∀ u, Measurable (ballField d W (s : ℝ) u))
    (a b : Fin 2 → ℝ) (i : Fin 2) (n : ℕ) :
    MeasurableSet (scaleChainEvent d W a b i n) := by
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun hs =>
    measurableSet_crossApprox (hm s hs.1) a b i _

theorem Sandpile.Support.scaleChainEvent_antitone {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) :
    Antitone (scaleChainEvent d W a b i) := by
  intro n m hnm ω hω
  obtain ⟨s, hω⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hs, hcr⟩ := Set.mem_iUnion.mp hω
  have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  have hinv : ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
    inv_anti₀ (by positivity) hnm'
  refine Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨hs.1, hs.2.trans_le hinv⟩, ?_⟩⟩
  exact crossApprox_mono_level _ a b i
    (mul_le_mul_of_nonneg_right hnm' (crossScale_pos (by exact_mod_cast hs.1)).le) hcr

theorem Sandpile.Support.scaleChainEvent_lower {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2}
    (hab : ∀ j, a j < b j)
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      ∀ᵐ ω ∂P, Continuous fun u => ballField d W (s : ℝ) u ω)
    {p : ℝ} (hlow : ∀ L : ℝ, 1 ≤ L → ∃ s₀ : ℝ, 0 < s₀ ∧
      ∀ s : ℚ, 0 < (s : ℝ) → (s : ℝ) < s₀ →
        ENNReal.ofReal p ≤ P {ω | Crosses a b i {u | L * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω}})
    (n : ℕ) : ENNReal.ofReal p ≤ P (scaleChainEvent d W a b i n) := by
  obtain ⟨s₀, hs₀, hb⟩ := hlow ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  obtain ⟨s, hs0, hslt⟩ := exists_rat_btwn (show (0 : ℝ) < min s₀ ((n : ℝ) + 1)⁻¹ by positivity)
  have hs : (0 : ℚ) < s := by exact_mod_cast hs0
  have hss₀ : (s : ℝ) < s₀ := hslt.trans_le (min_le_left _ _)
  have hsn : (s : ℝ) < ((n : ℝ) + 1)⁻¹ := hslt.trans_le (min_le_right _ _)
  have hcut : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc' := measure_crossing_le_crossApprox (i := i) P (hab 0) (hab 1)
      (crossScale_pos (d := d) hs0) (hc s hs (hsn.trans_le hcut).le)
      (l := ((n : ℝ) + 2) * crossScale d (s : ℝ))
  have heq : ((n : ℝ) + 2) * crossScale d (s : ℝ) - crossScale d (s : ℝ)
      = ((n : ℝ) + 1) * crossScale d (s : ℝ) := by ring
  rw [heq] at hc'
  refine (hb s hs0 hss₀).trans (hc'.trans (measure_mono ?_))
  intro ω hω
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨hs, hsn⟩, hω⟩⟩

theorem Sandpile.Support.le_measure_iInter_of_antitone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (hm : ∀ n, MeasurableSet (A n)) (ha : Antitone A)
    {p : ℝ≥0∞} (hp : ∀ n, p ≤ P (A n)) : p ≤ P (⋂ n, A n) := by
  rw [ha.measure_iInter (fun n => (hm n).nullMeasurableSet) ⟨0, measure_ne_top P _⟩]
  exact le_iInf hp

theorem Sandpile.Support.scaleCrossings_of_mem_scaleChainIntersection {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {ω : Ω}
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      Continuous fun u => ballField d W (s : ℝ) u ω)
    (h : ω ∈ ⋂ n, scaleChainEvent d W a b i n) : ScaleCrossings d W a b i ω := by
  intro L _ m
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt L
  let n := max n₀ m
  obtain ⟨s, hω⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp h n)
  obtain ⟨hs, hcr⟩ := Set.mem_iUnion.mp hω
  have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right (le_max_right n₀ m) 1
  have hnL : L ≤ (n : ℝ) + 1 := by
    have : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left n₀ m
    linarith
  have hcut : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  refine ⟨s, hs.1, hs.2.trans_le (inv_anti₀ (by positivity) hmn), ?_⟩
  exact crosses_level_mono (mul_le_mul_of_nonneg_right hnL
    (crossScale_pos (by exact_mod_cast hs.1)).le)
    (crossApprox_inter_subset_crossing ⟨hcr, hc s hs.1 (hs.2.trans_le hcut).le⟩)

theorem Sandpile.Support.mem_scaleChainIntersection_of_scaleCrossings {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2} {ω : Ω}
    (hab : ∀ j, a j < b j)
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      Continuous fun u => ballField d W (s : ℝ) u ω)
    (h : ScaleCrossings d W a b i ω) : ω ∈ ⋂ n, scaleChainEvent d W a b i n := by
  refine Set.mem_iInter.mpr fun n => ?_
  obtain ⟨s, hs, hsn, hcr⟩ := h ((n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n]) n
  have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hcut : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hc' := crossing_inter_subset_crossApprox (hab 0) (hab 1)
    (crossScale_pos (d := d) hs0) ⟨hcr, hc s hs (hsn.trans_le hcut).le⟩
  have heq : ((n : ℝ) + 2) * crossScale d (s : ℝ) - crossScale d (s : ℝ)
      = ((n : ℝ) + 1) * crossScale d (s : ℝ) := by ring
  rw [heq] at hc'
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨hs, hsn⟩, hc'⟩⟩

theorem Sandpile.Support.scaleChainIntersection_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2}
    (hab : ∀ j, a j < b j)
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      ∀ᵐ ω ∂P, Continuous fun u => ballField d W (s : ℝ) u ω) :
    (⋂ n, scaleChainEvent d W a b i n) =ᵐ[P] {ω | ScaleCrossings d W a b i ω} := by
  have hall : ∀ᵐ ω ∂P, ∀ s : {s : ℚ // 0 < s ∧ (s : ℝ) ≤ 1},
      Continuous fun u => ballField d W (s : ℚ) u ω :=
    ae_all_iff.mpr fun s => hc s s.2.1 s.2.2
  filter_upwards [hall] with ω hω
  exact propext
    ⟨scaleCrossings_of_mem_scaleChainIntersection
        (fun s hs hs1 => hω ⟨s, hs, hs1⟩),
      mem_scaleChainIntersection_of_scaleCrossings hab
        (fun s hs hs1 => hω ⟨s, hs, hs1⟩)⟩

theorem Sandpile.Support.scaleChainIntersection_positive {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2}
    (hab : ∀ j, a j < b j)
    (hm : ∀ s : ℚ, 0 < s → ∀ u, Measurable (ballField d W (s : ℝ) u))
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      ∀ᵐ ω ∂P, Continuous fun u => ballField d W (s : ℝ) u ω)
    (hlow : ScaleCrossingLowerAt d P W a b i) :
    0 < P (⋂ n, scaleChainEvent d W a b i n) := by
  obtain ⟨p, hp, hlow⟩ := hlow
  exact (ENNReal.ofReal_pos.mpr hp).trans_le
    (le_measure_iInter_of_antitone P _ (measurableSet_scaleChainEvent hm a b i)
      (scaleChainEvent_antitone d W a b i) (scaleChainEvent_lower hab hc hlow))

theorem Sandpile.Support.ae_scaleCrossings_of_tail {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {W : (Space d → ℝ) → Ω → ℝ} {a b : Fin 2 → ℝ} {i : Fin 2}
    (hc : ∀ s : ℚ, 0 < s → (s : ℝ) ≤ 1 →
      ∀ᵐ ω ∂P, Continuous fun u => ballField d W (s : ℝ) u ω)
    (f : ℕ → MeasurableSpace Ω) (hle : ∀ n, f n ≤ mΩ) (hind : iIndep f P)
    (htail : MeasurableSet[Filter.limsup f Filter.atTop] (⋂ n, scaleChainEvent d W a b i n))
    (hpos : 0 < P (⋂ n, scaleChainEvent d W a b i n)) :
    ∀ᵐ ω ∂P, ScaleCrossings d W a b i ω := by
  have hm : MeasurableSet (⋂ n, scaleChainEvent d W a b i n) :=
    (limsup_le_iSup.trans (iSup_le hle)) _ htail
  have h1 : P (⋂ n, scaleChainEvent d W a b i n) = 1 := by
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop hle hind htail with h0 | h1
    · exact False.elim (hpos.ne' h0)
    · exact h1
  have hall : ∀ᵐ ω ∂P, ω ∈ ⋂ n, scaleChainEvent d W a b i n :=
    ae_iff.mpr ((prob_compl_eq_zero_iff hm).mpr h1)
  have hc' : ∀ᵐ ω ∂P, ∀ s : {s : ℚ // 0 < s ∧ (s : ℝ) ≤ 1},
      Continuous fun u => ballField d W (s : ℚ) u ω :=
    ae_all_iff.mpr fun s => hc s s.2.1 s.2.2
  filter_upwards [hall, hc'] with ω hω hcont
  exact scaleCrossings_of_mem_scaleChainIntersection
    (fun s hs hs1 => hcont ⟨s, hs, hs1⟩) hω
