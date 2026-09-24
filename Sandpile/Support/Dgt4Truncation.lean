/-
The truncation that replaces the conditioning of Step 1 of case (b)
(`sandpile.tex:5361-5371`).

On `\{A_n=\varnothing\}` every weighted contribution `-G(0,z)\zeta(z)/G(0,0)` is at most the
level `\eta_n\E Pw_n(0)`, and the paper reads the deviation estimate off the conditional law
of the scenery there.  That conditional law is a product of conditioned marginals, and the
conditioned field is exactly the field truncated from below at the level: raising a scenery
value that falls below `-t/c_z` to that level changes nothing on the event, while off the
event it only raises the field.  Since `Pw_n(0)` is nondecreasing in the scenery
(`sandpile.tex:5371`) and reads only the box away from the origin, the conditional statement
becomes an UNCONDITIONED deviation estimate for the truncated field, whose coordinates are
independent and whose contributions lie in a bounded interval.  That is the form in which
Freedman's inequality is to be applied.
-/
import Sandpile.Support.Dgt4LargeSites

open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The localized odometer is nondecreasing in the scenery. -/
theorem localizedOdometer_mono (hd : 1 ≤ d) (D : Set (Sandpile.Site d)) :
    ∀ (n : ℕ) (x : Sandpile.Site d) {ζ η : Sandpile.Site d → ℝ}, (∀ z, ζ z ≤ η z) →
      Sandpile.localizedOdometer D ζ n x ≤ Sandpile.localizedOdometer D η n x := by
  intro n
  induction n with
  | zero =>
      intro x ζ η _
      rw [Sandpile.localizedOdometer_zero hd, Sandpile.localizedOdometer_zero hd]
  | succ m ih =>
      intro x ζ η h
      by_cases hx : x ∈ D
      · rw [Sandpile.localizedOdometer_succ' hd D ζ m x hx,
          Sandpile.localizedOdometer_succ' hd D η m x hx]
        exact max_le_max_left 0
          (add_le_add (h x) (Sandpile.avg_mono_le (fun y => ih y h) x))
      · rw [Sandpile.localizedOdometer_of_notMem D ζ (m + 1) hx,
          Sandpile.localizedOdometer_of_notMem D η (m + 1) hx]

/-- `Pw_n(0)` is nondecreasing in the scenery (`sandpile.tex:5366`). -/
theorem avg_originOdometer_mono (hd : 1 ≤ d) (n : ℕ) {ζ η : Sandpile.Site d → ℝ}
    (h : ∀ z, ζ z ≤ η z) :
    Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤
      Sandpile.avg (Sandpile.originOdometer η n) 0 :=
  Sandpile.avg_mono_le (fun y => localizedOdometer_mono hd _ n y h) 0

/-- The scenery truncated from below at the level of `A_n`: the value at `z` is raised to
`-t/c_z` when it falls below, so that the weighted contribution `-c_z\zeta(z)` never exceeds
`t`.  A site of weight zero is left alone, its contribution being zero. -/
noncomputable def truncScenery (c : Sandpile.Site d → ℝ) (t : ℝ)
    (ζ : Sandpile.Site d → ℝ) : Sandpile.Site d → ℝ :=
  fun z => if c z = 0 then ζ z else max (ζ z) (-(t / c z))

/-- Truncating from below only raises the scenery. -/
theorem le_truncScenery (c : Sandpile.Site d → ℝ) (t : ℝ) (ζ : Sandpile.Site d → ℝ)
    (z : Sandpile.Site d) : ζ z ≤ truncScenery c t ζ z := by
  rw [truncScenery]
  by_cases h : c z = 0
  · rw [if_pos h]
  · rw [if_neg h]
    exact le_max_left _ _

/-- Hence the neighbour average of the truncated field dominates that of the field, and in
particular its mean dominates `\E Pw_n(0)`, which is the first display of
`sandpile.tex:5364-5366`. -/
theorem avg_originOdometer_le_trunc (hd : 1 ≤ d) (n : ℕ) (c : Sandpile.Site d → ℝ) (t : ℝ)
    (ζ : Sandpile.Site d → ℝ) :
    Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤
      Sandpile.avg (Sandpile.originOdometer (truncScenery c t ζ) n) 0 :=
  avg_originOdometer_mono hd n (le_truncScenery c t ζ)

/-- On `\{A_n=\varnothing\}` the truncation changes nothing that `Pw_n(0)` sees: the two
fields agree on the box away from the origin, and `Pw_n(0)` does not read the origin. -/
theorem avg_originOdometer_trunc_eq (hd : 1 ≤ d) (n : ℕ) (c : Sandpile.Site d → ℝ)
    (hc : ∀ z, 0 ≤ c z) (t : ℝ) (ζ : Sandpile.Site d → ℝ)
    (h : ∀ z ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0,
      ¬ (t < -(c z * ζ z))) :
    Sandpile.avg (Sandpile.originOdometer (truncScenery c t ζ) n) 0
      = Sandpile.avg (Sandpile.originOdometer ζ n) 0 := by
  have hupd : ∀ ξ : Sandpile.Site d → ℝ,
      Sandpile.avg (Sandpile.originOdometer (Function.update ξ 0 0) n) 0
        = Sandpile.avg (Sandpile.originOdometer ξ n) 0 := by
    intro ξ
    rw [Sandpile.originOdometer_update hd ξ 0 n]
  rw [← hupd (truncScenery c t ζ), ← hupd ζ]
  refine Sandpile.avg_originOdometer_congr_box hd n _ _ ?_
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp
  · rw [Function.update_of_ne hz0, Function.update_of_ne hz0]
    have hmem : z ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0 :=
      Finset.mem_erase.mpr ⟨hz0, hz⟩
    have hle : -(c z * ζ z) ≤ t := not_lt.mp (h z hmem)
    rw [truncScenery]
    by_cases hc0 : c z = 0
    · rw [if_pos hc0]
    · rw [if_neg hc0]
      have hcpos : 0 < c z := lt_of_le_of_ne (hc z) (Ne.symm hc0)
      have : -(t / c z) ≤ ζ z := by
        rw [← neg_div, div_le_iff₀ hcpos]
        nlinarith [hle, mul_comm (ζ z) (c z)]
      exact max_eq_left this

/-- The comparison in the form Step 1 uses. -/
theorem measure_small_inter_empty_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (n : ℕ) (c : Sandpile.Site d → ℝ) (hc : ∀ z, 0 ≤ c z) (t r : ℝ) :
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
          {ζ | ((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0).filter
            (fun z => t < -(c z * ζ z)) = ∅})
      ≤ (LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer (truncScenery c t ζ) n) 0 ≤ r} := by
  refine measure_mono fun ζ hζ => ?_
  obtain ⟨h1, h2⟩ := hζ
  have hall : ∀ z ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0,
      ¬ (t < -(c z * ζ z)) := by
    intro z hz hlt
    have : z ∈ ((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0).filter
        (fun w => t < -(c w * ζ w)) := Finset.mem_filter.mpr ⟨hz, hlt⟩
    rw [h2] at this
    exact absurd this (Finset.notMem_empty z)
  show Sandpile.avg (Sandpile.originOdometer (truncScenery c t ζ) n) 0 ≤ r
  rw [avg_originOdometer_trunc_eq hd n c hc t ζ hall]
  exact h1

/-- The conditioning of `sandpile.tex:5356-5360` on `\{A_n=\varnothing\}` replaced by the
truncation: on that event the neighbour average is the one of the truncated field, whose
coordinates are independent and bounded below by the level. -/
theorem measure_small_inter_largeSites_empty_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 5 ≤ d) (n : ℕ) (K r : ℝ) :
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
          {ζ | largeSites d ν K n ζ = ∅})
      ≤ (LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer
          (truncScenery (fun z => Sandpile.green d 0 z / Sandpile.green d 0 0)
            (meanOriginAverage d ν n /
              (K * Real.log (meanOriginAverage d ν n))) ζ) n) 0 ≤ r} := by
  have hcnn : ∀ z : Sandpile.Site d, 0 ≤ Sandpile.green d 0 z / Sandpile.green d 0 0 := by
    intro z
    rw [greenRatio_eq_hitProb (by omega) z]
    exact LatticeProb.srwHitProb_nonneg z
  exact measure_small_inter_empty_le ν (by omega) n
    (fun z => Sandpile.green d 0 z / Sandpile.green d 0 0) hcnn _ r


/-- The neighbour average at the origin of a localized odometer reads only the box. -/
theorem avg_localizedOdometer_congr_box (hd : 1 ≤ d) (D : Set (Sandpile.Site d)) (n : ℕ)
    (ζ η : Sandpile.Site d → ℝ)
    (he : ∀ z ∈ Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1), ζ z = η z) :
    Sandpile.avg (Sandpile.localizedOdometer D ζ n) 0
      = Sandpile.avg (Sandpile.localizedOdometer D η n) 0 := by
  have hnbr : ∀ x : Sandpile.Site d, Sandpile.boxDist 0 x ≤ 1 →
      Sandpile.localizedOdometer D ζ n x = Sandpile.localizedOdometer D η n x := by
    intro x hx
    refine Sandpile.localizedOdometer_congr_box hd _ n x ζ η fun z hz => he z ?_
    have hd0 := Sandpile.boxDist_trans (0 : Sandpile.Site d) x z
    have hn := Sandpile.mem_boxFinset_iff.mp hz
    exact Sandpile.mem_boxFinset (by omega)
  unfold Sandpile.avg LatticeProb.walkOp LatticeProb.nbrSum
  congr 1
  exact Finset.sum_congr rfl fun i _ => congrArg₂ (· + ·)
    (hnbr _ (Sandpile.boxDist_add_unit 0 i)) (hnbr _ (Sandpile.boxDist_sub_unit 0 i))

/-- Killing the walk on a larger set only lowers the localized odometer. -/
theorem localizedOdometer_mono_set (hd : 1 ≤ d) {D D' : Set (Sandpile.Site d)} (hDD : D ⊆ D')
    (ζ : Sandpile.Site d → ℝ) : ∀ (n : ℕ) (x : Sandpile.Site d),
      Sandpile.localizedOdometer D ζ n x ≤ Sandpile.localizedOdometer D' ζ n x := by
  intro n
  induction n with
  | zero =>
      intro x
      rw [Sandpile.localizedOdometer_zero hd, Sandpile.localizedOdometer_zero hd]
  | succ m ih =>
      intro x
      by_cases hx : x ∈ D
      · rw [Sandpile.localizedOdometer_succ' hd D ζ m x hx,
          Sandpile.localizedOdometer_succ' hd D' ζ m x (hDD hx)]
        exact max_le_max_left 0 (add_le_add le_rfl (Sandpile.avg_mono_le ih x))
      · rw [Sandpile.localizedOdometer_of_notMem D ζ (m + 1) hx]
        exact Sandpile.localizedOdometer_nonneg hd D' ζ (m + 1) x

/-- The localized odometer does not read the scenery at a killed site. -/
theorem localizedOdometer_update_of_notMem (hd : 1 ≤ d) (D : Set (Sandpile.Site d))
    (ζ : Sandpile.Site d → ℝ) {z : Sandpile.Site d} (hz : z ∉ D) (v : ℝ) :
    ∀ n : ℕ, Sandpile.localizedOdometer D (Function.update ζ z v) n
      = Sandpile.localizedOdometer D ζ n := by
  intro n
  induction n with
  | zero =>
      funext x
      rw [Sandpile.localizedOdometer_zero hd, Sandpile.localizedOdometer_zero hd]
  | succ m ih =>
      funext x
      by_cases hx : x ∈ D
      · rw [Sandpile.localizedOdometer_succ' hd D _ m x hx,
          Sandpile.localizedOdometer_succ' hd D ζ m x hx, ih]
        have hxz : x ≠ z := fun h => hz (h ▸ hx)
        rw [Function.update_of_ne hxz]
      · rw [Sandpile.localizedOdometer_of_notMem D _ (m + 1) hx,
          Sandpile.localizedOdometer_of_notMem D ζ (m + 1) hx]

/-- `Pu_n^{\Z^d\setminus\{0,z\}}`, the odometer with the walk killed at the origin and at
`z` (`sandpile.tex:5361-5362`). -/
noncomputable abbrev pairOdometer (z : Sandpile.Site d) (ζ : Sandpile.Site d → ℝ) (n : ℕ) :
    Sandpile.Site d → ℝ :=
  Sandpile.localizedOdometer {x : Sandpile.Site d | x ≠ 0 ∧ x ≠ z} ζ n

/-- `Pw_n(0)\geq Pu_n^{\Z^d\setminus\{0,z\}}(0)`, the monotonicity of `sandpile.tex:5361`. -/
theorem avg_pairOdometer_le (hd : 1 ≤ d) (z : Sandpile.Site d) (ζ : Sandpile.Site d → ℝ)
    (n : ℕ) :
    Sandpile.avg (pairOdometer z ζ n) 0 ≤ Sandpile.avg (Sandpile.originOdometer ζ n) 0 :=
  Sandpile.avg_mono_le
    (fun y => localizedOdometer_mono_set hd (fun _ hw => hw.1) ζ n y) 0

/-- On `\{A_n=\{z\}\}` the truncation off `z` changes nothing that the odometer killed at
`\{0,z\}` sees. -/
theorem avg_pairOdometer_trunc_eq (hd : 1 ≤ d) (n : ℕ) (c : Sandpile.Site d → ℝ)
    (hc : ∀ z, 0 ≤ c z) (t : ℝ) (z₀ : Sandpile.Site d) (ζ : Sandpile.Site d → ℝ)
    (h : ∀ w ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0, w ≠ z₀ →
      ¬ (t < -(c w * ζ w))) :
    Sandpile.avg (pairOdometer z₀ (truncScenery c t ζ) n) 0
      = Sandpile.avg (pairOdometer z₀ ζ n) 0 := by
  set D : Set (Sandpile.Site d) := {x : Sandpile.Site d | x ≠ 0 ∧ x ≠ z₀} with hD
  have h0 : (0 : Sandpile.Site d) ∉ D := by simp [hD]
  have hz₀ : z₀ ∉ D := by simp [hD]
  have hupd : ∀ ξ : Sandpile.Site d → ℝ,
      Sandpile.avg (Sandpile.localizedOdometer D
          (Function.update (Function.update ξ 0 0) z₀ 0) n) 0
        = Sandpile.avg (Sandpile.localizedOdometer D ξ n) 0 := by
    intro ξ
    rw [localizedOdometer_update_of_notMem hd D _ hz₀ 0 n,
      localizedOdometer_update_of_notMem hd D ξ h0 0 n]
  rw [← hupd (truncScenery c t ζ), ← hupd ζ]
  refine avg_localizedOdometer_congr_box hd D n _ _ ?_
  intro w hw
  by_cases hwz : w = z₀
  · subst hwz
    simp
  · rw [Function.update_of_ne hwz, Function.update_of_ne hwz]
    by_cases hw0 : w = 0
    · subst hw0
      simp
    · rw [Function.update_of_ne hw0, Function.update_of_ne hw0]
      have hmem : w ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0 :=
        Finset.mem_erase.mpr ⟨hw0, hw⟩
      have hle : -(c w * ζ w) ≤ t := not_lt.mp (h w hmem hwz)
      rw [truncScenery]
      by_cases hc0 : c w = 0
      · rw [if_pos hc0]
      · rw [if_neg hc0]
        have hcpos : 0 < c w := lt_of_le_of_ne (hc w) (Ne.symm hc0)
        have hge : -(t / c w) ≤ ζ w := by
          rw [← neg_div, div_le_iff₀ hcpos]
          nlinarith [hle, mul_comm (ζ w) (c w)]
        exact max_eq_left hge


/-- The conditioning of `sandpile.tex:5361-5363` on `\{A_n=\{z\}\}`, in the same
unconditioned form: the odometer killed at `\{0,z\}` is below the neighbour average, does not
read the scenery at either killed site, and on the event agrees with its value at the
truncated field. -/
theorem measure_small_inter_largeSites_singleton_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 5 ≤ d) (n : ℕ) (K r : ℝ) (z₀ : Sandpile.Site d) :
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
          {ζ | largeSites d ν K n ζ = {z₀}})
      ≤ (LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (pairOdometer z₀
          (truncScenery (fun z => Sandpile.green d 0 z / Sandpile.green d 0 0)
            (meanOriginAverage d ν n /
              (K * Real.log (meanOriginAverage d ν n))) ζ) n) 0 ≤ r} := by
  have hcnn : ∀ z : Sandpile.Site d, 0 ≤ Sandpile.green d 0 z / Sandpile.green d 0 0 := by
    intro z
    rw [greenRatio_eq_hitProb (by omega) z]
    exact LatticeProb.srwHitProb_nonneg z
  refine measure_mono fun ζ hζ => ?_
  obtain ⟨h1, h2⟩ := hζ
  have hall : ∀ w ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0, w ≠ z₀ →
      ¬ (meanOriginAverage d ν n / (K * Real.log (meanOriginAverage d ν n)) <
        -((Sandpile.green d 0 w / Sandpile.green d 0 0) * ζ w)) := by
    intro w hw hwz hlt
    have hmem : w ∈ largeSites d ν K n ζ := Finset.mem_filter.mpr ⟨hw, hlt⟩
    rw [h2, Finset.mem_singleton] at hmem
    exact hwz hmem
  show Sandpile.avg (pairOdometer z₀ (truncScenery _ _ ζ) n) 0 ≤ r
  rw [avg_pairOdometer_trunc_eq (by omega) n _ hcnn _ z₀ ζ hall]
  exact le_trans (avg_pairOdometer_le (by omega) z₀ ζ n) h1


/-- The neighbour average at the origin of a localized odometer is measurable in the scenery. -/
theorem measurable_avg_localizedOdometer (hd : 1 ≤ d) (D : Set (Sandpile.Site d)) (n : ℕ) :
    Measurable (fun ζ : Sandpile.Site d → ℝ =>
      Sandpile.avg (Sandpile.localizedOdometer D ζ n) 0) := by
  unfold Sandpile.avg
  exact (Finset.measurable_sum _ fun i _ =>
    (Sandpile.measurable_localizedOdometer hd _ n _).add
      (Sandpile.measurable_localizedOdometer hd _ n _)).div_const _

/-- The truncation is measurable. -/
theorem measurable_truncScenery (c : Sandpile.Site d → ℝ) (t : ℝ) :
    Measurable (fun ζ : Sandpile.Site d → ℝ => truncScenery c t ζ) := by
  refine measurable_pi_lambda _ fun z => ?_
  by_cases h : c z = 0
  · simpa only [truncScenery, if_pos h] using measurable_pi_apply z
  · simpa only [truncScenery, if_neg h] using (measurable_pi_apply z).max measurable_const

/-- Truncation commutes with an update of one coordinate. -/
theorem truncScenery_update (c : Sandpile.Site d → ℝ) (t : ℝ) (ζ : Sandpile.Site d → ℝ)
    (z₀ : Sandpile.Site d) (v : ℝ) :
    truncScenery c t (Function.update ζ z₀ v)
      = Function.update (truncScenery c t ζ) z₀
        (if c z₀ = 0 then v else max v (-(t / c z₀))) := by
  funext w
  by_cases hw : w = z₀
  · subst hw
    simp [truncScenery]
  · simp [truncScenery, Function.update_of_ne hw]

/-- The site weights of `A_n`: `G(0,z)/G(0,0)`, the probability that the walk from `z` hits
the origin. -/
noncomputable def greenRatioWeight (d : ℕ) : Sandpile.Site d → ℝ :=
  fun z => Sandpile.green d 0 z / Sandpile.green d 0 0

theorem greenRatioWeight_nonneg (hd : 5 ≤ d) (z : Sandpile.Site d) :
    0 ≤ greenRatioWeight d z := by
  rw [greenRatioWeight, greenRatio_eq_hitProb (by omega) z]
  exact LatticeProb.srwHitProb_nonneg z

/-- The level `\eta_n\E Pw_n(0)` of `sandpile.tex:5350`. -/
noncomputable def originLevel (d : ℕ) (ν : Measure ℝ) (K : ℝ) (n : ℕ) : ℝ :=
  meanOriginAverage d ν n / (K * Real.log (meanOriginAverage d ν n))

/-- `Pu_n^{\Z^d\setminus\{0,z\}}(0)` at the truncated field. -/
noncomputable def truncPairAverage (d : ℕ) (ν : Measure ℝ) (K : ℝ) (n : ℕ)
    (z₀ : Sandpile.Site d) (ζ : Sandpile.Site d → ℝ) : ℝ :=
  Sandpile.avg (pairOdometer z₀
    (truncScenery (greenRatioWeight d) (originLevel d ν K n) ζ) n) 0

theorem measurable_truncPairAverage (hd : 1 ≤ d) (ν : Measure ℝ) (K : ℝ) (n : ℕ)
    (z₀ : Sandpile.Site d) : Measurable (truncPairAverage d ν K n z₀) :=
  (measurable_avg_localizedOdometer hd _ n).comp
    (measurable_truncScenery (greenRatioWeight d) (originLevel d ν K n))

/-- It does not read the scenery at the killed site `z`, which is what makes it independent
of the event `\{z\in A_n\}`. -/
theorem truncPairAverage_update (hd : 1 ≤ d) (ν : Measure ℝ) (K : ℝ) (n : ℕ)
    (z₀ : Sandpile.Site d) (ζ : Sandpile.Site d → ℝ) (v : ℝ) :
    truncPairAverage d ν K n z₀ (Function.update ζ z₀ v) = truncPairAverage d ν K n z₀ ζ := by
  have hz₀ : z₀ ∉ {x : Sandpile.Site d | x ≠ 0 ∧ x ≠ z₀} := by simp
  rw [truncPairAverage, truncPairAverage, truncScenery_update]
  exact congrArg (fun f => Sandpile.avg f 0)
    (localizedOdometer_update_of_notMem hd _ _ hz₀ _ n)

/-- The singleton case of `sandpile.tex:5361-5363` as a product: the deviation of the odometer
killed at `\{0,z\}` at the truncated field is independent of `\{z\in A_n\}`. -/
theorem measure_small_inter_singleton_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 5 ≤ d) (n : ℕ) (K r : ℝ) (z₀ : Sandpile.Site d) :
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
          {ζ | largeSites d ν K n ζ = {z₀}})
      ≤ ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} *
        (LatticeProb.iidLaw d ν) {ζ | truncPairAverage d ν K n z₀ ζ ≤ r} := by
  have hd1 : 1 ≤ d := by omega
  have hcnn : ∀ z : Sandpile.Site d, 0 ≤ greenRatioWeight d z := greenRatioWeight_nonneg hd
  have hA : MeasurableSet {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} := by
    have hm : Measurable fun y : ℝ => -(greenRatioWeight d z₀ * y) := by fun_prop
    exact measurableSet_lt measurable_const hm
  have hsub : ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
        {ζ | largeSites d ν K n ζ = {z₀}})
      ⊆ {ζ : Sandpile.Site d → ℝ |
          ζ z₀ ∈ {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} ∧
          truncPairAverage d ν K n z₀ ζ ∈ Set.Iic r} := by
    rintro ζ ⟨h1, h2⟩
    have hmemz : z₀ ∈ largeSites d ν K n ζ := by rw [h2]; exact Finset.mem_singleton_self z₀
    have hlt := (Finset.mem_filter.mp hmemz).2
    refine ⟨hlt, ?_⟩
    have hall : ∀ w ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0, w ≠ z₀ →
        ¬ (originLevel d ν K n < -(greenRatioWeight d w * ζ w)) := by
      intro w hw hwz hltw
      have hmem : w ∈ largeSites d ν K n ζ := Finset.mem_filter.mpr ⟨hw, hltw⟩
      rw [h2, Finset.mem_singleton] at hmem
      exact hwz hmem
    show truncPairAverage d ν K n z₀ ζ ≤ r
    rw [truncPairAverage,
      avg_pairOdometer_trunc_eq hd1 n (greenRatioWeight d) hcnn (originLevel d ν K n) z₀ ζ hall]
    exact le_trans (avg_pairOdometer_le hd1 z₀ ζ n) h1
  refine le_trans (measure_mono hsub) (le_of_eq ?_)
  exact measure_inter_site_indep ν z₀ (measurable_truncPairAverage hd1 ν K n z₀)
    (truncPairAverage_update hd1 ν K n z₀) hA measurableSet_Iic

/-- `Pw_n(0)` at the truncated field. -/
noncomputable def truncOriginAverage (d : ℕ) (ν : Measure ℝ) (K : ℝ) (n : ℕ)
    (ζ : Sandpile.Site d → ℝ) : ℝ :=
  Sandpile.avg (Sandpile.originOdometer
    (truncScenery (greenRatioWeight d) (originLevel d ν K n) ζ) n) 0

/-- The empty case of `sandpile.tex:5356-5360`. -/
theorem measure_small_inter_empty_le' (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 5 ≤ d) (n : ℕ) (K r : ℝ) :
    (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ r} ∩
          {ζ | largeSites d ν K n ζ = ∅})
      ≤ (LatticeProb.iidLaw d ν) {ζ | truncOriginAverage d ν K n ζ ≤ r} :=
  measure_small_inter_empty_le ν (by omega) n (greenRatioWeight d)
    (greenRatioWeight_nonneg hd) (originLevel d ν K n) r


/-- The unconditioned deviation estimate that Step 1 needs. -/
def TruncatedOriginDeviation (d : ℕ) (ν : Measure ℝ) (K β : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (LatticeProb.iidLaw d ν)
        {ζ | truncOriginAverage d ν K n ζ ≤ meanOriginAverage d ν n / 6}
      ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) ∧
    ∀ z₀ : Sandpile.Site d, (LatticeProb.iidLaw d ν)
        {ζ | truncPairAverage d ν K n z₀ ζ ≤ meanOriginAverage d ν n / 6}
      ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β))

theorem smallOriginNeighborAverage_of_truncated
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K β : ℝ} (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K) (hβ : α < β)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d => greenRatioWeight d z ^ p)
    (htr : TruncatedOriginDeviation d ν K β) :
    SmallOriginNeighborAverage d ν := by
  have hd1 : 1 ≤ d := by omega
  have hainf : Tendsto (meanOriginAverage d ν) atTop atTop :=
    tendsto_meanAvg_originOdometer_atTop hGH d hd ν hatom hmean hvar hvar'
  have hcnn : ∀ z : Sandpile.Site d, 0 ≤ greenRatioWeight d z := greenRatioWeight_nonneg hd
  set M : ℝ := ∫ y, |y| ^ p ∂ν with hMdef
  have hMnn : 0 ≤ M := integral_nonneg fun y => Real.rpow_nonneg (abs_nonneg y) p
  set B : ℝ := ∑' z : Sandpile.Site d, greenRatioWeight d z ^ p with hBdef
  have hBnn : 0 ≤ B := tsum_nonneg fun z => Real.rpow_nonneg (hcnn z) p
  have hlevelpos : ∀ᶠ n : ℕ in atTop, 0 < originLevel d ν K n := by
    filter_upwards [hainf.eventually_ge_atTop (Real.exp 1)] with n hge
    have hx0 : (0 : ℝ) < meanOriginAverage d ν n := lt_of_lt_of_le (Real.exp_pos 1) hge
    have hL : (1 : ℝ) ≤ Real.log (meanOriginAverage d ν n) := by
      have h := Real.log_le_log (Real.exp_pos 1) hge
      rwa [Real.log_exp] at h
    have hL0 : (0 : ℝ) < Real.log (meanOriginAverage d ν n) := lt_of_lt_of_le one_pos hL
    rw [originLevel]
    positivity
  have hmassreal : ∀ᶠ n : ℕ in atTop, M * B / originLevel d ν K n ^ p ≤ 1 := by
    have hz : Tendsto (fun x : ℝ => M * B * K ^ p * (Real.log x ^ p * x ^ (-p)))
        atTop (𝓝 0) := by
      have h0 := tendsto_log_rpow_mul_rpow_neg_atTop (q := p) hp
      simpa using h0.const_mul (M * B * K ^ p)
    have hlt := (hz.comp hainf).eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    filter_upwards [hlt, hainf.eventually_ge_atTop (Real.exp 1)] with n hn hge
    have hx0 : (0 : ℝ) < meanOriginAverage d ν n := lt_of_lt_of_le (Real.exp_pos 1) hge
    have hL : (1 : ℝ) ≤ Real.log (meanOriginAverage d ν n) := by
      have h := Real.log_le_log (Real.exp_pos 1) hge
      rwa [Real.log_exp] at h
    have hL0 : (0 : ℝ) < Real.log (meanOriginAverage d ν n) := lt_of_lt_of_le one_pos hL
    have hKL : (0 : ℝ) < K * Real.log (meanOriginAverage d ν n) := by positivity
    have hxp : (0 : ℝ) < meanOriginAverage d ν n ^ p := Real.rpow_pos_of_pos hx0 p
    have heq : M * B / originLevel d ν K n ^ p
        = M * B * K ^ p * (Real.log (meanOriginAverage d ν n) ^ p *
          meanOriginAverage d ν n ^ (-p)) := by
      rw [originLevel, Real.div_rpow hx0.le hKL.le p, Real.mul_rpow hK.le hL0.le,
        div_div_eq_mul_div, Real.rpow_neg hx0.le]
      field_simp
    rw [heq]
    exact le_of_lt hn
  have hsum1 : ∀ᶠ n : ℕ in atTop,
      ∑ z₀ ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0,
        ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} ≤ 1 := by
    filter_upwards [hlevelpos, hmassreal] with n hlt hmass
    set s : Finset (Sandpile.Site d) :=
      (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0 with hs
    have htp : (0 : ℝ) < originLevel d ν K n ^ p := Real.rpow_pos_of_pos hlt p
    have hterm : ∀ z₀ ∈ s,
        (ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)}).toReal
          ≤ M * greenRatioWeight d z₀ ^ p / originLevel d ν K n ^ p := by
      intro z₀ _
      have h := measure_site_threshold_le ν z₀ (hcnn z₀) hp hmom hlt
      rwa [measure_site_eq ν z₀ (greenRatioWeight d z₀) (originLevel d ν K n)] at h
    have hne : (∑ z₀ ∈ s, ν {y : ℝ | originLevel d ν K n <
        -(greenRatioWeight d z₀ * y)}) ≠ ⊤ :=
      (ENNReal.sum_lt_top.mpr fun z _ => measure_lt_top ν _).ne
    have hle : (∑ z₀ ∈ s, ν {y : ℝ | originLevel d ν K n <
        -(greenRatioWeight d z₀ * y)}).toReal ≤ 1 := by
      rw [ENNReal.toReal_sum (fun z _ => measure_ne_top ν _)]
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      refine le_trans (div_le_div_of_nonneg_right ?_ htp.le) hmass
      refine mul_le_mul_of_nonneg_left ?_ hMnn
      exact hsumc.sum_le_tsum s fun z _ => Real.rpow_nonneg (hcnn z) p
    have h1 : (1 : ℝ≥0∞).toReal = 1 := ENNReal.toReal_one
    rw [← ENNReal.toReal_le_toReal hne ENNReal.one_ne_top, h1]
    exact hle
  refine smallOriginNeighborAverage_of_measure_bound hGH hd ν hatom hmean hvar hvar'
    hp hpα hK hmom hrv hsumc (fun n => 2 * meanOriginAverage d ν n ^ (-β)) ?_ ?_ ?_
  · filter_upwards [hainf.eventually_gt_atTop 0] with n hpos
    have := Real.rpow_nonneg hpos.le (-β)
    linarith
  · have h1 := tendsto_rpow_neg_div_lowerTail ν hβ hrv (meanOriginAverage d ν) hainf
    have h2 := h1.const_mul (2 : ℝ)
    rw [mul_zero] at h2
    refine h2.congr fun n => ?_
    rw [mul_div_assoc]
  · filter_upwards [htr, hsum1, hainf.eventually_gt_atTop 0] with n hn hmass hpos
    have hpow : (0 : ℝ) ≤ meanOriginAverage d ν n ^ (-β) := Real.rpow_nonneg hpos.le _
    have h0 : (LatticeProb.iidLaw d ν)
        ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6} ∩
          {ζ | largeSites d ν K n ζ = ∅})
        ≤ ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) :=
      le_trans (measure_small_inter_empty_le' ν hd n K _) hn.1
    have h1 : ∀ z₀ ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0,
        (LatticeProb.iidLaw d ν)
          ({ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6} ∩
            {ζ | largeSites d ν K n ζ = {z₀}})
          ≤ ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} *
            ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) := by
      intro z₀ _
      refine le_trans (measure_small_inter_singleton_eq ν hd n K _ z₀) ?_
      gcongr
      exact hn.2 z₀
    have hadd := measure_inter_card_le_one_le_add (LatticeProb.iidLaw d ν)
      ((Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0)
      (fun z ζ => originLevel d ν K n < -(greenRatioWeight d z * ζ z))
      {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 ≤ meanOriginAverage d ν n / 6}
      (ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)))
      (fun z₀ => ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)} *
        ENNReal.ofReal (meanOriginAverage d ν n ^ (-β))) h0 h1
    refine le_trans hadd ?_
    rw [← Finset.sum_mul]
    have hstep : (∑ z₀ ∈ (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).erase 0,
          ν {y : ℝ | originLevel d ν K n < -(greenRatioWeight d z₀ * y)}) *
        ENNReal.ofReal (meanOriginAverage d ν n ^ (-β))
        ≤ 1 * ENNReal.ofReal (meanOriginAverage d ν n ^ (-β)) := by
      gcongr
    refine le_trans (add_le_add le_rfl hstep) (le_of_eq ?_)
    rw [one_mul, ← two_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num


/-- **Case (b) of `prop:dgt4-contact-asymptotics` from an unconditioned deviation estimate.**
Everything of `sandpile.tex:5301-5412` except `TruncatedOriginDeviation` is proved: the
conditioning of Step 1 has become a truncation, the number of large sites is controlled, and
the passage to the deterministic level is the regular variation of the lower tail. -/
theorem caseThresholdField_linear_of_truncated
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α p K β : ℝ} (hα : 1 < α) (hp : 0 < p) (hpα : α < 2 * p) (hK : 0 < K) (hβ : α < β)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν)
    (hrv : LatticeProb.RegularlyVaryingAtTop (LatticeProb.lowerTail ν) (-α))
    (hsumc : Summable fun z : Sandpile.Site d => greenRatioWeight d z ^ p)
    (htr : TruncatedOriginDeviation d ν K β) :
    CaseThresholdField d ν (1 - 1 / α) :=
  caseThresholdField_linear_of_smallOriginNeighborAverage hGH d hd ν hatom hmean hvar hvar'
    hα hrv
    (smallOriginNeighborAverage_of_truncated hGH hd ν hatom hmean hvar hvar'
      hp hpα hK hβ hmom hrv hsumc htr)

end Sandpile
