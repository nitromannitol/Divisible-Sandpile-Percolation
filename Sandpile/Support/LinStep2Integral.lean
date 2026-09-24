/-
The integration over the walk of Step 2 of `lem:dgt4-path-survival`
(`sandpile.tex:5529-5583`).

`Support/LinStep2Chain.lean` bounds, for a FIXED path `X`, the deviation of the
survival probability from the profile `x^κ` by four errors, the last of which is
controlled by a bound `η'` on the last-visit defect `|G(0,0)S(X)+\log x|`.  What
`lem:dgt4-weighted-last-visits` supplies is not a pointwise bound on that defect but an
INTEGRAL one, so the chain is applied along each path with its own pointwise defect in
place of `η'` and the resulting bound is integrated.  Since the pointwise chain is affine
in the defect, the integration is `integral_mono` against
`c + (κ + εκ)|G(0,0)S(X)+\log x|`.

Three bridges are needed first.  The frozen statement writes the survival probability as
`∫_σ S_{n,j}(X)`, an integral of the path-space indicator with `σ` held fixed, while the
chain of `Support/LinStep2Chain.lean` writes it as the measure of the scenery event; they
agree because the indicator, read as a function of `σ`, is the indicator of that event
(`integral_survival_eq_measureReal`), whose measurability is
`measurableSet_survivalSet`.  The integration over path space also needs the survival
probability to be measurable in `X`, which is the joint measurability of
`Support/LinSurvivalMeas.lean` followed by `StronglyMeasurable.integral_prod_left'`.
-/
import Sandpile.Support.LinStep2Chain
import Sandpile.Support.LinSurvivalMeas
import Sandpile.Support.LinStep2

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The scenery event that the odometer stays positive along the first `j` steps of a fixed
path is measurable: it is the countable intersection over `r ≤ j` of the events
`0 < u_{n-r}(X_r)`. -/
theorem measurableSet_survivalSet (n j : ℕ) (X : ℕ → Site d) :
    MeasurableSet {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)} := by
  have hset : {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
      = ⋂ r : ℕ, ⋂ _ : r ≤ j, {σ : Site d → ℝ | 0 < odometer σ (n - r) (X r)} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun r => MeasurableSet.iInter fun _ =>
    measurableSet_lt measurable_const (measurable_odometer (n - r) (X r))

/-- **`P(S_{n,j}(X)=1 | X)` in the two shapes.**  The frozen statement integrates the
path-space indicator `S_{n,j}` of `sandpile.tex:5443-5446` over the scenery; the chain of
Step 2 uses the measure of the scenery event.  They are equal. -/
theorem integral_survival_eq_measureReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n j : ℕ) (X : ℕ → Site d) :
    ∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)
      = (centeredMassLaw d ν).real
          {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)} := by
  have hfun : (fun σ : Site d → ℝ =>
      Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X)
      = Set.indicator {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
          (1 : (Site d → ℝ) → ℝ) := by
    funext σ
    by_cases h : ∀ r ≤ j, 0 < odometer σ (n - r) (X r)
    · rw [Set.indicator_of_mem (show X ∈ {Y : ℕ → Site d |
        ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} from h),
        Set.indicator_of_mem (show σ ∈ {σ : Site d → ℝ |
        ∀ r ≤ j, 0 < odometer σ (n - r) (X r)} from h)]
      rfl
    · rw [Set.indicator_of_notMem (show X ∉ {Y : ℕ → Site d |
        ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)} from h),
        Set.indicator_of_notMem (show σ ∉ {σ : Site d → ℝ |
        ∀ r ≤ j, 0 < odometer σ (n - r) (X r)} from h)]
  rw [hfun, integral_indicator_one (measurableSet_survivalSet n j X)]

/-- **The survival probability is a measurable function of the path.**  This is the joint
measurability of `Support/LinSurvivalMeas.lean` followed by the measurability of a Bochner
integral in the remaining variable. -/
theorem stronglyMeasurable_survivalProb (ν : Measure ℝ) [IsProbabilityMeasure ν] (n j : ℕ) :
    StronglyMeasurable fun X : ℕ → Site d =>
      ∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
        (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν) :=
  (measurable_uncurry_survival n j).stronglyMeasurable.integral_prod_left'

/-- **Step 2 of `lem:dgt4-path-survival`, integrated over the walk.**  The pointwise chain
of `Sandpile.abs_survival_sub_rpow_le` is applied along each path with its own last-visit
defect `|G S(X) + \log x|` in place of `η'`, and the affine bound that results is integrated;
`hlvint` is what `lem:dgt4-weighted-last-visits` supplies. -/
theorem integral_abs_survival_sub_rpow_le [NeZero d]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (eta theta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ X : ℕ → Site d, ∀ (m : ℕ) (ts : Fin m → ℕ),
      Function.Injective (fun i => X (ts i)) → (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta)
    (pi : ℕ → ℝ)
    (hpi : ∀ r, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r} = 1 - pi r)
    (kappa G L eta' eps x Q : ℝ) (S : (ℕ → Site d) → ℝ)
    (hpi0 : ∀ r ∈ Finset.range (j + 1), 0 ≤ pi r)
    (hpih : ∀ r ∈ Finset.range (j + 1), pi r ≤ 1 / 2)
    (hkappa : 0 < kappa) (hGS : ∀ X, 0 ≤ G * S X) (heps : 0 ≤ eps)
    (hx : 0 < x) (hx1 : x ≤ 1) (hL : L = Real.log x)
    (hQ : ∀ X : ℕ → Site d, (∑ r ∈ Finset.range (j + 1),
        ((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ) : ℝ) * pi r ^ 2) ≤ Q)
    (hPd : ∀ X : ℕ → Site d, |(∑ r ∈ Finset.range (j + 1),
        ((if r ∈ lastVisitTimes j X then 1 else 0 : ℕ) : ℝ) * pi r) - kappa * (G * S X)|
      ≤ eps * (kappa * (G * S X)))
    (hSint : Integrable (fun X : ℕ → Site d => |G * S X + L|) (walkLaw d 0))
    (hlvint : ∫ X, |G * S X + L| ∂(walkLaw d 0) ≤ eta') :
    ∫ X, |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - x ^ kappa| ∂(walkLaw d 0)
      ≤ (eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta) + 2 * Q
        + (kappa * eta' + eps * kappa * (eta' - L)) := by
  classical
  have hpt : ∀ X : ℕ → Site d,
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - x ^ kappa|
        ≤ ((eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta) + 2 * Q
            - eps * kappa * L) + (kappa + eps * kappa) * |G * S X + L| := by
    intro X
    rw [integral_survival_eq_measureReal ν n j X]
    have h := abs_survival_sub_rpow_le ν J b hb hshift n j hj X eta theta hthr (hfact X) pi hpi
      kappa G (S X) L |G * S X + L| eps x hpi0 hpih hkappa (hGS X) heps hx hx1 hL le_rfl (hPd X)
    have hq := hQ X
    linarith [h, hq]
  have hcoef : (0 : ℝ) ≤ kappa + eps * kappa := by nlinarith
  have hRHSint : Integrable (fun X : ℕ → Site d =>
      ((eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta) + 2 * Q
        - eps * kappa * L) + (kappa + eps * kappa) * |G * S X + L|) (walkLaw d 0) :=
    (integrable_const _).add (hSint.const_mul _)
  have hmeas : AEStronglyMeasurable (fun X : ℕ → Site d =>
      (∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - x ^ kappa) (walkLaw d 0) :=
    ((stronglyMeasurable_survivalProb ν n j).sub
      stronglyMeasurable_const).aestronglyMeasurable
  have hlhsint : Integrable (fun X : ℕ → Site d =>
      |(∫ σ, Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
            (fun _ => (1 : ℝ)) X ∂(centeredMassLaw d ν)) - x ^ kappa|) (walkLaw d 0) :=
    (Integrable.mono' hRHSint hmeas (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact hpt X)).abs
  have hmono := integral_mono hlhsint hRHSint hpt
  rw [integral_add (integrable_const _) (hSint.const_mul _), integral_const,
    integral_const_mul, probReal_univ, smul_eq_mul, one_mul] at hmono
  nlinarith [hmono, mul_le_mul_of_nonneg_left hlvint hcoef]

end Sandpile
