import Sandpile.Support.LinReturn
import LatticeProb.Prob.EfronSteinInequality

/-!
# Covariance of the survival indicators at two times

The covariance of the survival indicators of the walk at two times, in the form
the last-visit estimate `sandpile.tex:4760-4776`
(label `lem:dgt4-weighted-last-visits`) needs.

Writing `I_i^∞` for the indicator that the walk never returns to its position at
time `i`, the paper's proof compares `I_{i,j}` with `I_i^∞` and uses that the
`I_i^∞` are a stationary sequence with summable correlations.  The correlation
bound is elementary: `I_0^∞` is dominated by the indicator `B_k` that the walk
avoids the origin during its first `k` steps, `B_k` is a function of the first
`k` increments and `I_k^∞` is a function of the increments from time `k` on, so
`B_k` and `I_k^∞` are independent, and the two indicators differ in mean by
`ρ_k - ρ_∞`, the chance that the first return is finite but later than `k`.
-/

open MeasureTheory Filter Topology

namespace Sandpile
variable {d : ℕ}

/-- At `i = 0`, `visitInd 0 m X` reduces to the indicator of `noRet d m` evaluated
directly at `X`, since `relPath 0 X ∈ noRet d m` iff `X ∈ noRet d m`
(`preimage_relPath_zero_noRet`). -/
theorem visitInd_zero (m : ℕ) (X : ℕ → Site d) :
    visitInd 0 m X = Set.indicator (noRet d m) (fun _ => (1:ℝ)) X := by
  have hiff : relPath (d := d) 0 X ∈ noRet d m ↔ X ∈ noRet d m := by
    rw [← Set.mem_preimage, preimage_relPath_zero_noRet m]
  by_cases h : X ∈ noRet d m
  · rw [visitInd, Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h]
  · rw [visitInd, Set.indicator_of_notMem (fun hc => h (hiff.mp hc)), Set.indicator_of_notMem h]

/-- Likewise, `survInd 0 X` reduces to the indicator of `noRetEver d` evaluated
directly at `X`, via `preimage_relPath_zero_noRetEver`. -/
theorem survInd_zero (X : ℕ → Site d) :
    survInd 0 X = Set.indicator (noRetEver d) (fun _ => (1:ℝ)) X := by
  have hiff : relPath (d := d) 0 X ∈ noRetEver d ↔ X ∈ noRetEver d := by
    rw [← Set.mem_preimage, preimage_relPath_zero_noRetEver]
  by_cases h : X ∈ noRetEver d
  · rw [survInd, Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h]
  · rw [survInd, Set.indicator_of_notMem (fun hc => h (hiff.mp hc)), Set.indicator_of_notMem h]

/-- The change-of-variables formula for integrating over `walkLaw d 0`: since it is
definitionally the pushforward of `LatticeProb.incPathLaw d` under `walkPath 0`
(`integral_map`), integrating `F` over the walk law equals integrating `F ∘ walkPath 0`
over the increment path law. -/
theorem integral_walkLaw_zero [NeZero d] {F : (ℕ → Site d) → ℝ} (hF : Measurable F) :
    ∫ X, F X ∂(walkLaw d 0) = ∫ ξ, F (walkPath (0 : Site d) ξ) ∂(LatticeProb.incPathLaw d) := by
  have hbase : walkLaw d 0 = (LatticeProb.incPathLaw d).map (walkPath (0 : Site d)) := rfl
  rw [hbase, integral_map (measurable_walkPath 0).aemeasurable hF.aestronglyMeasurable]

/-- Pulling `integral_visitInd` back through `integral_walkLaw_zero` and `visitInd_zero`
identifies the increment-path integral of the raw `noRet d m` indicator with
`retProb d m`. -/
theorem integral_indNoRet [NeZero d] (m : ℕ) :
    ∫ ξ, Set.indicator (noRet d m) (fun _ => (1:ℝ)) (walkPath (0 : Site d) ξ)
      ∂(LatticeProb.incPathLaw d) = retProb d m := by
  have h := integral_walkLaw_zero (d := d)
    (F := fun X => Set.indicator (noRet d m) (fun _ => (1:ℝ)) X)
    (measurable_const.indicator (measurableSet_noRet m))
  rw [← h, ← integral_visitInd (d := d) 0 m]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => (visitInd_zero m X).symm)

/-- The analogous identity for `noRetEver d`, pulling `integral_survInd` back through
`integral_walkLaw_zero` and `survInd_zero` to identify the increment-path integral of
the indicator with `escProb d`. -/
theorem integral_indNoRetEver [NeZero d] :
    ∫ ξ, Set.indicator (noRetEver d) (fun _ => (1:ℝ)) (walkPath (0 : Site d) ξ)
      ∂(LatticeProb.incPathLaw d) = escProb d := by
  have h := integral_walkLaw_zero (d := d)
    (F := fun X => Set.indicator (noRetEver d) (fun _ => (1:ℝ)) X)
    (measurable_const.indicator measurableSet_noRetEver)
  rw [← h, ← integral_survInd (d := d) 0]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => (survInd_zero X).symm)


section Indep
variable {d : ℕ}

/-- The `noRet` event at range `k` reads only the first `k` positions. -/
theorem indNoRet_truncInc (k : ℕ) (ξ : ℕ → Site d) :
    Set.indicator (noRet d k) (fun _ => (1:ℝ)) (walkPath (0 : Site d) (LatticeProb.truncInc k ξ))
      = Set.indicator (noRet d k) (fun _ => (1:ℝ)) (walkPath (0 : Site d) ξ) := by
  have hcoord : ∀ r : ℕ, r ≤ k →
      walkPath (0 : Site d) (LatticeProb.truncInc k ξ) r = walkPath (0 : Site d) ξ r := by
    intro r hr
    exact LatticeProb.sitePath_truncInc hr (0 : Site d) ξ
  have hiff : walkPath (0 : Site d) (LatticeProb.truncInc k ξ) ∈ noRet d k
      ↔ walkPath (0 : Site d) ξ ∈ noRet d k := by
    constructor
    · intro h r hr1 hr2
      have := h r hr1 hr2
      rwa [hcoord r hr2, hcoord 0 (Nat.zero_le k)] at this
    · intro h r hr1 hr2
      have := h r hr1 hr2
      rwa [← hcoord r hr2, ← hcoord 0 (Nat.zero_le k)] at this
  by_cases h : walkPath (0 : Site d) ξ ∈ noRet d k
  · rw [Set.indicator_of_mem (hiff.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h (hiff.mp hc)), Set.indicator_of_notMem h]

/-- **Independence of the visit and survival indicators across the split at time
`k`.**  Since `visitInd 0 k` depends only on the first `k` increments
(`indNoRet_truncInc`) and `survInd k` only on the increments from `k` on, the product
integral factors via `LatticeProb.integral_truncInc_shiftInc` into `retProb d k * escProb d`. -/
theorem integral_visitInd_mul_survInd [NeZero d] (k : ℕ) :
    ∫ X, visitInd 0 k X * survInd k X ∂(walkLaw d 0) = retProb d k * escProb d := by
  classical
  set g : (ℕ → Site d) → ℝ := fun a => Set.indicator (noRet d k) (fun _ => (1:ℝ))
    (walkPath (0 : Site d) a) with hg
  set h : (ℕ → Site d) → ℝ := fun b => Set.indicator (noRetEver d) (fun _ => (1:ℝ))
    (walkPath (0 : Site d) b) with hh
  have hgmeas : Measurable g :=
    (measurable_const.indicator (measurableSet_noRet k)).comp (measurable_walkPath 0)
  have hhmeas : Measurable h :=
    (measurable_const.indicator measurableSet_noRetEver).comp (measurable_walkPath 0)
  set Φ : (ℕ → Site d) → (ℕ → Site d) → ℝ := fun a b => g a * h b with hΦ
  have hΦmeas : Measurable (Function.uncurry Φ) :=
    (hgmeas.comp measurable_fst).mul (hhmeas.comp measurable_snd)
  have hgb : ∀ a, |g a| ≤ 1 := by
    intro a
    rcases Classical.em (walkPath (0 : Site d) a ∈ noRet d k) with hm | hm
    · simp [hg, Set.indicator_of_mem hm]
    · simp [hg, Set.indicator_of_notMem hm]
  have hhb : ∀ b, |h b| ≤ 1 := by
    intro b
    rcases Classical.em (walkPath (0 : Site d) b ∈ noRetEver d) with hm | hm
    · simp [hh, Set.indicator_of_mem hm]
    · simp [hh, Set.indicator_of_notMem hm]
  have hΦb : ∀ a b, ‖Φ a b‖ ≤ 1 := by
    intro a b
    rw [hΦ]
    simp only [Real.norm_eq_abs, abs_mul]
    calc |g a| * |h b| ≤ 1 * 1 := by
          exact mul_le_mul (hgb a) (hhb b) (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hFmeas : Measurable fun X : ℕ → Site d => visitInd 0 k X * survInd k X :=
    (measurable_visitInd 0 k).mul (measurable_survInd k)
  rw [integral_walkLaw_zero hFmeas]
  have hpt : ∀ ξ : ℕ → Site d,
      visitInd 0 k (walkPath (0 : Site d) ξ) * survInd k (walkPath (0 : Site d) ξ)
        = Φ (LatticeProb.truncInc k ξ) (LatticeProb.shiftInc k ξ) := by
    intro ξ
    rw [visitInd_zero, survInd, relPath_walkPath, hΦ]
    simp only [hg, hh]
    rw [indNoRet_truncInc k ξ]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    LatticeProb.integral_truncInc_shiftInc d k Φ hΦmeas hΦb]
  have hinner : ∀ ξ : ℕ → Site d,
      (∫ η, Φ (LatticeProb.truncInc k ξ) η ∂(LatticeProb.incPathLaw d)) = g ξ * escProb d := by
    intro ξ
    simp only [hΦ]
    rw [integral_const_mul]
    congr 1
    · exact indNoRet_truncInc k ξ
    · exact integral_indNoRetEver
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const,
    integral_indNoRet k]

end Indep

/-! ### Integrability and the covariance bound -/

variable {d : ℕ}

/-- A measurable function bounded in absolute value by a constant `C` is integrable
against the (finite) measure `walkLaw d 0`. -/
theorem integrable_of_bdd [NeZero d] {F : (ℕ → Site d) → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ X, |F X| ≤ C) : Integrable F (walkLaw d 0) :=
  Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hC X)

/-- `survInd i` is integrable against `walkLaw d 0`, being bounded between `0` and `1`
(`survInd_nonneg`, `survInd_le_one`). -/
theorem integrable_survInd [NeZero d] (i : ℕ) : Integrable (survInd (d := d) i) (walkLaw d 0) :=
  integrable_of_bdd (measurable_survInd i) (C := 1) fun X => by
    rw [abs_of_nonneg (survInd_nonneg i X)]; exact survInd_le_one i X

/-- `visitInd i m` is integrable against `walkLaw d 0`, being bounded between `0` and `1`
(`visitInd_nonneg`, `visitInd_le_one`). -/
theorem integrable_visitInd [NeZero d] (i m : ℕ) :
    Integrable (visitInd (d := d) i m) (walkLaw d 0) :=
  integrable_of_bdd (measurable_visitInd i m) (C := 1) fun X => by
    rw [abs_of_nonneg (visitInd_nonneg i m X)]; exact visitInd_le_one i m X

/-- `relPath i` preserves the law of the walk (`measurePreserving_relPath`), so
integrating a function of the shifted path equals integrating the function itself. -/
theorem integral_comp_relPath [NeZero d] (i : ℕ) {F : (ℕ → Site d) → ℝ} (hF : Measurable F) :
    ∫ X, F (relPath i X) ∂(walkLaw d 0) = ∫ X, F X ∂(walkLaw d 0) := by
  conv_rhs => rw [← (measurePreserving_relPath (d := d) i).map_eq]
  rw [integral_map (measurable_relPath i).aemeasurable hF.aestronglyMeasurable]

/-- Shifting the survival indicator's base time by `relPath i` amounts to adding `i`
to its own time index, via `relPath_relPath`. -/
theorem survInd_relPath (i k : ℕ) (X : ℕ → Site d) :
    survInd k (relPath i X) = survInd (i + k) X := by
  rw [survInd, survInd, relPath_relPath]

/-- The survival correlation at lag `k` does not depend on the starting time. -/
theorem integral_survInd_mul_shift [NeZero d] (i k : ℕ) :
    ∫ X, survInd i X * survInd (i + k) X ∂(walkLaw d 0)
      = ∫ X, survInd 0 X * survInd k X ∂(walkLaw d 0) := by
  have hF : Measurable fun Y : ℕ → Site d => survInd (d := d) 0 Y * survInd (d := d) k Y :=
    (measurable_survInd 0).mul (measurable_survInd k)
  have h := integral_comp_relPath (d := d) i hF
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show survInd i X * survInd (i + k) X = survInd 0 (relPath i X) * survInd k (relPath i X)
  rw [survInd_relPath i 0 X, survInd_relPath i k X, Nat.add_zero]

/-- **The correlation bound.**  The survival indicators at two times separated by
`k` decorrelate at the rate at which the first return time stops being finite. -/
theorem abs_cov_survInd_le [NeZero d] (i k : ℕ) :
    |(∫ X, survInd i X * survInd (i + k) X ∂(walkLaw d 0)) - escProb d * escProb d|
      ≤ 2 * (retProb d k - escProb d) := by
  rw [integral_survInd_mul_shift i k]
  have hdiffnn : ∀ X : ℕ → Site d, 0 ≤ visitInd (d := d) 0 k X - survInd (d := d) 0 X :=
    fun X => sub_nonneg.mpr (survInd_le_visitInd 0 k X)
  have hint1 : Integrable (fun X => visitInd (d := d) 0 k X * survInd (d := d) k X)
      (walkLaw d 0) :=
    integrable_of_bdd ((measurable_visitInd 0 k).mul (measurable_survInd k)) (C := 1) fun X => by
      rw [abs_mul, abs_of_nonneg (visitInd_nonneg 0 k X), abs_of_nonneg (survInd_nonneg k X)]
      exact mul_le_one₀ (visitInd_le_one 0 k X) (survInd_nonneg k X) (survInd_le_one k X)
  have hint2 : Integrable (fun X => survInd (d := d) 0 X * survInd (d := d) k X)
      (walkLaw d 0) :=
    integrable_of_bdd ((measurable_survInd 0).mul (measurable_survInd k)) (C := 1) fun X => by
      rw [abs_mul, abs_of_nonneg (survInd_nonneg 0 X), abs_of_nonneg (survInd_nonneg k X)]
      exact mul_le_one₀ (survInd_le_one 0 X) (survInd_nonneg k X) (survInd_le_one k X)
  have hdiff : (∫ X, visitInd (d := d) 0 k X * survInd (d := d) k X ∂(walkLaw d 0))
      - (∫ X, survInd (d := d) 0 X * survInd (d := d) k X ∂(walkLaw d 0))
      ≤ retProb d k - escProb d := by
    rw [← integral_sub hint1 hint2]
    have hle : ∀ X : ℕ → Site d,
        visitInd (d := d) 0 k X * survInd (d := d) k X
          - survInd (d := d) 0 X * survInd (d := d) k X
          ≤ visitInd (d := d) 0 k X - survInd (d := d) 0 X := by
      intro X
      have h1 : (visitInd (d := d) 0 k X - survInd (d := d) 0 X) * survInd (d := d) k X
          ≤ (visitInd (d := d) 0 k X - survInd (d := d) 0 X) * 1 :=
        mul_le_mul_of_nonneg_left (survInd_le_one k X) (hdiffnn X)
      nlinarith [h1]
    have hb : Integrable (fun X => visitInd (d := d) 0 k X - survInd (d := d) 0 X)
        (walkLaw d 0) := (integrable_visitInd 0 k).sub (integrable_survInd 0)
    calc ∫ X, (visitInd (d := d) 0 k X * survInd (d := d) k X
            - survInd (d := d) 0 X * survInd (d := d) k X) ∂(walkLaw d 0)
        ≤ ∫ X, (visitInd (d := d) 0 k X - survInd (d := d) 0 X) ∂(walkLaw d 0) :=
          integral_mono (hint1.sub hint2) hb hle
      _ = retProb d k - escProb d := by
          rw [integral_sub (integrable_visitInd 0 k) (integrable_survInd 0),
            integral_visitInd 0 k, integral_survInd 0]
  have hge : (∫ X, survInd (d := d) 0 X * survInd (d := d) k X ∂(walkLaw d 0))
      ≤ ∫ X, visitInd (d := d) 0 k X * survInd (d := d) k X ∂(walkLaw d 0) := by
    refine integral_mono hint2 hint1 fun X => ?_
    exact mul_le_mul_of_nonneg_right (survInd_le_visitInd 0 k X) (survInd_nonneg k X)
  have hprod := integral_visitInd_mul_survInd (d := d) k
  have hesc1 : escProb d ≤ 1 := le_trans (escProb_le_retProb 0) (retProb_le_one 0)
  have hesc0 : 0 ≤ escProb d := escProb_nonneg
  have hret : escProb d ≤ retProb d k := escProb_le_retProb k
  rw [abs_le]
  constructor <;> nlinarith [hdiff, hge, hprod, hesc0, hesc1, hret]

end Sandpile
