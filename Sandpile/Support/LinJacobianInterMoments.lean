import Sandpile.Support.LinJacobianInter
import Sandpile.Support.LinEarlyVarMeasCov
import Sandpile.Support.LinEarlyVarCovBound

/-!
# Step 1's four intersection-count inputs, in Bochner form

The four inputs of Step 1 of `lem:dgt4-linearization-from-survival` that speak about the
intersection count, in the Bochner vocabulary that `Support/LinJacobianEarlyDisplay.lean`
asks for.

`eq:dgt4-tested-intersection-moments` (`sandpile.tex:5703-5709`) is proved in
`Support/LinTested.lean` with the intersection count in `ℝ≥0∞` and the two expectations as
iterated lower integrals, which is where it has no junk value. Step 1 works with a real
majorant `I(X,Y)` integrated against the law of the two walks. The passage between the two
is Tonelli for the product of the two walk laws, together with the finiteness of the first
moment in `d ≥ 5`: where the count is finite its real part is a genuine majorant of every
finite double sum of intersection indicators, and under the pair law that is almost
everywhere.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The intersection count is jointly measurable in the pair of paths. -/
theorem measurable_interCount_pair :
    Measurable fun p : (ℕ → Site d) × (ℕ → Site d) =>
      Sandpile.External.interCount p.1 p.2 := by
  classical
  have hset : ∀ p : ℕ × ℕ,
      MeasurableSet {P : (ℕ → Site d) × (ℕ → Site d) | P.1 p.1 = P.2 p.2} :=
    fun p => measurableSet_eq_fun
      ((measurable_pi_apply p.1).comp measurable_fst)
      ((measurable_pi_apply p.2).comp measurable_snd)
  have hfun : (fun P : (ℕ → Site d) × (ℕ → Site d) =>
      Sandpile.External.interCount P.1 P.2)
      = fun P => ∑' p : ℕ × ℕ,
        Set.indicator {P : (ℕ → Site d) × (ℕ → Site d) | P.1 p.1 = P.2 p.2}
          (fun _ => (1 : ℝ≥0∞)) P := by
    funext P
    rw [Sandpile.External.interCount]
    refine tsum_congr fun p => ?_
    by_cases h : P.1 p.1 = P.2 p.2
    · rw [Set.indicator_of_mem (by simpa using h), Set.indicator_of_mem (by simpa using h)]
    · rw [Set.indicator_of_notMem (by simpa using h), Set.indicator_of_notMem (by simpa using h)]
  rw [hfun]
  exact Measurable.tsum fun p => measurable_const.indicator (hset p)

/-- Tonelli for the two independent walks, at the intersection count. -/
theorem lintegral_walkPairLaw_interCount [NeZero d] (x y : Site d) :
    (∫⁻ p, Sandpile.External.interCount p.1 p.2 ∂(walkPairLaw d x y))
      = ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y) ∂(walkLaw d x) := by
  unfold walkPairLaw
  exact lintegral_prod _ measurable_interCount_pair.aemeasurable

/-- Tonelli for the two independent walks, at the square of the intersection count. -/
theorem lintegral_walkPairLaw_interCount_sq [NeZero d] (x y : Site d) :
    (∫⁻ p, Sandpile.External.interCount p.1 p.2 ^ 2 ∂(walkPairLaw d x y))
      = ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2 ∂(walkLaw d y) ∂(walkLaw d x) := by
  unfold walkPairLaw
  exact lintegral_prod _ (measurable_interCount_pair.pow_const 2).aemeasurable

/-- A finite first moment makes the intersection count finite almost everywhere
under the law of the two walks. -/
theorem ae_interCount_ne_top [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) :
    ∀ᵐ p ∂(walkPairLaw d x y), Sandpile.External.interCount p.1 p.2 ≠ ⊤ := by
  have h : (∫⁻ p, Sandpile.External.interCount p.1 p.2 ∂(walkPairLaw d x y)) ≠ ⊤ := by
    rw [lintegral_walkPairLaw_interCount]; exact hfin
  filter_upwards [ae_lt_top measurable_interCount_pair h] with p hp using hp.ne

/-- **The hypothesis `hsumI` of Step 1.**  Almost every pair of paths has a
finite intersection count, and there the real count majorizes every finite
double sum of intersection indicators. -/
theorem ae_sum_indicator_le_interCountReal [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) (t : Finset ℕ) :
    ∀ᵐ p ∂(walkPairLaw d x y),
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0)
        ≤ interCountReal p.1 p.2 := by
  filter_upwards [ae_interCount_ne_top x y hfin] with p hp
  exact sum_indicator_le_interCountReal t t p.1 p.2 hp

/-- The real intersection count is integrable under the law of the two walks. -/
theorem integrable_interCountReal [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) :
    Integrable (fun p => interCountReal p.1 p.2) (walkPairLaw d x y) :=
  integrable_toReal_of_lintegral_ne_top measurable_interCount_pair.aemeasurable
    (by rw [lintegral_walkPairLaw_interCount]; exact hfin)

/-- The square of the real intersection count is integrable under the law of the
two walks. -/
theorem integrable_interCountReal_sq [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) :
    Integrable (fun p => (interCountReal p.1 p.2) ^ 2) (walkPairLaw d x y) := by
  have hrw : (fun p : (ℕ → Site d) × (ℕ → Site d) => (interCountReal p.1 p.2) ^ 2)
      = fun p => (Sandpile.External.interCount p.1 p.2 ^ 2).toReal := by
    funext p
    rw [interCountReal, ENNReal.toReal_pow]
  rw [hrw]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_interCount_pair.pow_const 2).aemeasurable
    (by rw [lintegral_walkPairLaw_interCount_sq]; exact hfin)

/-- The Bochner first moment of the real intersection count is the real part of
the iterated lower integral. -/
theorem integral_interCountReal_eq [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) :
    (∫ p, interCountReal p.1 p.2 ∂(walkPairLaw d x y))
      = (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
          ∂(walkLaw d y) ∂(walkLaw d x)).toReal := by
  rw [← lintegral_walkPairLaw_interCount x y]
  refine integral_toReal measurable_interCount_pair.aemeasurable ?_
  filter_upwards [ae_interCount_ne_top x y hfin] with p hp using hp.lt_top

/-- The Bochner second moment of the real intersection count is the real part of
the iterated lower integral of the square. -/
theorem integral_interCountReal_sq_eq [NeZero d] (x y : Site d)
    (hfin : (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
      ∂(walkLaw d y) ∂(walkLaw d x)) ≠ ⊤) :
    (∫ p, (interCountReal p.1 p.2) ^ 2 ∂(walkPairLaw d x y))
      = (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
          ∂(walkLaw d y) ∂(walkLaw d x)).toReal := by
  have hrw : (fun p : (ℕ → Site d) × (ℕ → Site d) => (interCountReal p.1 p.2) ^ 2)
      = fun p => (Sandpile.External.interCount p.1 p.2 ^ 2).toReal := by
    funext p
    rw [interCountReal, ENNReal.toReal_pow]
  rw [hrw, ← lintegral_walkPairLaw_interCount_sq x y]
  refine integral_toReal (measurable_interCount_pair.pow_const 2).aemeasurable ?_
  have h : (∫⁻ p, Sandpile.External.interCount p.1 p.2 ^ 2 ∂(walkPairLaw d x y)) ≠ ⊤ := by
    rw [lintegral_walkPairLaw_interCount_sq]; exact hfin
  exact ae_lt_top (measurable_interCount_pair.pow_const 2) h

/-- A weighted double sum bounded in `ℝ≥0∞` is bounded in `ℝ` after taking real
parts, the weights being nonnegative reals. -/
theorem sum_sum_toReal_le_of_ennreal {ι : Type*} (s : Finset ι) (w : ι → ι → ℝ)
    (hw : ∀ x y, 0 ≤ w x y) (F : ι → ι → ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C)
    (hle : ∑ x ∈ s, ∑ y ∈ s, ENNReal.ofReal (w x y) * F x y ≤ ENNReal.ofReal C) :
    ∑ x ∈ s, ∑ y ∈ s, w x y * (F x y).toReal ≤ C := by
  classical
  have hStop : (∑ x ∈ s, ∑ y ∈ s, ENNReal.ofReal (w x y) * F x y) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hrowtop : ∀ x ∈ s, (∑ y ∈ s, ENNReal.ofReal (w x y) * F x y) ≠ ⊤ := by
    intro x hx
    refine ne_top_of_le_ne_top hStop ?_
    exact Finset.single_le_sum
      (f := fun x => ∑ y ∈ s, ENNReal.ofReal (w x y) * F x y) (fun _ _ => by simp) hx
  have htermtop : ∀ x ∈ s, ∀ y ∈ s, ENNReal.ofReal (w x y) * F x y ≠ ⊤ := by
    intro x hx y hy
    refine ne_top_of_le_ne_top (hrowtop x hx) ?_
    exact Finset.single_le_sum
      (f := fun y => ENNReal.ofReal (w x y) * F x y) (fun _ _ => by simp) hy
  have heq : ∑ x ∈ s, ∑ y ∈ s, w x y * (F x y).toReal
      = (∑ x ∈ s, ∑ y ∈ s, ENNReal.ofReal (w x y) * F x y).toReal := by
    rw [ENNReal.toReal_sum hrowtop]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ENNReal.toReal_sum (htermtop x hx)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw x y)]
  rw [heq]
  calc (∑ x ∈ s, ∑ y ∈ s, ENNReal.ofReal (w x y) * F x y).toReal
      ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = C := ENNReal.toReal_ofReal hC

/-- The conditional covariance of two survivals is a measurable function of the
pair of paths. -/
theorem measurable_covSurvival_fun (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ]
    (n i j : ℕ) :
    Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) => covSurvival μ n i j p.1 p.2) := by
  classical
  show Measurable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∫ σ : Site d → ℝ, (survivalInd σ n i p.1 - ∫ σ', survivalInd σ' n i p.1 ∂μ) *
        (survivalInd σ n j p.2 - ∫ σ', survivalInd σ' n j p.2 ∂μ) ∂μ)
  have hswap : Measurable fun q : ((ℕ → Site d) × (ℕ → Site d)) × (Site d → ℝ) =>
      (survivalInd q.2 n i q.1.1 - ∫ σ', survivalInd σ' n i q.1.1 ∂μ) *
        (survivalInd q.2 n j q.1.2 - ∫ σ', survivalInd σ' n j q.1.2 ∂μ) := by
    refine Measurable.mul ?_ ?_
    · refine Measurable.sub ?_ ?_
      · exact (measurable_uncurry_survival n i).comp
          ((measurable_snd).prodMk (measurable_fst.comp measurable_fst))
      · exact (measurable_integral_survivalInd μ n i).comp (measurable_fst.comp measurable_fst)
    · refine Measurable.sub ?_ ?_
      · exact (measurable_uncurry_survival n j).comp
          ((measurable_snd).prodMk (measurable_snd.comp measurable_fst))
      · exact (measurable_integral_survivalInd μ n j).comp (measurable_snd.comp measurable_fst)
  exact (hswap.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- **The hypothesis `hint3` of Step 1.**  The double sum of intersection
indicators against the conditional covariances is bounded by the number of time
pairs and is measurable, hence integrable under the law of the two walks. -/
theorem integrable_sum_indicator_mul_covSurvival [NeZero d]
    (μ : Measure (Site d → ℝ)) [IsProbabilityMeasure μ] (n : ℕ) (t : Finset ℕ)
    (x y : Site d) :
    Integrable (fun p : (ℕ → Site d) × (ℕ → Site d) =>
      ∑ i ∈ t, ∑ j ∈ t, (if p.1 i = p.2 j then (1 : ℝ) else 0) *
        covSurvival μ n i j p.1 p.2) (walkPairLaw d x y) := by
  classical
  have hmeas : ∀ i ∈ t, ∀ j ∈ t, Measurable
      (fun p : (ℕ → Site d) × (ℕ → Site d) =>
        (if p.1 i = p.2 j then (1 : ℝ) else 0) * covSurvival μ n i j p.1 p.2) := by
    intro i _ j _
    refine Measurable.mul ?_ (measurable_covSurvival_fun μ n i j)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply j).comp measurable_snd)
  refine integrable_finsetSum t fun i hi => integrable_finsetSum t fun j hj => ?_
  refine Integrable.mono' (integrable_const (1 : ℝ)) (hmeas i hi j hj).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  rw [norm_mul]
  have h1 : ‖(if p.1 i = p.2 j then (1 : ℝ) else 0)‖ ≤ 1 := by
    by_cases h : p.1 i = p.2 j <;> simp [h]
  have h2 : ‖covSurvival μ n i j p.1 p.2‖ ≤ 1 := by
    rw [Real.norm_eq_abs]; exact abs_covSurvival_le_one μ n i j p.1 p.2
  calc ‖(if p.1 i = p.2 j then (1 : ℝ) else 0)‖ * ‖covSurvival μ n i j p.1 p.2‖
      ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := by ring

end Sandpile
