/-
The quantitative form of the multi-parameter Kolmogorov criterion: a polynomial
tail for the supremum of a process over a box, with an exponent equal to the
moment exponent and a constant that does not depend on the process.

`LatticeProb.kolmogorovBoundPi` is a tightness criterion: for each accuracy it
produces one level, valid for EVERY process on EVERY probability space obeying
the same increment and anchor moment bounds on the box, but with no rate in the
accuracy.  An infinite union over the boxes of a lattice needs a rate, and the
criterion supplies one by itself.  Fix the accuracy at one half and let `B` be
the resulting level.  Given a process `X` and a level `L`, condition the measure
on the event that `X` exceeds `L` somewhere on the box and multiply the process
by the `p`-th root of the probability of that event.  Conditioning multiplies
every `p`-th moment by at most the reciprocal of that probability, and the
rescaling multiplies it by exactly that probability, so the rescaled process on
the conditioned space obeys the SAME two moment bounds and the criterion applies
to it unchanged.  Its conclusion says that the rescaled process exceeds `B`
somewhere on the box with conditional probability at most one half; but if the
probability of the original event were larger than `(B/L)^p`, the rescaled
process would exceed `B` on the whole of the conditioning event, whose
conditional probability is one.  Hence the event has probability at most
`(B/L)^p`.

The event is measurable because the paths are continuous on the box and the box
has a countable dense subset, namely the clamp of a countable dense subset of
the ambient space.
-/
import Sandpile.Support.ContKolmogorovAssembly

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The event that a process with continuous paths exceeds a level somewhere on a box is
measurable: the box has a countable dense subset, and on it the event is a countable union. -/
theorem measurableSet_exists_lt_abs {k : ℕ} {a b : Fin k → ℝ} (hab : a ≤ b)
    {Ω : Type*} [MeasurableSpace Ω] (X : (Fin k → ℝ) → Ω → ℝ)
    (hmeas : ∀ u, Measurable (X u))
    (hcont : ∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) (L : ℝ) :
    MeasurableSet {ω | ∃ u ∈ Set.Icc a b, L < |X u ω|} := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin k → ℝ)
  set E : Set (Fin k → ℝ) := LatticeProb.boxClamp a b hab '' D with hE
  have hEc : E.Countable := hDc.image _
  have hEsub : E ⊆ Set.Icc a b := by
    rintro _ ⟨x, -, rfl⟩; exact LatticeProb.boxClamp_mem a b hab x
  have hEdense : Set.Icc a b ⊆ closure E := by
    intro u hu
    have h2 : LatticeProb.boxClamp a b hab '' closure D ⊆ closure E :=
      image_closure_subset_closure_image (LatticeProb.continuous_boxClamp a b hab)
    rw [hDd.closure_eq] at h2
    have h3 : LatticeProb.boxClamp a b hab u ∈ closure E := h2 ⟨u, Set.mem_univ u, rfl⟩
    rwa [LatticeProb.boxClamp_eq hab hu] at h3
  have hset : {ω | ∃ u ∈ Set.Icc a b, L < |X u ω|} = ⋃ u ∈ E, {ω | L < |X u ω|} := by
    ext ω
    constructor
    · rintro ⟨u, hu, hlt⟩
      have hcw : ContinuousWithinAt (fun v => |X v ω|) (Set.Icc a b) u :=
        ((hcont ω).abs) u hu
      have hev : ∀ᶠ v in nhdsWithin u (Set.Icc a b), L < |X v ω| :=
        hcw.eventually (eventually_gt_nhds hlt)
      have hle : nhdsWithin u E ≤ nhdsWithin u (Set.Icc a b) := nhdsWithin_mono u hEsub
      haveI hne : (nhdsWithin u E).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hEdense hu)
      have h1 : ∀ᶠ v in nhdsWithin u E, L < |X v ω| := hev.filter_mono hle
      have h2 : ∀ᶠ v in nhdsWithin u E, v ∈ E := self_mem_nhdsWithin
      obtain ⟨v, hv⟩ := (h1.and h2).exists
      exact Set.mem_iUnion₂.mpr ⟨v, hv.2, hv.1⟩
    · intro h
      obtain ⟨u, hu, hlt⟩ := Set.mem_iUnion₂.mp h
      exact ⟨u, hEsub hu, hlt⟩
  rw [hset]
  exact MeasurableSet.biUnion hEc (fun u _ => measurableSet_lt measurable_const (hmeas u).abs)


/-- **A polynomial tail for the supremum on a box, from the tightness criterion alone.**  The
constant `B` depends only on the box, the moment exponents and the moment bound, and the tail
exponent is the moment exponent, which is what an infinite union over a lattice of boxes needs. -/
theorem kolmogorov_polynomial_tail (k : ℕ) (a b : Fin k → ℝ) (hab : a ≤ b)
    (p q M : ℝ) (hp : 0 < p) (hq : (k : ℝ) < q) :
    ∃ B : ℝ, 0 < B ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ X : (Fin k → ℝ) → Ω → ℝ,
          (∀ u, Measurable (X u)) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            Integrable (fun ω => |X u ω - X v ω| ^ p) P) →
          (∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
            ∫ ω, |X u ω - X v ω| ^ p ∂P ≤ M * dist u v ^ q) →
          Integrable (fun ω => |X a ω| ^ p) P →
          (∫ ω, |X a ω| ^ p ∂P ≤ M) →
          (∀ ω, ContinuousOn (fun u => X u ω) (Set.Icc a b)) →
          ∀ L : ℝ, 0 < L →
            P {ω | ∃ u ∈ Set.Icc a b, L < |X u ω|} ≤ ENNReal.ofReal ((B / L) ^ p) := by
  classical
  obtain ⟨B, hB⟩ := LatticeProb.kolmogorovBoundPi k a b p q M hp hq (1/2) (by norm_num)
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro Ω _ P hP X hmeas hint hbound hinta hinta' hcont L hL
  set B' : ℝ := max B 1 with hB'def
  have hB'1 : (1:ℝ) ≤ B' := le_max_right _ _
  have hB'0 : (0:ℝ) < B' := lt_of_lt_of_le one_pos hB'1
  have hBB' : B ≤ B' := le_max_left _ _
  set E : Set Ω := {ω | ∃ u ∈ Set.Icc a b, L < |X u ω|} with hEdef
  have hEm : MeasurableSet E := measurableSet_exists_lt_abs hab X hmeas hcont L
  rcases eq_or_ne (P E) 0 with h0 | h0
  · rw [h0]; exact bot_le
  have hfin : P E ≠ ⊤ := measure_ne_top P E
  set α : ℝ := (P E).toReal with hαdef
  have hα0 : 0 < α := ENNReal.toReal_pos h0 hfin
  have hPE : P E = ENNReal.ofReal α := (ENNReal.ofReal_toReal hfin).symm
  set c : ℝ := α ^ (1/p) with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos hα0 _
  have hcp : c ^ p = α := by
    rw [hcdef, ← Real.rpow_mul hα0.le, one_div, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  haveI hPc : IsProbabilityMeasure (P[|E]) := cond_isProbabilityMeasure h0
  have hcondle : P[|E] ≤ (P E)⁻¹ • P := by
    refine Measure.le_iff'.2 fun s => ?_
    show ((P E)⁻¹ • P.restrict E) s ≤ ((P E)⁻¹ • P) s
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.le_iff'.1 Measure.restrict_le_self s)
  have hinvne : (P E)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  have htoReal : ((P E)⁻¹).toReal = α⁻¹ := by rw [ENNReal.toReal_inv]
  have key : ∀ f : Ω → ℝ, Integrable f P → 0 ≤ f →
      Integrable f (P[|E]) ∧ ∫ ω, f ω ∂(P[|E]) ≤ α⁻¹ * ∫ ω, f ω ∂P := by
    intro f hf hf0
    have hsm : Integrable f ((P E)⁻¹ • P) := hf.smul_measure hinvne
    refine ⟨hsm.mono_measure hcondle, ?_⟩
    have h1 : ∫ ω, f ω ∂(P[|E]) ≤ ∫ ω, f ω ∂((P E)⁻¹ • P) :=
      integral_mono_measure hcondle (Filter.Eventually.of_forall hf0) hsm
    rwa [integral_smul_measure, htoReal, smul_eq_mul] at h1
  refine le_trans (le_of_eq hPE) (ENNReal.ofReal_le_ofReal ?_)
  have hcL : c * L ≤ B' := by
    by_contra hcon0
    have hcon : B' < c * L := not_le.mp hcon0
    set Y : (Fin k → ℝ) → Ω → ℝ := fun u ω => c * X u ω with hYdef
    have hYabs : ∀ (u v : Fin k → ℝ) (ω : Ω),
        |Y u ω - Y v ω| ^ p = c ^ p * |X u ω - X v ω| ^ p := by
      intro u v ω
      have : |Y u ω - Y v ω| = c * |X u ω - X v ω| := by
        rw [hYdef]; simp only [← mul_sub, abs_mul, abs_of_pos hc0]
      rw [this, Real.mul_rpow hc0.le (abs_nonneg _)]
    have hYanchor : ∀ ω : Ω, |Y a ω| ^ p = c ^ p * |X a ω| ^ p := by
      intro ω
      rw [hYdef]
      simp only [abs_mul, abs_of_pos hc0]
      rw [Real.mul_rpow hc0.le (abs_nonneg _)]
    have hYmeas : ∀ u, Measurable (Y u) := fun u => (hmeas u).const_mul c
    have hYint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
        Integrable (fun ω => |Y u ω - Y v ω| ^ p) (P[|E]) := by
      intro u hu v hv
      have h := (key (fun ω => |X u ω - X v ω| ^ p) (hint u hu v hv)
        (fun ω => Real.rpow_nonneg (abs_nonneg _) _)).1
      simpa only [hYabs] using h.const_mul (c ^ p)
    have hYbound : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
        ∫ ω, |Y u ω - Y v ω| ^ p ∂(P[|E]) ≤ M * dist u v ^ q := by
      intro u hu v hv
      have h := (key (fun ω => |X u ω - X v ω| ^ p) (hint u hu v hv)
        (fun ω => Real.rpow_nonneg (abs_nonneg _) _)).2
      have hc : ∫ ω, |Y u ω - Y v ω| ^ p ∂(P[|E])
          = c ^ p * ∫ ω, |X u ω - X v ω| ^ p ∂(P[|E]) := by
        simp only [hYabs, integral_const_mul]
      rw [hc, hcp]
      calc α * ∫ ω, |X u ω - X v ω| ^ p ∂(P[|E])
          ≤ α * (α⁻¹ * ∫ ω, |X u ω - X v ω| ^ p ∂P) := by
            exact mul_le_mul_of_nonneg_left h hα0.le
        _ = ∫ ω, |X u ω - X v ω| ^ p ∂P := by
            rw [← mul_assoc, mul_inv_cancel₀ hα0.ne', one_mul]
        _ ≤ M * dist u v ^ q := hbound u hu v hv
    have hYinta : Integrable (fun ω => |Y a ω| ^ p) (P[|E]) := by
      have h := (key (fun ω => |X a ω| ^ p) hinta
        (fun ω => Real.rpow_nonneg (abs_nonneg _) _)).1
      simpa only [hYanchor] using h.const_mul (c ^ p)
    have hYinta' : ∫ ω, |Y a ω| ^ p ∂(P[|E]) ≤ M := by
      have h := (key (fun ω => |X a ω| ^ p) hinta
        (fun ω => Real.rpow_nonneg (abs_nonneg _) _)).2
      have hc : ∫ ω, |Y a ω| ^ p ∂(P[|E]) = c ^ p * ∫ ω, |X a ω| ^ p ∂(P[|E]) := by
        simp only [hYanchor, integral_const_mul]
      rw [hc, hcp]
      calc α * ∫ ω, |X a ω| ^ p ∂(P[|E])
          ≤ α * (α⁻¹ * ∫ ω, |X a ω| ^ p ∂P) := mul_le_mul_of_nonneg_left h hα0.le
        _ = ∫ ω, |X a ω| ^ p ∂P := by rw [← mul_assoc, mul_inv_cancel₀ hα0.ne', one_mul]
        _ ≤ M := hinta'
    have hYcont : ∀ ω, ContinuousOn (fun u => Y u ω) (Set.Icc a b) := fun ω =>
      continuousOn_const.mul (hcont ω)
    have hfinal := hB (P[|E]) hPc Y hYmeas hYint hYbound hYinta hYinta' hYcont
    have hsub : E ⊆ {ω | ∃ u ∈ Set.Icc a b, B < |Y u ω|} := by
      rintro ω ⟨u, hu, hlt⟩
      refine ⟨u, hu, ?_⟩
      have : |Y u ω| = c * |X u ω| := by rw [hYdef]; simp [abs_mul, abs_of_pos hc0]
      rw [this]
      have : c * L < c * |X u ω| := by exact mul_lt_mul_of_pos_left hlt hc0
      linarith
    have hone : P[|E] E = 1 := by
      rw [cond_apply hEm P E, Set.inter_self, ENNReal.inv_mul_cancel h0 hfin]
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1/2) :=
      le_trans (le_of_eq hone.symm) (le_trans (measure_mono hsub) hfinal)
    rw [show ENNReal.ofReal (1/2 : ℝ) = (1/2 : ℝ≥0∞) by
      rw [ENNReal.ofReal_div_of_pos] <;> norm_num] at this
    norm_num at this
  have hcle : c ≤ B' / L := by rw [le_div_iff₀ hL]; exact hcL
  calc α = c ^ p := hcp.symm
    _ ≤ (B' / L) ^ p := Real.rpow_le_rpow hc0.le hcle hp.le

end Sandpile.Support
