/-
Step 2 of `lem:dgt4-path-survival` (`sandpile.tex:5529-5583`), up to the product over the
last visits.

The paper's Step 2 runs
`\P(S_{n_R,j}(X)=1\mid X)=\prod_{r=0}^j(1-\pi_{R,r})^{I_{r,j}(X)}+o_R(1)`
(`eq:dgt4-path-product-limit`) through two estimates: the threshold replacement
`eq:dgt4-path-contact-replacement`, which exchanges each contact event
`\{u_{n_R-r}(X_r)=0\}` for its threshold event `\{J(X_r)>\E u_{n_R-r-1}(0)\}`, and the
factorization `eq:dgt4-path-threshold-factorization` of Step 1.  What is proved here is that
chain, with the factorization left as an explicit hypothesis, since it is proved separately in
each branch (`Support/LinStep1Factor.lean` in the Gaussian branch,
`Sandpile.centeredMassLaw_threshold_factorization` in the independent one).

* `abs_survival_sub_threshold_le` is `eq:dgt4-path-contact-replacement` with the paper's data:
  the abstract inequality `abs_measureReal_iInter_sub_le_harmonic` of
  `Support/LinHarmonicWindow.lean` fed the survival events, the threshold events, the identity
  of symmetric differences `symmDiff_survival_threshold`, and the translation invariance of the
  pair `(J,(u_m))` at `sandpile.tex:5453-5454`, which enters as the hypothesis `hshift` and is
  a theorem in both branches (`measure_threshold_symmDiff_shift`,
  `measure_threshold_symmDiff_shift_gauss`).
* `exists_lastVisit_enum` enumerates the last-visit times by an injective family of SITES,
  which is the shape Step 1 consumes, and `prod_rpow_lastVisitIndicator` identifies the
  paper's `\prod_{r=0}^j(1-\pi_{R,r})^{I_{r,j}(X)}` with the product over those times.
* `abs_survival_sub_prod_le` is the chain itself.

The error is the sum of the two: the harmonic error `\eta\sum_{r\leq j}1/(n-r)` of the
replacement and the factorization error `\theta`.
-/
import Sandpile.Support.LinHarmonicWindow
import Sandpile.Support.LinNested

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-! ### The threshold replacement with the paper's data -/

/-- `eq:dgt4-path-contact-replacement` with the paper's data. -/
theorem abs_survival_sub_threshold_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (X : ℕ → Site d) (eta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta) :
    |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
        - (centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j,
            J σ (X r) ≤ b r}|
      ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ := by
  rw [setOf_forall_le_eq_iInter j (fun r σ => 0 < odometer σ (n - r) (X r)),
    setOf_forall_le_eq_iInter j
      (fun r σ => J σ (X r) ≤ b r)]
  refine abs_measureReal_iInter_sub_le_harmonic (centeredMassLaw d ν) n j _ _ eta ?_ ?_
  · intro r hr
    rw [Finset.mem_range] at hr
    have hnr : 0 < n - r := by omega
    exact_mod_cast hnr
  · intro r hr
    rw [Finset.mem_range] at hr
    rw [symmDiff_survival_threshold (n - r) (X r)
      (b r) J]
    rw [measureReal_def,
      hshift (n - r) (b r) (X r), ← measureReal_def]
    exact hthr r (by omega)

/-! ### The last visits -/

theorem lastVisitIndicator_eq_one_of_mem {j r : ℕ} (X : ℕ → Site d)
    (h : r ∈ lastVisitTimes j X) :
    Frozen.DGT4LastVisits.lastVisitIndicator r j X = 1 := by
  classical
  rw [lastVisitTimes, Finset.mem_filter] at h
  rw [Frozen.DGT4LastVisits.lastVisitIndicator, Set.indicator_of_mem]
  intro s hs1 hs2
  exact (h.2 s (Finset.mem_Ioc.mpr ⟨hs1, hs2⟩)).symm

theorem lastVisitIndicator_eq_zero_of_notMem {j r : ℕ} (X : ℕ → Site d)
    (hr : r ∈ Finset.range (j + 1)) (h : r ∉ lastVisitTimes j X) :
    Frozen.DGT4LastVisits.lastVisitIndicator r j X = 0 := by
  classical
  rw [Frozen.DGT4LastVisits.lastVisitIndicator, Set.indicator_of_notMem]
  intro hc
  refine h ?_
  rw [lastVisitTimes, Finset.mem_filter]
  refine ⟨hr, fun s hs => ?_⟩
  rw [Finset.mem_Ioc] at hs
  exact (hc s hs.1 hs.2).symm

/-- The paper's `\prod_{r=0}^j(1-\pi_{R,r})^{I_{r,j}(X)}` is the product over the last-visit
times, `sandpile.tex:5547-5552`. -/
theorem prod_rpow_lastVisitIndicator (j : ℕ) (X : ℕ → Site d) (f : ℕ → ℝ) :
    ∏ r ∈ Finset.range (j + 1),
        (f r) ^ (Frozen.DGT4LastVisits.lastVisitIndicator r j X)
      = ∏ r ∈ lastVisitTimes j X, f r := by
  classical
  rw [lastVisitTimes, Finset.prod_filter]
  refine Finset.prod_congr rfl fun r hr => ?_
  by_cases h : r ∈ lastVisitTimes j X
  · rw [lastVisitIndicator_eq_one_of_mem X h, Real.rpow_one, if_pos]
    rw [lastVisitTimes, Finset.mem_filter] at h
    exact h.2
  · rw [lastVisitIndicator_eq_zero_of_notMem X hr h, Real.rpow_zero, if_neg]
    intro hc
    exact h (by rw [lastVisitTimes, Finset.mem_filter]; exact ⟨hr, hc⟩)

/-- The last-visit times enumerated by an injective family of sites, which is the form
Step 1 of `lem:dgt4-path-survival` consumes. -/
theorem exists_lastVisit_enum (j : ℕ) (X : ℕ → Site d) :
    ∃ (m : ℕ) (ts : Fin m → ℕ), Function.Injective (fun i => X (ts i)) ∧
      (m : ℝ) ≤ (j : ℝ) + 1 ∧
      (∀ Q : ℕ → Prop, (∀ i : Fin m, Q (ts i)) ↔ ∀ r ∈ lastVisitTimes j X, Q r) ∧
      ∀ g : ℕ → ℝ, ∏ i : Fin m, g (ts i) = ∏ r ∈ lastVisitTimes j X, g r := by
  classical
  set s : Finset ℕ := lastVisitTimes j X with hs
  refine ⟨s.card, fun i => ((s.equivFin.symm i : {x // x ∈ s}) : ℕ), ?_, ?_, ?_, ?_⟩
  · intro i i' hii
    have hmem : ∀ i : Fin s.card, ((s.equivFin.symm i : {x // x ∈ s}) : ℕ) ∈ s :=
      fun i => (s.equivFin.symm i).2
    have hinj := lastVisit_injOn j X
    have h1 : ((s.equivFin.symm i : {x // x ∈ s}) : ℕ)
        = ((s.equivFin.symm i' : {x // x ∈ s}) : ℕ) :=
      hinj _ (hmem i) _ (hmem i') hii
    have h2 : (s.equivFin.symm i : {x // x ∈ s}) = (s.equivFin.symm i' : {x // x ∈ s}) :=
      Subtype.ext h1
    exact s.equivFin.symm.injective h2
  · have hcard : s.card ≤ j + 1 := by
      rw [hs, lastVisitTimes]
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have : ((s.card : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  · intro Q
    constructor
    · intro h r hr
      have := h (s.equivFin ⟨r, hr⟩)
      simpa using this
    · intro h i
      exact h _ (s.equivFin.symm i).2
  · intro g
    rw [Equiv.prod_comp s.equivFin.symm (fun x : {x // x ∈ s} => g (x : ℕ)),
      Finset.prod_coe_sort s g]

/-! ### The product over the last visits -/

/-- **`eq:dgt4-path-product-limit`** (`sandpile.tex:5547-5553`): after the threshold
replacement and the factorization, the survival probability along `X` is the product of the
one-site threshold probabilities over the last visits. -/
theorem abs_survival_sub_prod_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ) (b : ℕ → ℝ) (hb : Antitone b)
    (hshift : ∀ (t : ℕ) (c : ℝ) (y : Site d),
      (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t y = 0} {σ : Site d → ℝ | c < J σ y})
        = (centeredMassLaw d ν)
          (symmDiff {σ : Site d → ℝ | odometer σ t 0 = 0} {σ : Site d → ℝ | c < J σ 0}))
    (n j : ℕ) (hj : j < n) (X : ℕ → Site d) (eta theta : ℝ)
    (hthr : ∀ r, r ≤ j → ((n - r : ℕ) : ℝ) * (centeredMassLaw d ν).real
        (symmDiff {σ : Site d → ℝ | odometer σ (n - r) 0 = 0}
          {σ : Site d → ℝ | b r < J σ 0}) ≤ eta)
    (hfact : ∀ (m : ℕ) (ts : Fin m → ℕ), Function.Injective (fun i => X (ts i)) →
      (m : ℝ) ≤ (j : ℝ) + 1 →
      |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
        ≤ theta) :
    |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
        - ∏ r ∈ Finset.range (j + 1),
            ((centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r}) ^
              (Frozen.DGT4LastVisits.lastVisitIndicator r j X)|
      ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta := by
  classical
  obtain ⟨m, ts, hinj, hmle, hQ, hprod⟩ := exists_lastVisit_enum j X
  have hset : {σ : Site d → ℝ | ∀ r ≤ j, J σ (X r) ≤ b r}
      = {σ : Site d → ℝ | ∀ i : Fin m, J σ (X (ts i)) ≤ b (ts i)} := by
    have h1 : {σ : Site d → ℝ | ∀ r ≤ j, J σ (X r) ≤ b r}
        = ⋂ r ∈ Finset.range (j + 1), {σ : Site d → ℝ | J σ (X r) ≤ b r} :=
      setOf_forall_le_eq_iInter j (fun r σ => J σ (X r) ≤ b r)
    rw [h1, iInter_lastVisit_eq j X b hb J]
    ext σ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact (hQ (fun r => J σ (X r) ≤ b r)).symm
  have hprodeq : ∏ i : Fin m,
      (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}
      = ∏ r ∈ Finset.range (j + 1),
        ((centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r}) ^
          (Frozen.DGT4LastVisits.lastVisitIndicator r j X) := by
    rw [prod_rpow_lastVisitIndicator j X
      (fun r => (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r})]
    exact hprod (fun r => (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b r})
  have h1 := abs_survival_sub_threshold_le ν J b hshift n j hj X eta hthr
  have h2 := hfact m ts hinj hmle
  rw [← hset] at h2
  rw [← hprodeq]
  calc |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
        - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}|
      ≤ |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, 0 < odometer σ (n - r) (X r)}
          - (centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, J σ (X r) ≤ b r}|
        + |(centeredMassLaw d ν).real {σ : Site d → ℝ | ∀ r ≤ j, J σ (X r) ≤ b r}
          - ∏ i : Fin m, (centeredMassLaw d ν).real {σ : Site d → ℝ | J σ 0 ≤ b (ts i)}| :=
        abs_sub_le _ _ _
    _ ≤ eta * ∑ r ∈ Finset.range (j + 1), (((n - r : ℕ) : ℝ))⁻¹ + theta := by
        exact add_le_add h1 h2

end Sandpile
