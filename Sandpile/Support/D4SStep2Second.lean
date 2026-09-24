/-
The second display of Step 2 of `prop:d4-superdiffusive-limit`
(`sandpile.tex:3374-3382`):
`E‖(C_R^{(R)})^ω‖²_{H^{-s}(D)} ≤ C_{D,s}(1+\log\log t_R)R^{-2\min\{s,1\}}`,
where `C_R` is constant on each parity class of the lattice.

The `ω`-shift has total mass zero, so a field constant on each parity class
pairs against the cell masses through the difference of the two constants and
the mass of ONE class alone (`sum_parity_const_mul`).  That mass is the integral
of the shifted test function against the even-cell indicator, and the parity of
`⌊Rz⌋` flips under the step `e_{i}/R`, so the integral is half the `L¹` modulus
of continuity of the shifted test function at scale `1/R`
(`abs_integral_mul_parityChar_le`).  Cauchy-Schwarz on a ball containing the
support turns that into the `L²` modulus, which is `‖h‖^{\min\{s,1\}}` for the
test function and `‖h‖` for the fixed density.
-/
import Sandpile.Support.D4SOmegaModulus
import Sandpile.Support.D4SModulus
import Sandpile.Support.D4SParity
import Sandpile.Support.D4SmoothL2
import Sandpile.Support.D4SNegSobolev

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support
open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- For a base at most one and an exponent `2σ` below two, the square is the
smaller power. -/
theorem rpow_sq_le_rpow_two_mul {r σ : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) : r ^ 2 ≤ r ^ (2 * σ) := by
  rcases eq_or_lt_of_le hr0 with h0 | h0
  · rw [← h0, Real.zero_rpow (by positivity)]
    norm_num
  · have hcast : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
    have hrw0 : r ^ (((2:ℕ)) : ℝ) = r ^ (2:ℕ) := Real.rpow_natCast r 2
    have hrw : r ^ (2:ℕ) = r ^ (2:ℝ) := by rw [← hrw0, hcast]
    rw [hrw]
    exact Real.rpow_le_rpow_of_exponent_ge h0 hr1 (by nlinarith)

/-- The square root of `r^{2σ}` is `r^σ`. -/
theorem sqrt_rpow_two_mul {r σ : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (r ^ (2 * σ)) = r ^ σ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr]
  congr 1
  ring

theorem norm_meshStep (R : ℝ) (i₀ : Fin d) : ‖meshStep d R i₀‖ = |R⁻¹| := by
  rw [meshStep, PiLp.norm_single, Real.norm_eq_abs]

theorem parityChar_eq_embed (R : ℝ) (z : Space d)
    [DecidablePred fun x : Sandpile.Site d => Sandpile.External.SameParity x 0] :
    parityChar R z =
      Sandpile.Continuum.embed R
        (fun x : Sandpile.Site d => if Sandpile.External.SameParity x 0 then (1:ℝ) else 0) z := by
  simp [parityChar, Sandpile.Continuum.embed, Sandpile.External.SameParity]

/-- **The even-cell mass is the pairing against the parity indicator.** -/
theorem sum_filter_cellMass_eq (R : ℝ) (ψ : Space d → ℝ) (hψ : Integrable ψ)
    (s : Finset (Sandpile.Site d))
    [DecidablePred fun x : Sandpile.Site d => Sandpile.External.SameParity x 0]
    (hs : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    ∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), cellMass R ψ x =
      ∫ z : Space d, ψ z * parityChar R z := by
  set f : Sandpile.Site d → ℝ :=
    fun x => if Sandpile.External.SameParity x 0 then (1:ℝ) else 0 with hf
  have hsum := latticePairing_eq_sum R f ψ hψ s hs
  have hfsum : ∑ x ∈ s, f x * cellMass R ψ x =
      ∑ x ∈ s.filter (fun x => Sandpile.External.SameParity x 0), cellMass R ψ x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Sandpile.External.SameParity x 0
    · simp [hf, hx]
    · simp [hf, hx]
  have hpair : latticePairing R f ψ = ∫ z : Space d, ψ z * parityChar R z := by
    show ∫ z : Space d, Sandpile.Continuum.embed R f z * ψ z =
      ∫ z : Space d, ψ z * parityChar R z
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Sandpile.Continuum.embed R f z * ψ z = ψ z * parityChar R z
    rw [parityChar_eq_embed R z, hf, mul_comm]
  rw [← hfsum, ← hpair, hsum]

/-- The total cell mass of an integrable function supported inside the mesh is
its integral. -/
theorem sum_cellMass_eq (R : ℝ) (ψ : Space d → ℝ) (hψ : Integrable ψ)
    (s : Finset (Sandpile.Site d))
    (hs : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    ∑ x ∈ s, cellMass R ψ x = ∫ z : Space d, ψ z := by
  have hsum := latticePairing_eq_sum R (fun _ => (1:ℝ)) ψ hψ s hs
  have hembed : ∀ z : Space d, Sandpile.Continuum.embed R (fun _ => (1:ℝ)) z = 1 :=
    fun _ => rfl
  have hpair : latticePairing R (fun _ => (1:ℝ)) ψ = ∫ z : Space d, ψ z := by
    unfold Sandpile.Continuum.latticePairing
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Sandpile.Continuum.embed R (fun _ => (1:ℝ)) z * ψ z = ψ z
    rw [hembed z, one_mul]
  rw [← hpair, hsum]
  exact Finset.sum_congr rfl fun x _ => (one_mul _).symm

/-- **The `L²` modulus of continuity of the `ω`-shift on the `H^s` unit ball.**
The shift splits into the test function, whose modulus is `4‖h‖^{2\min\{s,1\}}`
by Plancherel, and the fixed density, whose modulus is `C_ω‖h‖^2` by the mean
value inequality; for `‖h‖\leq1` the second is below the first. -/
theorem exists_integral_sq_sub_translate_omegaShift_le {s : ℝ} (hs : 0 < s)
    {D : Set (Space d)} (hD : IsDomain D) {w : Space d → ℝ} (hw : IsAveragingDensity D w) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
      ∀ h : Space d, ‖h‖ ≤ 1 →
        ∫ z : Space d, (omegaShift D w φ z - omegaShift D w φ (z + h)) ^ 2
          ≤ Cw * ‖h‖ ^ (2 * min s 1) := by
  classical
  obtain ⟨hwt, hwnn, hw1⟩ := hw
  obtain ⟨Cw0, hCw0, hCw⟩ := exists_integral_sq_sub_translate_testFn hwt
  set VD : ℝ := (volume D).toReal with hVD
  have hVDnn : (0:ℝ) ≤ VD := by rw [hVD]; exact ENNReal.toReal_nonneg
  have hDne : volume D ≠ ⊤ := (hD.2.1.measure_lt_top).ne
  refine ⟨8 + 2 * VD * Cw0, by positivity, ?_⟩
  intro φ hφ hnorm h hh1
  obtain ⟨hφsm, hφcs, hφsupp⟩ := hφ
  obtain ⟨hwsm, hwcs, hwsupp⟩ := hwt
  set c : ℝ := ∫ y in D, φ y with hc
  -- the two moduli
  have hmodφ : ∫ z : Space d, (φ z - φ (z + h)) ^ 2 ≤ 4 * ‖h‖ ^ (2 * min s 1) :=
    integral_sq_sub_translate_le d s hs φ hφsm hφcs hnorm h
  have hmodw : ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤ Cw0 * ‖h‖ ^ 2 := hCw h
  -- `‖h‖² ≤ ‖h‖^{2σ}`
  have hσ0 : 0 < min s 1 := lt_min hs zero_lt_one
  have hσ1 : min s 1 ≤ 1 := min_le_right _ _
  have hpow : ‖h‖ ^ 2 ≤ ‖h‖ ^ (2 * min s 1) := by
    rcases eq_or_lt_of_le (norm_nonneg h) with h0 | h0
    · have hz : ‖h‖ = 0 := h0.symm
      rw [hz]
      rw [Real.zero_rpow (by positivity)]
      norm_num
    · have hrw : ‖h‖ ^ (2:ℕ) = ‖h‖ ^ (2:ℝ) := by
        rw [← Real.rpow_natCast ‖h‖ 2]; norm_num
      rw [hrw]
      exact Real.rpow_le_rpow_of_exponent_ge h0 hh1 (by nlinarith)
  -- integrability
  have hφint2 : Integrable (fun z : Space d => (φ z - φ (z + h)) ^ 2) := by
    have hsmT : Continuous (fun z : Space d => φ z - φ (z + h)) :=
      hφsm.continuous.sub (hφsm.continuous.comp (continuous_id.add continuous_const))
    have hcsT : HasCompactSupport (fun z : Space d => φ z - φ (z + h)) :=
      hφcs.sub (hφcs.comp_homeomorph (Homeomorph.addRight h))
    have hsq : Continuous (fun z : Space d => (φ z - φ (z + h)) ^ 2) := hsmT.pow 2
    have hksq : HasCompactSupport (fun z : Space d => (φ z - φ (z + h)) ^ 2) :=
      hcsT.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact hsq.integrable_of_hasCompactSupport hksq
  have hwint2 : Integrable (fun z : Space d => (w z - w (z + h)) ^ 2) := by
    have hsmT : Continuous (fun z : Space d => w z - w (z + h)) :=
      hwsm.continuous.sub (hwsm.continuous.comp (continuous_id.add continuous_const))
    have hcsT : HasCompactSupport (fun z : Space d => w z - w (z + h)) :=
      hwcs.sub (hwcs.comp_homeomorph (Homeomorph.addRight h))
    have hsq : Continuous (fun z : Space d => (w z - w (z + h)) ^ 2) := hsmT.pow 2
    have hksq : HasCompactSupport (fun z : Space d => (w z - w (z + h)) ^ 2) :=
      hcsT.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact hsq.integrable_of_hasCompactSupport hksq
  have hlhsint : Integrable
      (fun z : Space d => (omegaShift D w φ z - omegaShift D w φ (z + h)) ^ 2) := by
    have hsm : Continuous (omegaShift D w φ) :=
      hφsm.continuous.sub (hwsm.continuous.mul continuous_const)
    have hcs : HasCompactSupport (omegaShift D w φ) := hφcs.sub (hwcs.mul_right)
    have hsmT : Continuous (fun z : Space d => omegaShift D w φ z - omegaShift D w φ (z + h)) :=
      hsm.sub (hsm.comp (continuous_id.add continuous_const))
    have hcsT : HasCompactSupport
        (fun z : Space d => omegaShift D w φ z - omegaShift D w φ (z + h)) :=
      hcs.sub (hcs.comp_homeomorph (Homeomorph.addRight h))
    have hsq : Continuous
        (fun z : Space d => (omegaShift D w φ z - omegaShift D w φ (z + h)) ^ 2) := hsmT.pow 2
    have hksq : HasCompactSupport
        (fun z : Space d => (omegaShift D w φ z - omegaShift D w φ (z + h)) ^ 2) :=
      hcsT.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact hsq.integrable_of_hasCompactSupport hksq
  -- the pointwise split
  have hptw : ∀ z : Space d,
      (omegaShift D w φ z - omegaShift D w φ (z + h)) ^ 2 ≤
        2 * (φ z - φ (z + h)) ^ 2 + 2 * c ^ 2 * (w z - w (z + h)) ^ 2 := by
    intro z
    have he : omegaShift D w φ z - omegaShift D w φ (z + h)
        = (φ z - φ (z + h)) - c * (w z - w (z + h)) := by
      show (φ z - w z * c) - (φ (z + h) - w (z + h) * c) = _
      ring
    rw [he]
    nlinarith [sq_nonneg ((φ z - φ (z + h)) + c * (w z - w (z + h))), sq_nonneg c,
      sq_nonneg (w z - w (z + h))]
  have hmaj : Integrable (fun z : Space d =>
      2 * (φ z - φ (z + h)) ^ 2 + 2 * c ^ 2 * (w z - w (z + h)) ^ 2) :=
    (hφint2.const_mul 2).add (hwint2.const_mul _)
  have hmono := integral_mono hlhsint hmaj hptw
  rw [integral_add (hφint2.const_mul 2) (hwint2.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  -- the bound on `c²`
  have hφint : Integrable φ := hφsm.continuous.integrable_of_hasCompactSupport hφcs
  have hφsq : Integrable (fun z : Space d => φ z ^ 2) := by
    have hsq : Continuous (fun z : Space d => φ z ^ 2) := hφsm.continuous.pow 2
    have hksq : HasCompactSupport (fun z : Space d => φ z ^ 2) :=
      hφcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact hsq.integrable_of_hasCompactSupport hksq
  have hc2 : c ^ 2 ≤ VD := by
    have hφ2 : ∫ z : Space d, φ z ^ 2 ≤ 1 :=
      integral_sq_le_one_of_sobolevNormSq_le d s hs.le φ hφsm hφcs hnorm
    have hcs' := sq_setIntegral_le D φ hφint.integrableOn hφsq.integrableOn hDne
    have h2 : ∫ z in D, φ z ^ 2 ≤ ∫ z, φ z ^ 2 :=
      setIntegral_le_integral hφsq (Filter.Eventually.of_forall fun z => sq_nonneg _)
    calc c ^ 2 ≤ VD * ∫ z in D, φ z ^ 2 := hcs'
      _ ≤ VD * 1 := mul_le_mul_of_nonneg_left (le_trans h2 hφ2) hVDnn
      _ = VD := mul_one _
  have hwnn2 : (0:ℝ) ≤ ∫ z : Space d, (w z - w (z + h)) ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hstep : 2 * c ^ 2 * ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤
      2 * VD * (Cw0 * ‖h‖ ^ (2 * min s 1)) := by
    have hA : 2 * c ^ 2 * ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤
        2 * VD * ∫ z : Space d, (w z - w (z + h)) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) hwnn2
    have hB : 2 * VD * ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤
        2 * VD * (Cw0 * ‖h‖ ^ (2 * min s 1)) := by
      have : ∫ z : Space d, (w z - w (z + h)) ^ 2 ≤ Cw0 * ‖h‖ ^ (2 * min s 1) := by
        refine le_trans hmodw ?_
        exact mul_le_mul_of_nonneg_left hpow hCw0
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hpownn : (0:ℝ) ≤ ‖h‖ ^ (2 * min s 1) := Real.rpow_nonneg (norm_nonneg h) _
  nlinarith [hmono, hstep, hmodφ]

/-- **The second display of Step 2 of `prop:d4-superdiffusive-limit`**
(`sandpile.tex:3379-3381`).  A lattice field constant on each parity class has
`ω`-representative of `H^{-s}(D)` norm at most `K|c_0-c_1|R^{-\min\{s,1\}}`.
The total mass of the `ω`-shift is zero, so only the imbalance between the two
parity classes of the mesh survives; the parity flips under one mesh step, so
that imbalance is the modulus of continuity of the shifted test function at
scale `1/R`. -/
theorem exists_negSobolevNorm_parityConst_le {s : ℝ} (hs : 0 < s)
    {D : Set (Space d)} (hD : IsDomain D) {w : Space d → ℝ} (hw : IsAveragingDensity D w)
    (i₀ : Fin d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ (C : Sandpile.Site d → ℝ) (c₀ c₁ : ℝ),
      (∀ x : Sandpile.Site d, Sandpile.External.SameParity x 0 → C x = c₀) →
      (∀ x : Sandpile.Site d, ¬ Sandpile.External.SameParity x 0 → C x = c₁) →
      negSobolevNorm d s D (omegaRep D w (latticePairing R C)) ≤
        ENNReal.ofReal (K * |c₀ - c₁| * (R⁻¹) ^ (min s 1)) := by
  classical
  obtain ⟨Cw, hCw0, hCw⟩ := exists_integral_sq_sub_translate_omegaShift_le hs hD hw
  obtain ⟨r, hr⟩ := hD.2.1.subset_closedBall (0 : Space d)
  set Lb : ℝ := max r 0 with hLb
  have hLb0 : (0:ℝ) ≤ Lb := le_max_right _ _
  have hLbd : ∀ z ∈ D, ‖z‖ ≤ Lb := by
    intro z hz
    have := hr hz
    rw [mem_closedBall_zero_iff] at this
    exact le_trans this (le_max_left _ _)
  set A : Set (Space d) := Metric.closedBall (0 : Space d) (Lb + 1) with hA
  have hAvol : volume A ≠ ⊤ := (isCompact_closedBall (0 : Space d) (Lb + 1)).measure_lt_top.ne
  refine ⟨(1/2) * Real.sqrt ((volume A).toReal) * Real.sqrt Cw, by positivity, ?_⟩
  intro R hR C c₀ c₁ hC₀ hC₁
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set h : Space d := meshStep d R i₀ with hh
  have hnh : ‖h‖ = R⁻¹ := by
    rw [hh, norm_meshStep, abs_of_pos (by positivity)]
  have hnh1 : ‖h‖ ≤ 1 := by
    rw [hnh]
    exact inv_le_one_of_one_le₀ hR
  have hσ0 : 0 < min s 1 := lt_min hs zero_lt_one
  refine sSup_le ?_
  rintro v ⟨φ, hφ, hnorm, rfl⟩
  have hφt := hφ
  obtain ⟨hφsm, hφcs, hφsupp⟩ := hφ
  obtain ⟨hwt, hwnn, hw1⟩ := hw
  obtain ⟨hwsm, hwcs, hwsupp⟩ := hwt
  set ψ : Space d → ℝ := omegaShift D w φ with hψ
  have hψsm : Continuous ψ := hφsm.continuous.sub (hwsm.continuous.mul continuous_const)
  have hψcs : HasCompactSupport ψ := hφcs.sub (hwcs.mul_right)
  have hψint : Integrable ψ := hψsm.integrable_of_hasCompactSupport hψcs
  have hψmean : ∫ z : Space d, ψ z = 0 :=
    integral_omegaShift_eq_zero ⟨⟨hwsm, hwcs, hwsupp⟩, hwnn, hw1⟩ hφt
  -- the support of the shifted test function
  have hψsupp : ∀ z : Space d, ψ z ≠ 0 → ‖z‖ ≤ Lb := by
    intro z hz
    by_cases hφz : φ z = 0
    · have hwz : w z ≠ 0 := by
        intro hwz
        exact hz (by show φ z - w z * _ = 0; rw [hφz, hwz]; ring)
      exact hLbd z (hwsupp (subset_tsupport _ hwz))
    · exact hLbd z (hφsupp (subset_tsupport _ hφz))
  set S : Finset (Sandpile.Site d) :=
    Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * Lb⌉₊ + 1) with hS
  have hmem : ∀ z : Space d, ψ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ S :=
    fun z hz => floor_mem_boxFinset R z (hψsupp z hz)
  -- the pairing as a parity imbalance
  have hpairsum := latticePairing_eq_sum R C ψ hψint S hmem
  have hmass : ∑ x ∈ S, cellMass R ψ x = 0 := by
    rw [sum_cellMass_eq R ψ hψint S hmem, hψmean]
  have hparity := sum_parity_const_mul S C (cellMass R ψ) c₀ c₁ hC₀ hC₁ hmass
  have hfilter := sum_filter_cellMass_eq R ψ hψint S hmem
  have hrep : omegaRep D w (latticePairing R C) φ = latticePairing R C ψ := rfl
  -- the imbalance is a modulus of continuity
  have himb := abs_integral_mul_parityChar_le (d := d) hR0 i₀ ψ hψint hψmean
  -- the `L¹` modulus through Cauchy-Schwarz on a ball containing the support
  have hdsm : Continuous (fun z : Space d => ψ z - ψ (z + h)) :=
    hψsm.sub (hψsm.comp (continuous_id.add continuous_const))
  have hdcs : HasCompactSupport (fun z : Space d => ψ z - ψ (z + h)) :=
    hψcs.sub (hψcs.comp_homeomorph (Homeomorph.addRight h))
  have hdint : Integrable (fun z : Space d => ψ z - ψ (z + h)) :=
    hdsm.integrable_of_hasCompactSupport hdcs
  have hdsq : Continuous (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) := hdsm.pow 2
  have hdksq : HasCompactSupport (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) :=
    hdcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hdint2 : Integrable (fun z : Space d => (ψ z - ψ (z + h)) ^ 2) :=
    hdsq.integrable_of_hasCompactSupport hdksq
  have hdsuppA : ∀ z : Space d, ψ z - ψ (z + h) ≠ 0 → z ∈ A := by
    intro z hz
    rw [hA, mem_closedBall_zero_iff]
    by_cases h1 : ψ z = 0
    · have h2 : ψ (z + h) ≠ 0 := by intro hc; exact hz (by rw [h1, hc]; ring)
      have h3 : ‖z + h‖ ≤ Lb := hψsupp _ h2
      have h4 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by
        have := norm_sub_le (z + h) h
        simpa using this
      linarith [hnh1]
    · linarith [hψsupp z h1]
  have hL1 := integral_abs_le_sqrt_measure_mul A (fun z : Space d => ψ z - ψ (z + h))
    hdint hdint2 hAvol hdsuppA
  have hL2 : ∫ z : Space d, (ψ z - ψ (z + h)) ^ 2 ≤ Cw * ‖h‖ ^ (2 * min s 1) :=
    hCw φ hφt hnorm h hnh1
  have hsqrtle : Real.sqrt (∫ z : Space d, (ψ z - ψ (z + h)) ^ 2) ≤
      Real.sqrt Cw * (R⁻¹) ^ (min s 1) := by
    have h1 : Real.sqrt (∫ z : Space d, (ψ z - ψ (z + h)) ^ 2) ≤
        Real.sqrt (Cw * ‖h‖ ^ (2 * min s 1)) := Real.sqrt_le_sqrt hL2
    have h2 : Real.sqrt (Cw * ‖h‖ ^ (2 * min s 1)) =
        Real.sqrt Cw * (R⁻¹) ^ (min s 1) := by
      rw [Real.sqrt_mul hCw0, sqrt_rpow_two_mul (norm_nonneg h), hnh]
    rw [← h2]; exact h1
  -- assemble
  have habs : |latticePairing R C ψ| ≤
      (1/2) * Real.sqrt ((volume A).toReal) * Real.sqrt Cw * |c₀ - c₁| * (R⁻¹) ^ (min s 1) := by
    rw [hpairsum, hparity, hfilter, abs_mul]
    have hb : |∫ z : Space d, ψ z * parityChar R z| ≤
        (1/2) * (Real.sqrt ((volume A).toReal) * (Real.sqrt Cw * (R⁻¹) ^ (min s 1))) := by
      refine le_trans himb ?_
      have hstep : ∫ z : Space d, |ψ z - ψ (z + h)| ≤
          Real.sqrt ((volume A).toReal) * (Real.sqrt Cw * (R⁻¹) ^ (min s 1)) := by
        refine le_trans hL1 ?_
        exact mul_le_mul_of_nonneg_left hsqrtle (Real.sqrt_nonneg _)
      linarith
    calc |c₀ - c₁| * |∫ z : Space d, ψ z * parityChar R z|
        ≤ |c₀ - c₁| * ((1/2) * (Real.sqrt ((volume A).toReal) *
            (Real.sqrt Cw * (R⁻¹) ^ (min s 1)))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = (1/2) * Real.sqrt ((volume A).toReal) * Real.sqrt Cw * |c₀ - c₁| *
            (R⁻¹) ^ (min s 1) := by ring
  rw [hrep]
  exact ENNReal.ofReal_le_ofReal (by linarith [habs])

end Sandpile.Support
