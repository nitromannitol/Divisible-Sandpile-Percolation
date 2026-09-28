import Sandpile.Support.Dgt4ALinTight
import Sandpile.Support.LinJacobianFirstConjunct
import Sandpile.Support.LinMeasureZero
import Sandpile.Support.Dgt4ANegSobolevBridge
import Sandpile.External.RellichKondrachovNegSobolev
import LatticeProb.Analysis.Sobolev.DualNet

/-!
# Upgrading a tested `L²` estimate to convergence in the negative Sobolev norm

Convergence in probability to zero of a tested `L²` estimate against a fixed test function
upgrades to convergence in probability of the whole `H^{-s}(D)` dual norm, provided the family
is additionally tight in the weaker norm `H^{-s₀}(D)` for some `s₀ < s`. The mechanism is the
classical Rellich-Kondrachov compactness of the unit ball of `H^s(D)` in `H^{-s₀}(D)`
(`Sandpile.External.RellichKondrachovNegSobolev`): a functional bounded in the `H^{-s₀}(D)`
dual norm is controlled, in the `H^{-s}(D)` dual norm, by its values on a fixed finite net of
test functions, so the whole norm converges to zero once each of those finitely many pairings
does. This file assembles that upgrade and applies it to the odometer's fluctuation field
arising in the linearization lemma.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {d : ℕ}

/-- **The dual norm of a functional is exactly rescaled by a positive
constant.**  Two applications of `negSobolevNorm_smul_le` give the reverse
inequality as well. -/
theorem negSobolevNorm_const_mul {s : ℝ} {D : Set (Sandpile.Continuum.Space d)}
    (F : (Sandpile.Continuum.Space d → ℝ) → ℝ) {c : ℝ} (hc : 0 < c) :
    Sandpile.Continuum.negSobolevNorm d s D (fun φ => c * F φ)
      = ENNReal.ofReal c * Sandpile.Continuum.negSobolevNorm d s D F := by
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [negSobolevNorm_eq_latticeProb, negSobolevNorm_eq_latticeProb]
  apply le_antisymm
  · have h := LatticeProb.Sobolev.negSobolevNorm_smul_le s D c F
    rwa [abs_of_pos hc] at h
  · have h := LatticeProb.Sobolev.negSobolevNorm_smul_le s D c⁻¹ (fun φ => c * F φ)
    have hcancel : (fun φ => c⁻¹ * (c * F φ)) = F := by
      funext φ; field_simp
    rw [hcancel, abs_of_pos (inv_pos.mpr hc)] at h
    have h2 : ENNReal.ofReal c * LatticeProb.Sobolev.negSobolevNorm d s D F
        ≤ ENNReal.ofReal c * (ENNReal.ofReal c⁻¹ *
          LatticeProb.Sobolev.negSobolevNorm d s D (fun φ => c * F φ)) :=
      mul_le_mul_right h _
    rwa [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hcne, ENNReal.ofReal_one,
      one_mul] at h2

/-- **The dual norm only reads a functional's values at test functions of `D`.**
Two functionals agreeing there have the same `H^{-s}(D)` dual norm. -/
theorem negSobolevNorm_congr {s : ℝ} {D : Set (Sandpile.Continuum.Space d)}
    {F1 F2 : (Sandpile.Continuum.Space d → ℝ) → ℝ}
    (h : ∀ φ, Sandpile.Continuum.IsTestFn D φ → F1 φ = F2 φ) :
    Sandpile.Continuum.negSobolevNorm d s D F1 = Sandpile.Continuum.negSobolevNorm d s D F2 := by
  unfold Sandpile.Continuum.negSobolevNorm
  congr 1
  ext v
  constructor
  · rintro ⟨φ, hφ, hn, rfl⟩; exact ⟨φ, hφ, hn, by rw [h φ hφ]⟩
  · rintro ⟨φ, hφ, hn, rfl⟩; exact ⟨φ, hφ, hn, by rw [h φ hφ]⟩

/-- **The finite-net Rellich-Kondrachov upgrade, restricted to a subtraction on
test functions.**  Transposed from the shared library's
`negSobolevNorm_le_sup_add`, with the hypothesis that `F` is additive
weakened to `F` being SUBTRACTIVE on test functions (`hsub`): the pairing
`Sandpile.Continuum.latticePairing` is not additive on arbitrary (possibly
non-integrable) functions, only on the difference of two test functions
(`latticePairing_sub_testFn`), while it IS homogeneous on arbitrary functions
(`MeasureTheory.integral_const_mul` needs no integrability), so `hsmul` stays
unrestricted.  The library's own proof only ever invokes its `hadd` at a test
function and a scalar multiple of a test function, i.e. exactly the shape
`hsub` supplies. -/
theorem negSobolevNorm_le_sup_add_sub {D : Set (LatticeProb.Sobolev.Space d)} {s₀ s : ℝ}
    (_h : s₀ < s) (η : ℝ) (hη : 0 < η) (N : ℕ) (ψ : Fin N → LatticeProb.Sobolev.Space d → ℝ)
    (hψt : ∀ i, LatticeProb.Sobolev.IsTestFn D (ψ i))
    (hnet : ∀ φ : LatticeProb.Sobolev.Space d → ℝ, LatticeProb.Sobolev.IsTestFn D φ →
      LatticeProb.Sobolev.sobolevNormSq d s φ ≤ 1 →
      ∃ i, LatticeProb.Sobolev.sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal (η ^ 2))
    (F : (LatticeProb.Sobolev.Space d → ℝ) → ℝ)
    (hsub : ∀ φ ψ' : LatticeProb.Sobolev.Space d → ℝ, LatticeProb.Sobolev.IsTestFn D φ →
      LatticeProb.Sobolev.IsTestFn D ψ' → F (fun x => φ x - ψ' x) = F φ - F ψ')
    (hsmul : ∀ (c : ℝ) (φ : LatticeProb.Sobolev.Space d → ℝ), F (fun x => c * φ x) = c * F φ)
    (hF : LatticeProb.Sobolev.negSobolevNorm d s₀ D F ≤ 1) :
    LatticeProb.Sobolev.negSobolevNorm d s D F
      ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := by
  unfold LatticeProb.Sobolev.negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hn
  have hsmall : ENNReal.ofReal |F (fun x => φ x - ψ i x)| ≤ ENNReal.ofReal η := by
    have h1 := LatticeProb.Sobolev.abs_apply_le_negSobolevNorm D s₀ η hη F hsmul
      (hφ.sub (hψt i)) hi
    calc ENNReal.ofReal |F (fun x => φ x - ψ i x)|
        ≤ ENNReal.ofReal η * LatticeProb.Sobolev.negSobolevNorm d s₀ D F := h1
      _ ≤ ENNReal.ofReal η * 1 := mul_le_mul_right hF _
      _ = ENNReal.ofReal η := mul_one _
  have hsplit : F φ = F (fun x => φ x - ψ i x) + F (ψ i) := by
    have hs := hsub φ (ψ i) hφ (hψt i)
    linarith
  calc ENNReal.ofReal |F φ|
      = ENNReal.ofReal |F (fun x => φ x - ψ i x) + F (ψ i)| := by rw [hsplit]
    _ ≤ ENNReal.ofReal (|F (fun x => φ x - ψ i x)| + |F (ψ i)|) := by
          apply ENNReal.ofReal_le_ofReal
          exact abs_add_le _ _
    _ = ENNReal.ofReal |F (fun x => φ x - ψ i x)| + ENNReal.ofReal |F (ψ i)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ ENNReal.ofReal η + (⨆ i, ENNReal.ofReal |F (ψ i)|) :=
          add_le_add hsmall (le_iSup (fun i => ENNReal.ofReal |F (ψ i)|) i)
    _ = (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := add_comm _ _

/-- **The finite-net Rellich-Kondrachov upgrade, in probability.**  A family
tight in `H^{-s_0}(D)`, subtractive on test functions and homogeneous, whose
value at every fixed test function converges to zero in probability, converges
to zero in probability in the `H^{-s}(D)` dual norm for every `s_0 < s`. -/
theorem tendsto_negSobolevNorm_zero_of_tight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s₀ : ℝ) (F : ℝ → Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (hTight : Sandpile.Continuum.TightInNegSobolev d s₀ P F)
    (hsub : ∀ (R : ℝ) (ω : Ω) (φ ψ : Sandpile.Continuum.Space d → ℝ),
      Sandpile.Continuum.IsTestFn Set.univ φ → Sandpile.Continuum.IsTestFn Set.univ ψ →
      F R ω (fun x => φ x - ψ x) = F R ω φ - F R ω ψ)
    (hsmul : ∀ (R : ℝ) (ω : Ω) (c : ℝ) (φ : Sandpile.Continuum.Space d → ℝ),
      F R ω (fun x => c * φ x) = c * F R ω φ)
    (htendsto : ∀ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun R : ℝ => (P {ω | ENNReal.ofReal δ < ENNReal.ofReal |F R ω φ|}).toReal)
          atTop (𝓝 0))
    (hRK : LatticeProb.External.RellichKondrachovNegSobolev)
    (s : ℝ) (hs₀s : s₀ < s) (D : Set (Sandpile.Continuum.Space d))
    (hD : Sandpile.Continuum.IsDomain D) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun R : ℝ =>
        (P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}).toReal)
      atTop (𝓝 0) := by
  have hnn : ∀ R : ℝ,
      0 ≤ (P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}).toReal :=
    fun R => ENNReal.toReal_nonneg
  refine tendsto_order.mpr ⟨fun a ha => Filter.Eventually.of_forall fun R =>
    lt_of_lt_of_le ha (hnn R), fun b hb => ?_⟩
  -- η controls the tightness threshold's failure probability; kept strictly below `b/3`.
  set η : ℝ := min (b / 4) 1 with hη_def
  have hηpos : 0 < η := lt_min (by linarith) one_pos
  have hη3 : η < b / 3 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨M, hM, hMR⟩ := hTight D hD η hηpos
  set M1 : ℝ≥0∞ := M + 1 with hM1_def
  have hM1ne : M1 ≠ ⊤ := by rw [hM1_def]; exact ENNReal.add_ne_top.mpr ⟨hM, ENNReal.one_ne_top⟩
  have hM1pos : (0 : ℝ≥0∞) < M1 := by
    rw [hM1_def]
    calc (0 : ℝ≥0∞) < 1 := one_pos
      _ ≤ M + 1 := le_add_self
  have hMleM1 : M ≤ M1 := by rw [hM1_def]; exact le_self_add
  have hM1toRealPos : 0 < M1.toReal := ENNReal.toReal_pos hM1pos.ne' hM1ne
  set c : ℝ := (M1.toReal)⁻¹ with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  -- η1 controls the Rellich-Kondrachov net's residual, kept strictly below both `b/3` and the
  -- amount that, rescaled by `M1`, is below `ε/2`.
  set η1 : ℝ := min (b / 4) (ε / (4 * (M1.toReal + 1))) with hη1_def
  have hη1pos : 0 < η1 := lt_min (by linarith) (by positivity)
  have hη1_3 : η1 < b / 3 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη1_val : η1 ≤ ε / (4 * (M1.toReal + 1)) := min_le_right _ _
  obtain ⟨N, ψ, hψt, hnet⟩ := hRK d D hD s₀ s hs₀s η1 hη1pos
  have hchebyshev : ∀ i : Fin N,
      ∀ᶠ R : ℝ in atTop,
        (P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}).toReal
          < b / (3 * N + 3) := by
    intro i
    have htf : Sandpile.Continuum.IsTestFn Set.univ (ψ i) := by
      obtain ⟨hsm, hcs, _hts⟩ := hψt i
      exact ⟨hsm, hcs, Set.subset_univ _⟩
    exact (tendsto_order.mp (htendsto (ψ i) htf (ε / 2) (by linarith))).2
      (b / (3 * N + 3)) (by positivity)
  have hbig1 : ∀ᶠ R : ℝ in atTop,
      (P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}).toReal < b / 3 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR1
    have hsubM : {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}
        ⊆ {ω | M < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)} := by
      intro ω hω
      exact lt_of_le_of_lt hMleM1 hω
    calc (P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}).toReal
        ≤ (P {ω | M < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubM)
      _ ≤ (ENNReal.ofReal η).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMR R hR1)
      _ = η := ENNReal.toReal_ofReal hηpos.le
      _ < b / 3 := hη3
  have hbig2 : ∀ᶠ R : ℝ in atTop, ∀ i : Fin N,
      (P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}).toReal
        < b / (3 * N + 3) :=
    Filter.eventually_all.mpr hchebyshev
  filter_upwards [hbig1, hbig2] with R hR1 hR2
  set G : Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ := fun ω φ => c * F R ω φ with hG_def
  have hFeq : ∀ ω φ, F R ω φ = M1.toReal * G ω φ := by
    intro ω φ
    show F R ω φ = M1.toReal * (c * F R ω φ)
    rw [hc_def, ← mul_assoc, mul_inv_cancel₀ hM1toRealPos.ne', one_mul]
  have hFGrel : ∀ ω : Ω, F R ω = (fun φ => M1.toReal * G ω φ) := fun ω => funext (hFeq ω)
  have hnormEq : ∀ ω, Sandpile.Continuum.negSobolevNorm d s D (F R ω)
      = ENNReal.ofReal (M1.toReal) * Sandpile.Continuum.negSobolevNorm d s D (G ω) := by
    intro ω; rw [hFGrel ω]; exact negSobolevNorm_const_mul (G ω) hM1toRealPos
  have hnormEq0 : ∀ ω, Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)
      = ENNReal.ofReal (M1.toReal) * Sandpile.Continuum.negSobolevNorm d s₀ D (G ω) := by
    intro ω; rw [hFGrel ω]; exact negSobolevNorm_const_mul (G ω) hM1toRealPos
  have hGsub : ∀ (ω : Ω) (φ ψ' : Sandpile.Continuum.Space d → ℝ),
      Sandpile.Continuum.IsTestFn Set.univ φ → Sandpile.Continuum.IsTestFn Set.univ ψ' →
      G ω (fun x => φ x - ψ' x) = G ω φ - G ω ψ' := by
    intro ω φ ψ' hφ' hψ''
    show c * F R ω (fun x => φ x - ψ' x) = c * F R ω φ - c * F R ω ψ'
    rw [hsub R ω φ ψ' hφ' hψ'']; ring
  have hGsmul : ∀ (ω : Ω) (c' : ℝ) (φ : Sandpile.Continuum.Space d → ℝ),
      G ω (fun x => c' * φ x) = c' * G ω φ := by
    intro ω c' φ; show c * F R ω (fun x => c' * φ x) = c' * (c * F R ω φ)
    rw [hsmul R ω c' φ]; ring
  have hsub : {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
      ⊆ {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)} ∪
        (⋃ i : Fin N, {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hcon
    obtain ⟨hcon1, hcon2⟩ := hcon
    have hle1 : Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω) ≤ M1 := not_lt.mp hcon1
    have hcon2' : ∀ i : Fin N, |F R ω (ψ i)| ≤ ε / 2 := by
      intro i
      have := not_lt.mp (hcon2 i)
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    have hGle1 : Sandpile.Continuum.negSobolevNorm d s₀ D (G ω) ≤ 1 := by
      have h1 : ENNReal.ofReal (M1.toReal) * Sandpile.Continuum.negSobolevNorm d s₀ D (G ω)
          ≤ M1 := by
        rw [← hnormEq0 ω]; exact hle1
      rw [ENNReal.ofReal_toReal hM1ne] at h1
      have h1' : Sandpile.Continuum.negSobolevNorm d s₀ D (G ω) * M1 ≤ 1 * M1 := by
        rw [one_mul, mul_comm]; exact h1
      exact (ENNReal.mul_le_mul_iff_left hM1pos.ne' hM1ne).mp h1'
    have hGle1' : LatticeProb.Sobolev.negSobolevNorm d s₀ D (G ω) ≤ 1 := by
      rwa [← negSobolevNorm_eq_latticeProb]
    have hGsub' : ∀ φ ψ' : LatticeProb.Sobolev.Space d → ℝ, LatticeProb.Sobolev.IsTestFn D φ →
        LatticeProb.Sobolev.IsTestFn D ψ' → G ω (fun x => φ x - ψ' x) = G ω φ - G ω ψ' := by
      intro φ ψ' hφD hψD'
      obtain ⟨a1, a2, _a3⟩ := hφD
      obtain ⟨b1, b2, _b3⟩ := hψD'
      exact hGsub ω φ ψ' ⟨a1, a2, Set.subset_univ _⟩ ⟨b1, b2, Set.subset_univ _⟩
    have hnetstep := negSobolevNorm_le_sup_add_sub hs₀s η1 hη1pos N ψ hψt hnet
      (G ω) hGsub' (hGsmul ω) hGle1'
    have hsupbound : (⨆ i, ENNReal.ofReal |G ω (ψ i)|) ≤ ENNReal.ofReal (ε / (2 * M1.toReal)) := by
      refine iSup_le fun i => ?_
      have hGψ : G ω (ψ i) = c * F R ω (ψ i) := rfl
      have hb1 : |G ω (ψ i)| ≤ c * (ε / 2) := by
        rw [hGψ, abs_mul, abs_of_pos hcpos]
        exact mul_le_mul_of_nonneg_left (hcon2' i) hcpos.le
      refine ENNReal.ofReal_le_ofReal (le_trans hb1 (le_of_eq ?_))
      rw [hc_def]; ring
    have hη1lt : η1 < ε / (2 * M1.toReal) := by
      refine lt_of_le_of_lt hη1_val ?_
      rw [div_lt_div_iff_of_pos_left hε (by linarith [hM1toRealPos])
        (by linarith [hM1toRealPos])]
      nlinarith [hM1toRealPos]
    have hnormG : LatticeProb.Sobolev.negSobolevNorm d s D (G ω)
        < ENNReal.ofReal (ε / M1.toReal) := by
      have hLHS : LatticeProb.Sobolev.negSobolevNorm d s D (G ω)
          ≤ ENNReal.ofReal (ε / (2 * M1.toReal)) + ENNReal.ofReal η1 :=
        le_trans hnetstep (by gcongr)
      have hRHS_eq : ENNReal.ofReal (ε / (2 * M1.toReal)) + ENNReal.ofReal η1
          = ENNReal.ofReal (ε / (2 * M1.toReal) + η1) :=
        (ENNReal.ofReal_add (by positivity) hη1pos.le).symm
      have hsum_lt : ε / (2 * M1.toReal) + η1 < ε / M1.toReal := by
        have heq : ε / M1.toReal - ε / (2 * M1.toReal) = ε / (2 * M1.toReal) := by
          field_simp; ring
        linarith [hη1lt, heq]
      calc LatticeProb.Sobolev.negSobolevNorm d s D (G ω)
          ≤ ENNReal.ofReal (ε / (2 * M1.toReal) + η1) := by rw [← hRHS_eq]; exact hLHS
        _ < ENNReal.ofReal (ε / M1.toReal) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsum_lt
    have hnormF : Sandpile.Continuum.negSobolevNorm d s D (F R ω) < ENNReal.ofReal ε := by
      have hstep : Sandpile.Continuum.negSobolevNorm d s D (F R ω)
          = ENNReal.ofReal M1.toReal * LatticeProb.Sobolev.negSobolevNorm d s D (G ω) := by
        rw [hnormEq ω, negSobolevNorm_eq_latticeProb]
      rw [hstep]
      have hMe : ENNReal.ofReal M1.toReal ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hM1toRealPos
      have hMe' : ENNReal.ofReal M1.toReal ≠ ⊤ := ENNReal.ofReal_ne_top
      have hkey := ENNReal.mul_lt_mul_left hMe hMe' hnormG
      rw [mul_comm (LatticeProb.Sobolev.negSobolevNorm d s D (G ω)),
        mul_comm (ENNReal.ofReal (ε / M1.toReal))] at hkey
      have heq : ENNReal.ofReal M1.toReal * ENNReal.ofReal (ε / M1.toReal) = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul hM1toRealPos.le]
        congr 1
        field_simp
      rwa [heq] at hkey
    exact absurd hω (not_lt.mpr hnormF.le)
  have hcombine : P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
      ≤ P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}
        + ∑ i : Fin N, P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|} := by
    have h1 : P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
        ≤ P ({ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)} ∪
            (⋃ i : Fin N, {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|})) :=
      measure_mono hsub
    have h3 : P (⋃ i : Fin N, {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|})
        ≤ ∑ i : Fin N, P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|} :=
      measure_iUnion_fintype_le _ _
    calc P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
        ≤ P ({ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)} ∪
            (⋃ i : Fin N, {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|})) := h1
      _ ≤ P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}
          + P (⋃ i : Fin N, {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}) :=
        measure_union_le _ _
      _ ≤ P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}
          + ∑ i : Fin N, P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|} := by
        gcongr
  have hcombine' :
      (P {ω | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}).toReal
      ≤ (P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}).toReal
        + ∑ i : Fin N, (P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}).toReal := by
    have hne : P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}
          + ∑ i : Fin N, P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|} ≠ ⊤ :=
      ENNReal.add_ne_top.mpr
        ⟨measure_ne_top _ _, ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top _ _⟩
    have := ENNReal.toReal_mono hne hcombine
    rwa [ENNReal.toReal_add (measure_ne_top _ _)
        (ENNReal.sum_ne_top.mpr fun i _ => measure_ne_top _ _),
      ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at this
  have hsum_lt : (P {ω | M1 < Sandpile.Continuum.negSobolevNorm d s₀ D (F R ω)}).toReal
      + ∑ i : Fin N, (P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}).toReal
      < b := by
    have hstep : ∑ i : Fin N, (P {ω | ENNReal.ofReal (ε / 2) < ENNReal.ofReal |F R ω (ψ i)|}).toReal
        ≤ ∑ _i : Fin N, b / (3 * N + 3) :=
      Finset.sum_le_sum fun i _ => (hR2 i).le
    have hstep2 : (∑ _i : Fin N, b / (3 * N + 3) : ℝ) ≤ b / 3 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]
      rw [show (N:ℝ) * (b / (3 * N + 3)) * 3 = (3 * N * b) / (3 * N + 3) by ring]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * (N:ℝ) + 3)]
      nlinarith [Nat.cast_nonneg (α := ℝ) N, hb]
    linarith [hR1, hstep, hstep2]
  linarith [hcombine', hsum_lt]

/-- `Sandpile.Continuum.latticePairing` is homogeneous in the test function:
`MeasureTheory.integral_const_mul` needs no integrability, unlike the
subtraction `latticePairing_sub_testFn`. -/
theorem latticePairing_apply_const_mul (R c : ℝ) (f : Sandpile.Site d → ℝ)
    (φ : Sandpile.Continuum.Space d → ℝ) :
    Sandpile.Continuum.latticePairing R f (fun x => c * φ x)
      = c * Sandpile.Continuum.latticePairing R f φ := by
  show ∫ z, Sandpile.Continuum.embed R f z * (c * φ z)
    = c * ∫ z, Sandpile.Continuum.embed R f z * φ z
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- **The `H^{-s}_loc` clause of `lem:dgt4-linearization-from-survival`**
(`sandpile.tex:5836-5849`), from the tested `L²` estimate (the first
conclusion) and the tightness of the odometer and the weighted field. -/
theorem tendsto_negSobolevNorm_zero_of_linearization [NeZero d] (hd : 5 ≤ d)
    (hGH : Sandpile.External.GreenBoundsHigh)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (hRK : Sandpile.External.RellichKondrachovNegSobolev)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hsqν : Integrable (fun z => z ^ 2) ν)
    (T : ℝ) (hT : 0 < T) (q : ℝ → ℕ → ℝ)
    (hq : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ → q R j ∈ Set.Icc (0 : ℝ) 1)
    (hL2 : ∀ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn Set.univ φ →
      Tendsto (fun R : ℝ =>
          ∫ σ, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
              (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                  q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ) ^ 2
            ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0)) :
    ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
      ∀ D : Set (Sandpile.Continuum.Space d), Sandpile.Continuum.IsDomain D →
        ∀ ε : ℝ, 0 < ε →
          Tendsto (fun R : ℝ =>
              ((Sandpile.centeredMassLaw d ν)
                {σ | ENNReal.ofReal ε < Sandpile.Continuum.negSobolevNorm d s D
                  (fun φ => R ^ (((d : ℝ) - 4) / 2) *
                    Sandpile.Continuum.latticePairing R
                      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
                        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
                          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ)}).toReal)
            atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsqν
  have hpos : Integrable (fun z : ℝ => max z 0) ν := Sandpile.integrable_posPart_of_sq ν hsqν
  set O : ℝ → (Sandpile.Site d → ℝ) → (Sandpile.Continuum.Space d → ℝ) → ℝ := fun R σ φ =>
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ with hO_def
  set W : ℝ → (Sandpile.Site d → ℝ) → (Sandpile.Continuum.Space d → ℝ) → ℝ := fun R σ φ =>
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
      (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ with hW_def
  have hdiff : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ),
      Sandpile.Continuum.IsTestFn Set.univ φ →
      O R σ φ - W R σ φ = R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ := by
    intro R σ φ hφtest
    obtain ⟨_, L, _, _, hb, hsupp, hint⟩ := exists_bound_of_isTestFn hφtest
    rw [hO_def, hW_def]
    show R ^ (((d : ℝ) - 4) / 2) *
        Sandpile.Continuum.latticePairing R (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ -
        R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
          (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ
      = R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
        (fun x => (Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) -
          ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
            q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ
    rw [← mul_sub]
    congr 1
    exact (Sandpile.Support.latticePairing_sub R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊)
      (fun x => ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ hint hsupp).symm
  set diffField : ℝ → (Sandpile.Site d → ℝ) → (Sandpile.Continuum.Space d → ℝ) → ℝ :=
    fun R σ φ => R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ with hdiffField_def
  have hdiff' : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ),
      Sandpile.Continuum.IsTestFn Set.univ φ → O R σ φ - W R σ φ = diffField R σ φ :=
    hdiff
  have hsubF : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ ψ : Sandpile.Continuum.Space d → ℝ),
      Sandpile.Continuum.IsTestFn Set.univ φ → Sandpile.Continuum.IsTestFn Set.univ ψ →
      diffField R σ (fun x => φ x - ψ x) = diffField R σ φ - diffField R σ ψ := by
    intro R σ φ ψ hφt hψt
    obtain ⟨_, Lφ, _, _, _, hsuppφ, hintφ⟩ := exists_bound_of_isTestFn hφt
    obtain ⟨_, Lψ, _, _, _, hsuppψ, hintψ⟩ := exists_bound_of_isTestFn hψt
    show diffField R σ (fun x => φ x - ψ x) = diffField R σ φ - diffField R σ ψ
    rw [hdiffField_def]
    have hkey := Sandpile.latticePairing_sub_testFn R
      (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
        ∑ j ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          q R j * (Sandpile.avg^[j] (Sandpile.scenery d σ)) x) φ ψ hintφ hintψ
      (L := max Lφ Lψ) (fun z hz => le_trans (hsuppφ z hz) (le_max_left _ _))
      (fun z hz => le_trans (hsuppψ z hz) (le_max_right _ _))
    show R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R _ (fun x => φ x - ψ x)
      = R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R _ φ
        - R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R _ ψ
    rw [hkey]; ring
  have hsmulF : ∀ (R : ℝ) (σ : Sandpile.Site d → ℝ) (c : ℝ)
      (φ : Sandpile.Continuum.Space d → ℝ),
      diffField R σ (fun x => c * φ x) = c * diffField R σ φ := by
    intro R σ c φ
    show R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R _ (fun x => c * φ x)
      = c * (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Continuum.latticePairing R _ φ)
    rw [latticePairing_apply_const_mul]; ring
  have htendstoF : ∀ φ : Sandpile.Continuum.Space d → ℝ,
      Sandpile.Continuum.IsTestFn Set.univ φ → ∀ δ : ℝ, 0 < δ →
      Tendsto (fun R : ℝ =>
          ((Sandpile.centeredMassLaw d ν)
            {σ | ENNReal.ofReal δ < ENNReal.ofReal |diffField R σ φ|}).toReal) atTop (𝓝 0) := by
    intro φ hφtest δ hδ
    obtain ⟨_, Lφ, _, _, _, hsupp, hint⟩ := exists_bound_of_isTestFn hφtest
    have hmemR : ∀ R : ℝ, MemLp (fun σ => diffField R σ φ) 2 (Sandpile.centeredMassLaw d ν) := by
      intro R
      have hF : ∀ x : Sandpile.Site d, MemLp (fun σ : Sandpile.Site d → ℝ =>
          Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊ -
            Sandpile.Support.weightedField (q R) ⌊R ^ 2 * T⌋₊ (Sandpile.scenery d σ) x) 2
          (Sandpile.centeredMassLaw d ν) := fun x =>
        ((memLp_two_odometer ν hsqν hd1 ⌊R ^ 2 * T⌋₊ x).sub (memLp_const _)).sub
          (Sandpile.Support.memLp_two_weightedField_mass ν hLp hd1 (q R) ⌊R ^ 2 * T⌋₊ x)
      have h1 :=
        (memLp_two_latticePairing (Sandpile.centeredMassLaw d ν) R _ hF φ hint hsupp).const_mul
          (R ^ (((d : ℝ) - 4) / 2))
      exact h1
    have htim : TendstoInMeasure (Sandpile.centeredMassLaw d ν) (fun R σ => diffField R σ φ)
        atTop 0 :=
      tendstoInMeasure_zero_of_tendsto_integral_sq (Sandpile.centeredMassLaw d ν)
        (fun R σ => diffField R σ φ) hmemR (hL2 φ hφtest)
    exact tendsto_toReal_measure_lt_of_tendstoInMeasure (Sandpile.centeredMassLaw d ν)
      (fun R σ => diffField R σ φ) htim δ hδ
  intro s hs D hD ε hε
  set s₀ : ℝ := (((d : ℝ) - 4) / 2 + s) / 2 with hs₀_def
  have hs₀big : ((d : ℝ) - 4) / 2 < s₀ := by rw [hs₀_def]; linarith
  have hs₀s : s₀ < s := by rw [hs₀_def]; linarith
  have hqQ : ∀ (R : ℝ) (j : ℕ), j < ⌊R ^ 2 * T⌋₊ → |q R j| ≤ 1 := by
    intro R j hj
    have h := hq R j hj
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  have hTightO : Sandpile.Continuum.TightInNegSobolev d s₀ (Sandpile.centeredMassLaw d ν) O :=
    dgt4_odometer_tight hGH hBesov hd ν hsqν hpos T hT s₀ hs₀big
  have hTightW : Sandpile.Continuum.TightInNegSobolev d s₀ (Sandpile.centeredMassLaw d ν) W :=
    weighted_membrane_tight_general hGH hBesov hd ν hLp hmean T hT q 1 (by norm_num) hqQ s₀ hs₀big
  have hTightDiff : Sandpile.Continuum.TightInNegSobolev d s₀ (Sandpile.centeredMassLaw d ν)
      (fun R σ φ => O R σ φ - W R σ φ) :=
    tight_sub s₀ (Sandpile.centeredMassLaw d ν) O W hTightO hTightW
  have hTightDiffField : Sandpile.Continuum.TightInNegSobolev d s₀
      (Sandpile.centeredMassLaw d ν) diffField := by
    intro D' hD' ε' hε'
    obtain ⟨M, hM, hMR⟩ := hTightDiff D' hD' ε' hε'
    refine ⟨M, hM, fun R hR => ?_⟩
    have heq : {σ | M < Sandpile.Continuum.negSobolevNorm d s₀ D'
          (fun φ => O R σ φ - W R σ φ)}
        = {σ | M < Sandpile.Continuum.negSobolevNorm d s₀ D' (diffField R σ)} := by
      ext σ
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
        negSobolevNorm_congr (fun φ hφ => hdiff' R σ φ
          (⟨hφ.1, hφ.2.1, Set.subset_univ _⟩ : Sandpile.Continuum.IsTestFn Set.univ φ))]
    rw [← heq]
    exact hMR R hR
  exact tendsto_negSobolevNorm_zero_of_tight (Sandpile.centeredMassLaw d ν) s₀ diffField
    hTightDiffField hsubF hsmulF htendstoF hRK s hs₀s D hD ε hε

end Sandpile.Support
