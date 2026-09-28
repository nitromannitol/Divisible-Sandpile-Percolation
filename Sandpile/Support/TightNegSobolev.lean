import Sandpile.Continuum.Membrane
import LatticeProb.Analysis.Sobolev.Basic

/-!
# Elementary properties of the negative Sobolev norm

Elementary properties of the negative Sobolev norm and of the lattice pairing: the norm is
monotone in the size of the functional, tightness only reads the family at scales at least one,
and the pairing is homogeneous in the field. These facts (`tight_congr_ge_one`,
`latticePairing_const_mul`, `negSobolevNorm_le_const_mul`, `tight_of_abs_le`, `tight_sub`,
`negSobolevNorm_mono_domain`) reduce tightness of a functional to tightness of a dominating or
approximating one, which is how tightness in `H^{-s}_loc` is established elsewhere from more
elementary tight families.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Support

/-- Tightness in `H^{-s}_loc` depends on the family only at scales at least one. -/
theorem tight_congr_ge_one {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ) (P : Measure Ω)
    (F G : ℝ → Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (h : ∀ R : ℝ, 1 ≤ R → ∀ ω : Ω, F R ω = G R ω)
    (hF : Sandpile.Continuum.TightInNegSobolev d s P F) :
    Sandpile.Continuum.TightInNegSobolev d s P G := by
  intro D hD ε hε
  obtain ⟨M, hM, hMR⟩ := hF D hD ε hε
  refine ⟨M, hM, fun R hR => ?_⟩
  have hset : {ω | M < Sandpile.Continuum.negSobolevNorm d s D (G R ω)}
      = {ω | M < Sandpile.Continuum.negSobolevNorm d s D (F R ω)} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h R hR ω]
  rw [hset]
  exact hMR R hR

/-- The lattice pairing is homogeneous in the field. -/
theorem latticePairing_const_mul {d : ℕ} (R c : ℝ) (f : Sandpile.Site d → ℝ)
    (φ : Sandpile.Continuum.Space d → ℝ) :
    Sandpile.Continuum.latticePairing R (fun x => c * f x) φ
      = c * Sandpile.Continuum.latticePairing R f φ := by
  unfold Sandpile.Continuum.latticePairing
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show Sandpile.Continuum.embed R (fun x => c * f x) z * φ z
    = c * (Sandpile.Continuum.embed R f z * φ z)
  unfold Sandpile.Continuum.embed
  ring

/-- The `H^{-s}(D)` norm of a functional is at most that of a multiple of it by
a factor at least one. -/
theorem negSobolevNorm_le_const_mul {d : ℕ} (s : ℝ) (D : Set (Sandpile.Continuum.Space d))
    (F : (Sandpile.Continuum.Space d → ℝ) → ℝ) (c : ℝ) (hc : 1 ≤ c) :
    Sandpile.Continuum.negSobolevNorm d s D F
      ≤ Sandpile.Continuum.negSobolevNorm d s D (fun φ => c * F φ) := by
  refine LatticeProb.Sobolev.negSobolevNorm_le_of_abs_le s D F (fun φ => c * F φ) ?_
  intro φ
  have hc0 : (0:ℝ) ≤ c := le_trans zero_le_one hc
  rw [abs_mul, abs_of_nonneg hc0]
  nlinarith [abs_nonneg (F φ)]

/-- Tightness passes to a family dominated pointwise by a tight one. -/
theorem tight_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (s : ℝ)
    (P : Measure Ω)
    (F G : ℝ → Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (hFG : ∀ R : ℝ, 1 ≤ R → ∀ (ω : Ω) (φ : Sandpile.Continuum.Space d → ℝ),
      |F R ω φ| ≤ |G R ω φ|)
    (hG : Sandpile.Continuum.TightInNegSobolev d s P G) :
    Sandpile.Continuum.TightInNegSobolev d s P F := by
  intro D hD ε hε
  obtain ⟨M, hM, hMR⟩ := hG D hD ε hε
  refine ⟨M, hM, ?_⟩
  intro R hR
  refine le_trans (measure_mono ?_) (hMR R hR)
  intro ω hω
  exact lt_of_lt_of_le hω
    (LatticeProb.Sobolev.negSobolevNorm_le_of_abs_le s D (F R ω) (G R ω) (hFG R hR ω))

/-- Tightness in `H^{-s}_loc` passes to the difference of two tight families: the
norm of a difference is at most the sum of the norms, so the event where the
difference exceeds `M_F + M_G` is contained in the union of the two bad events. -/
theorem tight_sub {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (s : ℝ) (P : Measure Ω)
    (F G : ℝ → Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (hF : Sandpile.Continuum.TightInNegSobolev d s P F)
    (hG : Sandpile.Continuum.TightInNegSobolev d s P G) :
    Sandpile.Continuum.TightInNegSobolev d s P (fun R ω φ => F R ω φ - G R ω φ) := by
  intro D hD ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨MF, hMF, hMFR⟩ := hF D hD (ε / 2) hε2
  obtain ⟨MG, hMG, hMGR⟩ := hG D hD (ε / 2) hε2
  refine ⟨MF + MG, by simp [hMF, hMG], ?_⟩
  intro R hR
  have hsub : {ω | MF + MG < Sandpile.Continuum.negSobolevNorm d s D
        (fun φ => F R ω φ - G R ω φ)}
      ⊆ {ω | MF < Sandpile.Continuum.negSobolevNorm d s D (F R ω)} ∪
        {ω | MG < Sandpile.Continuum.negSobolevNorm d s D (G R ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    by_contra hcon
    push Not at hcon
    have hle := LatticeProb.Sobolev.negSobolevNorm_sub_le s D (F R ω) (G R ω)
    exact absurd (le_trans hle (add_le_add hcon.1 hcon.2)) (not_le.mpr hω)
  calc P {ω | MF + MG < Sandpile.Continuum.negSobolevNorm d s D
        (fun φ => F R ω φ - G R ω φ)}
      ≤ P ({ω | MF < Sandpile.Continuum.negSobolevNorm d s D (F R ω)} ∪
          {ω | MG < Sandpile.Continuum.negSobolevNorm d s D (G R ω)}) :=
        measure_mono hsub
    _ ≤ P {ω | MF < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
        + P {ω | MG < Sandpile.Continuum.negSobolevNorm d s D (G R ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add (hMFR R hR) (hMGR R hR)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        norm_num

/-- The `H^{-s}` norm on a larger domain is larger, since it takes the supremum
over more test functions. -/
theorem negSobolevNorm_mono_domain {d : ℕ} (s : ℝ) {D D' : Set (Sandpile.Continuum.Space d)}
    (h : D ⊆ D') (F : (Sandpile.Continuum.Space d → ℝ) → ℝ) :
    Sandpile.Continuum.negSobolevNorm d s D F
      ≤ Sandpile.Continuum.negSobolevNorm d s D' F := by
  unfold Sandpile.Continuum.negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, ⟨hsm, hcs, hts⟩, hn, rfl⟩
  exact le_sSup ⟨φ, ⟨hsm, hcs, hts.trans h⟩, hn, rfl⟩

end Sandpile.Support
