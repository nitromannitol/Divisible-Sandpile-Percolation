import Sandpile.External.ContinuumBesovTightness
import Sandpile.Support.ContCell
import Sandpile.Support.TightFloorComparison

/-!
# Tightness in negative Sobolev norm from covariance decay

Lemma of Section 3 of sandpile.tex, frozen.  `sandpile.tex:1692-1702`
(label `lem:sobolev-tightness`):

  "[Tightness from covariance decay]  Let $0<\beta<d$ and $K<\infty$.  For each
   $R\geq1$, let $(F_R(x))_{x\in\Z^d}$ be a mean-zero random field satisfying
   \[
     \bigl|\Cov\bigl(F_R(x),F_R(y)\bigr)\bigr|
     \leq K(1+|x-y|)^{-\beta}
   \]
   for every $x,y\in\Z^d$.  Then, for every $s>\beta/2$, the fields
   $\bigl(R^{\beta/2}F_R^{(R)}\bigr)_{R\geq1}$ are tight in
   $H^{-s}_{\rm loc}(\R^d)$."

The paper's index `R` runs over `[1,∞)`, so every hypothesis about the field is
stated for real `R ≥ 1` and the conclusion is `TightInNegSobolev`, whose own
quantifiers already restrict to `1 ≤ R`.

The paper lets the field `F_R` live on an unnamed probability space, one for
each `R`; nothing in the lemma couples different values of `R`, so a family
of spaces and a single space give the same statement, and the paper applies
the lemma to fields built from one scenery on one space.  Accordingly all
the fields here are carried by a single space `Ω` with law `P`, and `F R ω x` is
`F_R(x)` evaluated at the sample point `ω`.

`|x - y|` is the Euclidean norm of the notation section (`sandpile.tex:678`),
written on the lattice as `latticeDist`.  `Cov` is Mathlib's `covariance`,
which is an integral and would take the junk value zero for a field whose
product is not integrable; the square-integrability hypothesis `hmem` removes
that, and it is also what makes `Cov(F_R(x),F_R(y))` a well-defined number in
the paper.  Mean zero is stated separately, as the paper does, even though it
is not needed for `covariance` to be defined.

`F_R^{(R)}` is the paper's embedding `f^{(R)}(z) = f(⌊Rz⌋)`, and pairing it
with a test function is `latticePairing`, so the tested family is
`φ ↦ R^{β/2} F_R^{(R)}(φ)`.  Tightness in `H^{-s}_{loc}(ℝ^d)` is
`TightInNegSobolev`, which is the paper's own definition: tightness of the
`H^{-s}(D)` norms for every bounded domain `D`.

`(1 + |x-y|)^{-β}` is a real power of a base at least one, so no junk arises.

Cited input.  The paper's whole proof is the sentence at `sandpile.tex:1676-1680`
that the covariance hypothesis verifies the moment conditions of Furlan and
Mourrat, Theorem 2.30, at `p = q = 2` with regularity exponent `-β/2` and
`α = -s`, and that `B^{-s,loc}_{2,2}(ℝ^d)` is `H^{-s}_loc(ℝ^d)`.  Standing
convention R1 therefore attaches that criterion, and nothing else, as the explicit
hypothesis `hBesov` (`Sandpile.External.ContinuumBesovTightness`), stated for a
field on `ℝ^d` whose covariance decays at scale `R`.  What the lemma adds and
what is proved below is the passage from the lattice field to its
piecewise-constant embedding: the embedded field is square-integrable and
centred because the lattice field is, and its covariance obeys the continuum
decay because the embedding moves each coordinate by less than one, so the
lattice distance of the embedded sites and `R|y-y'|` differ by at most `√d`
and the two decaying powers differ by the factor `(1 + √d)^β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Frozen.SobolevTightness

/-- The Euclidean distance `|x - y|` between lattice points, in the sense of
the notation section (`sandpile.tex:678`): "For $x\in\R^d$, write $|x|$ for the
Euclidean norm." -/
noncomputable def latticeDist {d : ℕ} (x y : Sandpile.Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

end Sandpile.Frozen.SobolevTightness

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.sobolev_tightness
    (d : ℕ) (β K : ℝ) (hβ0 : 0 < β) (hβd : β < (d : ℝ))
    {Ω : Type*} [MeasurableSpace Ω]
    (hBesov : Sandpile.External.ContinuumBesovTightness Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → Sandpile.Site d → ℝ)
    (hmem : ∀ R : ℝ, 1 ≤ R → ∀ x : Sandpile.Site d, MemLp (fun ω => F R ω x) 2 P)
    (hmean : ∀ R : ℝ, 1 ≤ R → ∀ x : Sandpile.Site d, ∫ ω, F R ω x ∂P = 0)
    (hcov : ∀ R : ℝ, 1 ≤ R → ∀ x y : Sandpile.Site d,
      |covariance (fun ω => F R ω x) (fun ω => F R ω y) P| ≤
        K * (1 + Sandpile.Frozen.SobolevTightness.latticeDist x y) ^ (-β))
    (s : ℝ) (hs : β / 2 < s) :
    Sandpile.Continuum.TightInNegSobolev d s P
      (fun R ω φ => R ^ (β / 2) * Sandpile.Continuum.latticePairing R (F R ω) φ)
-- FROZEN-STATEMENT-END
:= by
  have hR0 : ∀ R : ℝ, 1 ≤ R → (0 : ℝ) ≤ R := fun R hR => le_trans zero_le_one hR
  have hK : 0 ≤ K := by
    have h := hcov 1 le_rfl (fun _ => 0) (fun _ => 0)
    have hzero : Sandpile.Frozen.SobolevTightness.latticeDist
        (fun _ : Fin d => (0 : ℤ)) (fun _ : Fin d => (0 : ℤ)) = 0 := by
      simp [Sandpile.Frozen.SobolevTightness.latticeDist]
    rw [hzero] at h
    simpa using le_trans (abs_nonneg _) h
  change Sandpile.Continuum.TightInNegSobolev d s P
    (fun R ω φ => R ^ (β / 2) *
      ∫ y : Sandpile.Continuum.Space d, F R ω (fun i => ⌊R * y i⌋) * φ y)
  refine hBesov d β (K * (1 + Real.sqrt (d : ℝ)) ^ β) hβ0 hβd s hs P
    (fun R ω y => F R ω (fun i => ⌊R * y i⌋)) ?_ ?_ ?_ ?_
  · intro R hR ω
    constructor
    · exact (measurable_of_countable (F R ω)).comp
        (measurable_pi_lambda _ fun i => Sandpile.Support.measurable_coord R i)
    · intro φ hφ
      obtain ⟨_, L, _, _, _, hsupp, hφint⟩ :=
        Sandpile.Support.exists_bound_of_isTestFn hφ
      let s : Finset (Sandpile.Site d) :=
        Sandpile.boxFinset (0 : Sandpile.Site d) (⌈|R| * L⌉₊ + 1)
      have hs : ∀ z : Sandpile.Continuum.Space d, φ z ≠ 0 →
          (fun i => ⌊R * z i⌋) ∈ s := by
        intro z hz
        exact Sandpile.Support.floor_mem_boxFinset R z (hsupp z hz)
      change Integrable (fun z => Sandpile.Continuum.embed R (F R ω) z * φ z)
      simp_rw [Sandpile.Support.embed_mul_eq_sum R (F R ω) φ s hs]
      refine MeasureTheory.integrable_finsetSum s (fun x _ => ?_)
      exact (hφint.const_mul (F R ω x)).indicator
        (Sandpile.Support.measurableSet_cell d R x)
  · intro R hR y
    exact hmem R hR _
  · intro R hR y
    exact hmean R hR _
  intro R hR y y'
  refine le_trans (hcov R hR _ _) ?_
  have hcomp : (1 + Sandpile.Frozen.SobolevTightness.latticeDist
        (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋)) ^ (-β)
      ≤ (1 + Real.sqrt (d : ℝ)) ^ β * (1 + R * ‖y - y'‖) ^ (-β) :=
    Sandpile.Support.rpow_neg_latticeDist_le β hβ0 R (hR0 R hR) y y'
  calc K * (1 + Sandpile.Frozen.SobolevTightness.latticeDist
        (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋)) ^ (-β)
      ≤ K * ((1 + Real.sqrt (d : ℝ)) ^ β * (1 + R * ‖y - y'‖) ^ (-β)) :=
        mul_le_mul_of_nonneg_left hcomp hK
    _ = K * (1 + Real.sqrt (d : ℝ)) ^ β * (1 + R * ‖y - y'‖) ^ (-β) := by ring
