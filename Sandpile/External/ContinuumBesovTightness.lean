import Sandpile.Continuum.Membrane

/-!
# The Furlan-Mourrat Besov tightness criterion

External input: the tightness criterion cited at `sandpile.tex:1661-1662` and
`sandpile.tex:1676-1680`.  The paper introduces its tightness lemma with

  "We will use the following easy consequence of the tightness criterion of
   \citet{FurlanMourrat}."

and, after the statement of `lem:sobolev-tightness`, gives its whole proof:

  "Indeed, the covariance hypothesis verifies the moment conditions of
   \citet[Theorem~2.30]{FurlanMourrat} with $p=q=2$, regularity exponent
   $-\beta/2$, and $\alpha=-s$, and
   $\mathcal B^{-s,{\rm loc}}_{2,2}(\R^d)$ coincides with
   $H^{-s}_{\rm loc}(\R^d)$."

The cited source is Furlan and Mourrat, *A tightness criterion for random
fields, with application to the Ising model*, Annales de l'Institut Henri
Poincaré Probabilités et Statistiques 53 (2017), Theorem 2.30.  What is
assumed here is that theorem in exactly the shape the sentence above puts it
in: at `p = q = 2` a second-moment bound at the diffusive scale, with the
regularity exponent the covariance decay produces, gives tightness in the
Besov space `B^{-s,loc}_{2,2}(ℝ^d)`, and that space is `H^{-s}_loc(ℝ^d)`.  Both
halves of the sentence, the moment criterion and the identification of the two
scales of spaces, are assumed together, since the paper asserts them together
and proves neither.

Shape of the input.  A field indexed by `R ≥ 1` whose covariance decays like
`K R^β (1 + R|y - y'|)^{-β}` is exactly a field whose pairing against a bump of
width `λ` has second moment `O(λ^{-β})`, which is the moment condition at
`p = q = 2` with regularity exponent `-β/2`; the conclusion is tightness of the
pairings in `H^{-s}_loc(ℝ^d)` for every `s > β/2`.  Writing the input this way,
for a field on `ℝ^d` rather than on the lattice, keeps the passage from the
lattice field to its piecewise-constant embedding, and the comparison of the
lattice distance with the Euclidean one, on the paper's side of the boundary;
that passage is what `lem:sobolev-tightness` adds to the criterion, and it is
proved, not assumed.

Modelling.  `Cov` is Mathlib's `covariance`, an integral that would take the
junk value zero for a field whose product is not integrable; the
square-integrability hypothesis removes that, exactly as in the paper's lemma.
The mean-zero hypothesis is stated separately, as the paper does.  The base
`1 + R‖y - y'‖` of the decaying power is at least one, so the real power is not
a junk value.  Tightness is `TightInNegSobolev`, the paper's own formulation:
tightness of the `H^{-s}(D)` norms on every bounded domain `D`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The covariance form of the tightness criterion of Furlan and Mourrat,
Theorem 2.30, at `p = q = 2` with regularity exponent `-β/2` and `α = -s`,
together with the identification of `B^{-s,loc}_{2,2}(ℝ^d)` with
`H^{-s}_loc(ℝ^d)`, in the form the paper invokes at `sandpile.tex:1676-1680`.
Assumed, not proved. -/
def Sandpile.External.ContinuumBesovTightness (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (β K : ℝ), 0 < β → β < (d : ℝ) → ∀ s : ℝ, β / 2 < s →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P]
      (u : ℝ → Ω → Sandpile.Continuum.Space d → ℝ),
      (∀ R : ℝ, 1 ≤ R → ∀ ω : Ω,
        Measurable (fun y => u R ω y) ∧
          ∀ φ : Sandpile.Continuum.Space d → ℝ,
            Sandpile.Continuum.IsTestFn Set.univ φ →
              Integrable (fun y => u R ω y * φ y)) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Sandpile.Continuum.Space d,
        MemLp (fun ω => u R ω y) 2 P) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Sandpile.Continuum.Space d, ∫ ω, u R ω y ∂P = 0) →
      (∀ R : ℝ, 1 ≤ R → ∀ y y' : Sandpile.Continuum.Space d,
        |covariance (fun ω => u R ω y) (fun ω => u R ω y') P| ≤
          K * (1 + R * ‖y - y'‖) ^ (-β)) →
      Sandpile.Continuum.TightInNegSobolev d s P
        (fun R ω φ => R ^ (β / 2) *
          ∫ y : Sandpile.Continuum.Space d, u R ω y * φ y)
-- FROZEN-STATEMENT-END
