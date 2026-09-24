/-
External input: the optimal-stopping theorem for a finite horizon, in the form
cited at `sandpile.tex:1099`.  The paper states the Brownian optimal-stopping
representation (`prop:brownian-os`, `sandpile.tex:1083-1098`) and then proves it
in one line:

  "This is the optimal-stopping theorem applied to the gain $-h(T-s,B_s)$; see
   \citet[Theorem~2.2]{PeskirShiryaev}."

The cited source is Peskir and Shiryaev, *Optimal Stopping and Free-Boundary
Problems*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2006, Chapter I,
Section 2, Theorem 2.2, the finite-horizon Markovian optimal-stopping theorem.
For a right-continuous strong Markov process `X`, a horizon `T`, and a gain `G`
with `E sup_{0 ≤ s ≤ T} |G(s, X_s)| < ∞`, that theorem asserts, for the value
`V(t,x) = sup_{0 ≤ τ ≤ t} E_x G(t - τ, X_τ)`:

  * the value process `s ↦ V(T - s, X_s)` has a right-continuous modification;
  * the first entry time into the contact set `{V = G}` is a stopping time and
    is optimal;
  * the optimal value is attained, and the value is finite;
  * every optimal stopping time dominates that first entry time.

Here `X` is Brownian motion on `ℝ^d` with generator `Δ/(2d)`, which is a
right-continuous strong Markov process, and the gain is the one the paper names,
`G = -h`, with `h` continuous of polynomial growth on `[0,T] × ℝ^d`.  Those two
properties of `h` are exactly the standing assumptions of the paper's
subsection (`sandpile.tex:1071-1073`), and they are what makes the source's
integrability condition automatic, since the maximum of `‖B_s‖` over `s ≤ T`
has moments of every order; the paper does not verify it separately and neither
does this input, which is assumed, not proved.

This input is stated for a general gain `G`, as in the source.  The paper's
value `𝒟_h` is `snellValue` at the gain `-h`, and `𝒰_h = h + 𝒟_h`; the
translation between the two vocabularies is made where the input is applied,
not here.

Modelling.  Attainment of the value and finiteness of the value are recorded
together as `IsGreatest`: the optimal stopping time's payoff belongs to the set
of attainable payoffs and dominates every member of it.  Writing them this way
avoids the junk value of an unbounded real supremum, which would otherwise make
the paper's displayed identity a statement about `sSup ∅`-style defaults rather
than about the value.  The first entry time is written as `IsLeast` of the
contact set, which asserts both membership and minimality and again avoids the
junk value of `sInf`.  Measurability of each `M s` is asserted because a
modification of a process is a process.
-/
import Sandpile.Continuum.Stopping

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Snell

/-- The value of the finite-horizon stopping problem with gain `G` and horizon
`t`, `V(t,x) = sup_{0 ≤ τ ≤ t} E_x G(t - τ, B_τ)`, for the Brownian motion `B`
started at `x`.  The paper's `𝒟_h(t,x)` is this value at the gain `G = -h`. -/
noncomputable def snellValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ) (t : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

/-- The payoffs attainable at horizon `t` by an admissible stopping time. -/
def attainable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ) (t : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

end Sandpile.External.Snell

-- FROZEN-STATEMENT-BEGIN
/-- The finite-horizon optimal-stopping theorem for Brownian motion on `ℝ^d`
with a continuous gain of polynomial growth, in the form cited at
`sandpile.tex:1099` (Peskir and Shiryaev, Theorem 2.2), on a probability space
`Ω` carrying such a Brownian family.  Assumed, not proved. -/
def Sandpile.External.ContinuumOptimalStopping (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (T : ℝ), 0 < T →
    ∀ G : ℝ → Sandpile.Continuum.Space d → ℝ,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) →
      (∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ y : Sandpile.Continuum.Space d, |G t y| ≤ C * (1 + ‖y‖) ^ k) →
      ∀ x : Sandpile.Continuum.Space d,
        ∀ (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d),
          (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P) →
          ∃ M : ℝ≥0 → Ω → ℝ,
            (∀ s : ℝ≥0, Measurable (M s)) ∧
            (∀ s : ℝ≥0, (s : ℝ) ≤ T →
              M s =ᵐ[P] fun ω =>
                Sandpile.External.Snell.snellValue (B (B x s ω)) P G (T - (s : ℝ))) ∧
            (∀ (ω : Ω) (s : ℝ≥0),
              ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
            ∃ τ : Ω → ℝ≥0,
              (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
                M s ω = G (T - (s : ℝ)) (B x s ω)} (τ ω)) ∧
              Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
              IsGreatest (Sandpile.External.Snell.attainable (B x) P G T)
                (∫ ω, G (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∧
              ∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
                (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
                (∫ ω, G (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P) =
                  Sandpile.External.Snell.snellValue (B x) P G T →
                ∀ᵐ ω ∂P, τ ω ≤ τ' ω
-- FROZEN-STATEMENT-END
