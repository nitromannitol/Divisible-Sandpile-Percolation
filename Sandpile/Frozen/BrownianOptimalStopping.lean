import Sandpile.External.ContinuumOptimalStopping

/-!
# Brownian optimal-stopping representation

Proposition of Section 2 of sandpile.tex, frozen.  `sandpile.tex:1083-1099`
(label `prop:brownian-os`):

  "[Brownian optimal-stopping representation]  Fix $T>0$ and $x\in\R^d$.  The
   value process $s\mapsto \mathcal D_h(T-s,B_s)$ has a right-continuous
   modification.  With this modification, the first time at which the value
   vanishes,
   \[
     \tau_h^*\coloneqq \inf\{0\leq s\leq T:\mathcal U_h(T-s,B_s)=0\}\leq T\, ,
   \]
   is optimal, and for every optimal stopping time $\tau$ it satisfies
   $\tau_h^*\leq\tau$ almost surely.  In particular,
   \[
     \mathcal U_h(T,x)
     =
     \sup_{0\leq\tau\leq T}\bigl(h(T,x)-\mathbf E_x^{\rm BM} h(T-\tau,B_\tau)\bigr)
     =
     h(T,x)-\mathbf E_x^{\rm BM} h(T-\tau_h^*,B_{\tau_h^*})\, ."

The setup is `sandpile.tex:1069-1082`: "We state it for a fixed deterministic
field $h:[0,T]\times\R^d\to\R$ that is continuous and has polynomial growth.
For $0\leq t\leq T$, set
$\mathcal D_h(t,x)\coloneqq\sup_{\tau\leq t}\mathbf E_x^{\rm BM}[-h(t-\tau,B_\tau)]$,
$\mathcal U_h(t,x)\coloneqq h(t,x)+\mathcal D_h(t,x)$, where the supremum is
over Brownian stopping times."  Those two objects are `brownianDiscount` and
`brownianValue`.  All three properties of `h` are hypotheses: it is a function,
not a random field, so it is deterministic by construction; `hcont` is
continuity on `[0,T]×ℝ^d`; `hgrow` is polynomial growth there, with the degree
and the constant existentially quantified as the phrase "has polynomial growth"
means.

Modelling choices.

Mathlib 4.32 has no construction of Brownian motion, so the statement is
quantified over a space carrying one.  `brownianDiscount B P h t` carries the
starting point only through `B`, which must be Brownian motion started there,
so the value at a general point needs a family `B` of Brownian motions indexed
by the starting point, with `B y` started at `y`.  The value process
`s ↦ 𝒟_h(T-s,B_s)` is then `fun ω => brownianDiscount (B (B x s ω)) P h (T-s)`:
the outer `B x` is the path being followed, the inner `B (B x s ω)` supplies
the Brownian motion started at the point reached.  The paper's `\mathbf E_x^{BM}`
is the integral against `P` of the family member started at `x`.

"Has a right-continuous modification" is the existence of a process `M` on the
same space which equals the value process almost surely at each fixed time
`s ∈ [0,T]` and whose paths are right-continuous at every time.  Measurability
of `M s` is asserted, since a modification of a process is a process; the paper
does not say this separately.

`τ_h^*` is written as the least element of `{s ≤ T : 𝒰_h(T-s,B_s) = 0}` rather
than as an `sInf`.  This both avoids the junk value `sInf ∅ = 0` and records the
paper's phrase "the first time at which the value vanishes"; the set is
nonempty, since `𝒟_h(0,y) = -h(0,y)` makes `s = T` a member, so `τ_h^* ≤ T` is
a consequence and is not stated separately.  `IsLeast` asserts attainment,
which is what right-continuity of the modification provides.

"Optimal" is the second displayed identity: the stopping time attains the
value.  The minimality clause is stated for every admissible `τ'` which attains
the same value, and asserts `τ ≤ τ'` almost surely, the null set depending on
`τ'`.  The first displayed
identity is the supremum over admissible stopping times of
`h(T,x) - E_x^{BM} h(T-τ,B_τ)`, written as the `sSup` of the set of values
attained, which is how `brownianDiscount` itself is written.

Stopping times are those of `IsBrownianStopping`, Galmarino's criterion, which
for the natural filtration of `B` is equivalent to the paper's "stopping times
of the completed natural filtration of $B$" (`sandpile.tex:973-974`).

Every clause of the proposition is transcribed; none is dropped.

Cited input.  The paper's proof is the single sentence at `sandpile.tex:1099`,
"This is the optimal-stopping theorem applied to the gain $-h(T-s,B_s)$; see
\citet[Theorem~2.2]{PeskirShiryaev}."  Standing convention R1 therefore attaches
that theorem, and nothing else, as the explicit hypothesis `hOS`, the
finite-horizon optimal-stopping theorem for Brownian motion with a continuous
gain of polynomial growth (`Sandpile.External.ContinuumOptimalStopping`).  The gain is
`G = -h`, as the paper says; the proof below verifies that `-h` is continuous
with polynomial growth and translates the input's value, contact set and
attainment into the paper's `𝒟_h`, `𝒰_h` and the two displayed identities.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.brownian_optimal_stopping
    (d : ℕ) (T : ℝ) (hT : 0 < T) (h : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y : Sandpile.Continuum.Space d, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    (x : Sandpile.Continuum.Space d)
    {Ω : Type*} [MeasurableSpace Ω]
    (hOS : Sandpile.External.ContinuumOptimalStopping Ω)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s : ℝ≥0, Measurable (M s)) ∧
      (∀ s : ℝ≥0, (s : ℝ) ≤ T →
        M s =ᵐ[P] fun ω =>
          Sandpile.Continuum.brownianDiscount (B (B x s ω)) P h (T - (s : ℝ))) ∧
      (∀ (ω : Ω) (s : ℝ≥0),
        ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
          h (T - (s : ℝ)) (B x s ω) + M s ω = 0} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P ∧
        (∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
          (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
          Sandpile.Continuum.brownianValue (B x) P h T x =
            h T x - ∫ ω, h (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P →
          ∀ᵐ ω ∂P, τ ω ≤ τ' ω) ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          sSup {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
            (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
            a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P}
-- FROZEN-STATEMENT-END
:= by
  classical
  have hGcont : ContinuousOn
      (fun p : ℝ × Sandpile.Continuum.Space d => (fun t y => -h t y) p.1 p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) := hcont.neg
  have hGgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y : Sandpile.Continuum.Space d, |(fun t y => -h t y) t y| ≤ C * (1 + ‖y‖) ^ k := by
    obtain ⟨C, k, hCk⟩ := hgrow
    exact ⟨C, k, fun t ht y => by simpa using hCk t ht y⟩
  obtain ⟨M, hMmeas, hMmod, hMright, τ, hτleast, hτstop, hτgreat, hτmin⟩ :=
    hOS d T hT (fun t y => -h t y) hGcont hGgrow x P B hB
  have hτle : ∀ ω : Ω, ((τ ω : ℝ≥0) : ℝ) ≤ T := fun ω => (hτleast ω).1.1
  -- the value of the stopping problem is attained at `τ`
  have hdisc : Sandpile.Continuum.brownianDiscount (B x) P h T
      = -∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
    have hg : sSup (Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T)
        = ∫ ω, -h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := hτgreat.csSup_eq
    rw [show Sandpile.Continuum.brownianDiscount (B x) P h T
        = sSup (Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T) from rfl,
      hg, integral_neg]
  have hvalue : Sandpile.Continuum.brownianValue (B x) P h T x
      = h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
    rw [show Sandpile.Continuum.brownianValue (B x) P h T x
        = h T x + Sandpile.Continuum.brownianDiscount (B x) P h T from rfl, hdisc]
    ring
  refine ⟨M, hMmeas, ?_, hMright, τ, ?_, hτstop, hvalue, ?_, ?_⟩
  · intro s hs
    exact hMmod s hs
  · intro ω
    have hset : {s : ℝ≥0 | (s : ℝ) ≤ T ∧ M s ω = (fun t y => -h t y) (T - (s : ℝ)) (B x s ω)}
        = {s : ℝ≥0 | (s : ℝ) ≤ T ∧ h (T - (s : ℝ)) (B x s ω) + M s ω = 0} := by
      ext s
      simp only [Set.mem_setOf_eq, and_congr_right_iff]
      intro _
      constructor
      · intro hh; rw [hh]; ring
      · intro hh; linarith
    exact hset ▸ hτleast ω
  · intro τ' hτ'stop hτ'le hτ'opt
    refine hτmin τ' hτ'stop hτ'le ?_
    have h1 : Sandpile.Continuum.brownianDiscount (B x) P h T
        = -∫ ω, h (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P := by
      have := hτ'opt
      rw [show Sandpile.Continuum.brownianValue (B x) P h T x
          = h T x + Sandpile.Continuum.brownianDiscount (B x) P h T from rfl] at this
      linarith
    rw [show Sandpile.External.Snell.snellValue (B x) P (fun t y => -h t y) T
        = Sandpile.Continuum.brownianDiscount (B x) P h T from rfl, h1, integral_neg]
  · have hmem : (h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∈
        {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
          (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
          a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P} :=
      ⟨τ, hτstop, hτle, rfl⟩
    have hub : ∀ a ∈ {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
        (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
        a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P},
        a ≤ h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P := by
      rintro a ⟨σ, hσstop, hσle, rfl⟩
      have hmemσ : (∫ ω, -h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P) ∈
          Sandpile.External.Snell.attainable (B x) P (fun t y => -h t y) T :=
        ⟨σ, hσstop, hσle, rfl⟩
      have := hτgreat.2 hmemσ
      rw [integral_neg, integral_neg] at this
      linarith
    have : IsGreatest {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
        (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
        a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P}
        (h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) := ⟨hmem, hub⟩
    rw [hvalue, this.csSup_eq]
