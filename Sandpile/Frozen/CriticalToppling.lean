/-
Theorem of Section 3 of sandpile.tex, frozen.  `sandpile.tex:1730-1748`
(label `thm:critical-toppling`, with the standing hypotheses of
Subsection `ssec:expl-d123` stated at `sandpile.tex:1696-1701`):

  "Throughout this subsection, $d\leq3$, the scenery is i.i.d.,
   $\E\zeta(0)=0$, $0<\Var(\zeta(0))<\infty$, and $\E|\zeta(0)|^3<\infty$.

   [Lower tail at the critical scale]  Fix $\nu_0>0$ and $M<\infty$.  For every
   $a\in(0,4/(4-d))$ there are $c>0$ and $C<\infty$, depending only on $d$, $a$,
   $\nu_0$, and $M$, such that every i.i.d.\ mean-zero field with
   $\Var(\zeta(0))\geq\nu_0^2$, $\E|\zeta(0)|^3\leq M\,\Var(\zeta(0))^{3/2}$
   satisfies, for all $t\geq3$ and $L\geq2$ with $L^a\leq t/2$,
   $\P\bigl(u_t(0)\leq t^{(4-d)/4}/L\bigr)\leq CL^{-c}+C\cdot
   \{(\log t)^{3/4}t^{-1/4}L^{a/4}$ for $d\in\{1,3\}$,
   $(\log t)^{7/4}t^{-1/2}L^{a/2}$ for $d=2\}$."

The scenery `ζ` is carried by its one-site law `ν`, and the field itself by
`centeredMassLaw d ν`, the law of `σ = 1 + 2dζ`.  The dimension `d` is bound
first because the range `(0, 4/(4-d))` of `a` mentions it; then `ν₀` and `M`,
then `a`, then `c` and `C`, then the law, then `t` and `L`, exactly as the
paper orders them, so `c` and `C` are uniform over every law satisfying the two
moment bounds.  The threshold `L` is a real, not an integer, since the
corollary that follows the theorem applies it with `L = t^{β-γ}`.  The
probability is stated on the measure of the event in `ℝ≥0∞`, against
`ENNReal.ofReal` of the paper's right-hand side, so that no `toReal` junk value
can weaken it; `t ≥ 3` keeps `log t` positive.  Integrability of `|ζ(0)|³` is
carried as a hypothesis of its own so that the third-moment bound cannot be
satisfied by the junk value `∫ = 0` of a divergent integral.
-/
import Sandpile.Law
import Sandpile.External.BerryEsseen
import Sandpile.External.VarianceScale
import Sandpile.Support.CriticalAssembly

open MeasureTheory ProbabilityTheory Filter Topology

/-- The Berry--Esseen remainder of `eq:dlt4-green-lower-tail`: the factor that
multiplies `C` in the second summand, `(\log t)^{3/4}t^{-1/4}L^{a/4}` for
`d ∈ {1, 3}` and `(\log t)^{7/4}t^{-1/2}L^{a/2}` for `d = 2`. -/
noncomputable def Sandpile.lowerTailRemainder (d : ℕ) (t : ℕ) (L a : ℝ) : ℝ :=
  if d = 2 then
    Real.log t ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
  else
    Real.log t ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.critical_toppling
    (hBerryEsseen : Sandpile.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν₀ M : ℝ) (hν₀ : 0 < ν₀)
    (a : ℝ) (ha : 0 < a) (ha' : a < 4 / (4 - (d : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => |z| ^ 3) ν →
      ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
      ∀ (t : ℕ) (L : ℝ), 3 ≤ t → 2 ≤ L → L ^ a ≤ (t : ℝ) / 2 →
        Sandpile.centeredMassLaw d ν
            {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} ≤
          ENNReal.ofReal (C * L ^ (-c) + C * Sandpile.lowerTailRemainder d t L a)
-- FROZEN-STATEMENT-END
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    Sandpile.exists_critical_toppling_bound hVarScale hBerryEsseen d hd hd3 ν₀ M hν₀ a ha ha'
  refine ⟨c, C, hc, hC, ?_⟩
  intro ν hprob hmean hvar hvar' hint hν₀var hmom t L ht hL hLa
  haveI := hprob
  have hne0 : evariance (id : ℝ → ℝ) ν ≠ 0 := ne_of_gt hvar
  have hnetop : evariance (id : ℝ → ℝ) ν ≠ ⊤ := ne_of_lt hvar'
  have hvarR : 0 < variance (id : ℝ → ℝ) ν := by
    show 0 < (evariance (id : ℝ → ℝ) ν).toReal
    exact ENNReal.toReal_pos hne0 hnetop
  have hν₀R : ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν :=
    (ENNReal.ofReal_le_iff_le_toReal hnetop).mp hν₀var
  have hkey := hbound ν hprob hmean hvarR hint hν₀R hmom t L ht hL hLa
  have hlogt : (0 : ℝ) ≤ Real.log (t : ℝ) := Real.log_natCast_nonneg t
  have hL0R : (0 : ℝ) < L := by linarith
  have h2 : (0 : ℝ) ≤ Sandpile.lowerTailRemainder d t L a := by
    rw [Sandpile.lowerTailRemainder]
    split <;>
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hlogt _)
        (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL0R.le _)
  have h1 : (0 : ℝ) < L ^ (-c) := Real.rpow_pos_of_pos hL0R _
  have hrhs0 : (0 : ℝ) ≤ C * L ^ (-c) + C * Sandpile.lowerTailRemainder d t L a := by
    have := mul_nonneg hC.le h2
    nlinarith
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hrhs0).mpr ?_
  rw [Sandpile.lowerTailRemainder]
  exact hkey
