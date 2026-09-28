import Sandpile.Walk
import Sandpile.External.HeatKernelBounds
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.Support.Stationary
import Sandpile.Support.MeanLocalization

/-!
# The frozen mean-localization corollary

This module states and proves the corollary "Mean localization" of
`sandpile.tex:1624-1634` (label `cor:mean-localization`):

  "Suppose that the scenery is stationary and $\E\zeta(0)^+<\infty$.  For every
   $0<T<\infty$ there are $C<\infty$ and $c>0$ such that, for all $A\geq1$, all
   $R\geq1$, all $t\leq TR^2$, and all $x\in\Z^d$,
   \[
     0\leq\E u_t(0)-\E u_t^{Q(x,AR)}(x)\leq Ce^{-cA^2/T}\E u_t(0)\, .
   \]"

Modelling.  The scenery is a random field on `ℤ^d` whose law `P` is an arbitrary
probability measure on `Site d → ℝ`.  Stationarity is `Sandpile.IsStationary d P`:
`P` is invariant under every lattice translation `ζ ↦ ζ(· + v)`.  No independence
is assumed, as in the paper.  The i.i.d. scenery with one-site law `ν` is the
instance `P = LatticeProb.iidLaw d ν`, which is stationary by
`Sandpile.isStationary_iidLaw`.  `\E\zeta(0)^+<\infty` is
`Integrable (fun ζ => max (ζ 0) 0) P`, the one-sided first moment of the paper;
nothing is assumed about the negative part.  `u_t` is `Sandpile.odometerOf ζ t`
and `u_t^{Q(x,AR)}` is `Sandpile.localizedOdometer (Sandpile.supBox x (A*R)) ζ t`.
Stationarity enters only to move the mean odometer from any site to the origin,
and integrability of `ζ(0)^+` only to make the odometer integrable.

`Q(x,L)` is the sup-norm box of the notation section, `sandpile.tex:677-683`,
`{y ∈ ℤ^d : max_i |y_i - x_i| ≤ L}` for a real radius `L`.  Since the
coordinates of `y` and `x` are integers, the condition `|y_i - x_i| ≤ L` is
equivalent to `|y_i - x_i| ≤ ⌊L⌋`, so `supBox` below compares integers with the
integer floor of the radius and no coercion of the box radius to a real is
needed.

Quantifier order.  `C` and `c` are bound after `T`, and before `A`, `R`, `t`
and `x`, as the paper orders them; the dimension and the scenery law are the
standing hypotheses of the corollary and precede `T`.  The constraint
`t ≤ TR^2` is compared in `ℝ` since `T` and `R` are real.

The dimension hypothesis `1 ≤ d` is the paper's standing assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology

/-- The sup-norm box `Q(x, L) = {y ∈ ℤ^d : max_i |y_i - x_i| ≤ L}` of the
notation section, at a real radius `L`, written with the integer floor of `L`. -/
def Sandpile.supBox {d : ℕ} (x : Sandpile.Site d) (L : ℝ) : Set (Sandpile.Site d) :=
  {y | ∀ i, |y i - x i| ≤ ⌊L⌋}

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.mean_localization
    (d : ℕ) (hd : 1 ≤ d)
    (P : Measure (Sandpile.Site d → ℝ)) (hprob : IsProbabilityMeasure P)
    (hstat : Sandpile.IsStationary d P)
    (hpos : Integrable (fun ζ => max (ζ 0) 0) P)
    (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ A : ℝ, 1 ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ t : ℕ, (t : ℝ) ≤ T * R ^ 2 →
        ∀ x : Sandpile.Site d,
          0 ≤ (∫ ζ, Sandpile.odometerOf ζ t 0 ∂P) -
                ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x ∂P ∧
            (∫ ζ, Sandpile.odometerOf ζ t 0 ∂P) -
                (∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x ∂P) ≤
              C * Real.exp (-(c * A ^ 2 / T)) *
                ∫ ζ, Sandpile.odometerOf ζ t 0 ∂P
-- FROZEN-STATEMENT-END
:= by
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  haveI := hprob
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, C₀, c₀, hC₀, hc₀, hbnd⟩ := hHeatKernel d hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro A hA R hR t htR x
  have hAR1 : (1 : ℝ) ≤ A * R := by nlinarith
  have hfloor : 1 ≤ ⌊A * R⌋ := by
    have : ((1 : ℤ) : ℝ) ≤ A * R := by exact_mod_cast hAR1
    exact Int.le_floor.mpr this
  have hx : x ∈ Sandpile.supBox x (A * R) := by
    show ∀ i, |x i - x i| ≤ ⌊A * R⌋
    intro i
    simp only [sub_self, abs_zero]
    omega
  set D : Set (Sandpile.Site d) := Sandpile.supBox x (A * R) with hD
  have hU0 : 0 ≤ ∫ ζ, Sandpile.odometerOf ζ t 0 ∂P :=
    integral_nonneg fun ζ => Sandpile.odometerOf_nonneg ζ t 0
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    have hL : (∫ ζ, Sandpile.localizedOdometer D ζ 0 x ∂P) = 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
        Sandpile.localizedOdometer_zero hd D ζ x)]
      exact integral_zero _ _
    have hUz : (∫ ζ, Sandpile.odometerOf ζ 0 0 ∂P) = 0 := by
      show (∫ _ : Sandpile.Site d → ℝ, (0 : ℝ) ∂P) = 0
      exact integral_zero _ _
    rw [hL, hUz]
    norm_num
  -- the exit probability, by the maximal-displacement estimate
  have hU := Sandpile.mean_localization_bound_of_stationary hd P hstat hpos D t x hx
  set R' : ℕ := (⌊A * R⌋).toNat + 1 with hR'def
  have hR'1 : 1 ≤ R' := by omega
  have hR'int : ((R' : ℕ) : ℤ) = ⌊A * R⌋ + 1 := by omega
  have hR'real : A * R < (R' : ℝ) := by
    have h2 : A * R < (⌊A * R⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : ((R' : ℕ) : ℝ) = (⌊A * R⌋ : ℝ) + 1 := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) hR'int
      push_cast at hc
      exact hc
    rw [h3]
    exact h2
  have hsub : {X : ℕ → Sandpile.Site d | Sandpile.exitNat D t X ≤ t}
      ⊆ {X : ℕ → Sandpile.Site d |
          ∃ k ≤ t, (R' : ℝ) ≤ Sandpile.External.latticeDist (X k) x} := by
    intro X hX
    obtain ⟨j, hj, hjD⟩ := Sandpile.exitNat_le_iff.mp hX
    have hex : ∃ i, ⌊A * R⌋ < |X j i - x i| := by
      by_contra hc
      push Not at hc
      exact hjD (fun i => hc i)
    obtain ⟨i, hi⟩ := hex
    refine ⟨j, hj, ?_⟩
    have hint : ((R' : ℕ) : ℤ) ≤ |X j i - x i| := by omega
    have hterm : ((R' : ℕ) : ℝ) ≤ |((X j i - x i : ℤ) : ℝ)| := by
      have hcast : (((|X j i - x i| : ℤ)) : ℝ) = |((X j i - x i : ℤ) : ℝ)| := by
        push_cast [Int.cast_abs]
        ring
      calc ((R' : ℕ) : ℝ) = (((R' : ℕ) : ℤ) : ℝ) := by push_cast; ring
        _ ≤ ((|X j i - x i| : ℤ) : ℝ) := by exact_mod_cast hint
        _ = |((X j i - x i : ℤ) : ℝ)| := hcast
    have hsq : ((R' : ℕ) : ℝ) ^ 2 ≤ ((X j i - x i : ℤ) : ℝ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ((R' : ℕ) : ℝ) := by positivity
      nlinarith [hterm, abs_nonneg ((X j i - x i : ℤ) : ℝ),
        sq_abs ((X j i - x i : ℤ) : ℝ)]
    have hsum : ((X j i - x i : ℤ) : ℝ) ^ 2
        ≤ ∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i' => ((X j i' - x i' : ℤ) : ℝ) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    show ((R' : ℕ) : ℝ) ≤ Real.sqrt (∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2)
    calc ((R' : ℕ) : ℝ) = Real.sqrt (((R' : ℕ) : ℝ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (le_trans hsq hsum)
  have hP : ((Sandpile.walkLaw d x)
        {X : ℕ → Sandpile.Site d | Sandpile.exitNat D t X ≤ t}).toReal
      ≤ C₀ * Real.exp (-c₀ * (R' : ℝ) ^ 2 / (t : ℝ)) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hR'1real : (1 : ℝ) ≤ (R' : ℝ) := by exact_mod_cast hR'1
    exact le_trans (measure_mono hsub) (hbnd t (R' : ℝ) ht1 hR'1real x)
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have hexp : Real.exp (-c₀ * (R' : ℝ) ^ 2 / (t : ℝ))
      ≤ Real.exp (-(c₀ * A ^ 2 / T)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : c₀ * A ^ 2 / T ≤ c₀ * (R' : ℝ) ^ 2 / (t : ℝ) := by
      rw [div_le_div_iff₀ hT ht0R]
      have hARnn : (0 : ℝ) ≤ A * R := by nlinarith
      have hsq : (A * R) ^ 2 ≤ (R' : ℝ) ^ 2 := by nlinarith [hR'real, hARnn]
      have h2 : c₀ * A ^ 2 * (t : ℝ) ≤ c₀ * A ^ 2 * (T * R ^ 2) :=
        mul_le_mul_of_nonneg_left htR (by positivity)
      have h3 : c₀ * A ^ 2 * (T * R ^ 2) = (c₀ * T) * (A * R) ^ 2 := by ring
      have h4 : (c₀ * T) * (A * R) ^ 2 ≤ (c₀ * T) * (R' : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have h5 : (c₀ * T) * (R' : ℝ) ^ 2 = c₀ * (R' : ℝ) ^ 2 * T := by ring
      linarith
    have hrw : -c₀ * (R' : ℝ) ^ 2 / (t : ℝ) = -(c₀ * (R' : ℝ) ^ 2 / (t : ℝ)) := by ring
    rw [hrw]
    exact neg_le_neg h1
  refine ⟨hU.1, le_trans hU.2 ?_⟩
  refine mul_le_mul_of_nonneg_right (le_trans hP ?_) hU0
  exact mul_le_mul_of_nonneg_left hexp hC₀.le
