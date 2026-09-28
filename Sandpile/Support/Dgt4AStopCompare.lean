import Sandpile.Support.Dgt4FieldRecursion
import Sandpile.Support.RefinedIncrement
import Sandpile.Support.Killed
import Sandpile.Support.LinLastVisit
import Sandpile.Support.OriginConcentration

/-!
**The stopping comparison of Step 3 of case (a)**
(`eq:dgt4-gaussian-stopping-comparison`, `sandpile.tex:5197-5210`).

On the event that the payoff `V_\infty(z)+\E u_n(0)` is positive at every site
`0<|z|\leq k+1`, the paper compares the optimal value with the value of the
strategy "stop at the first return to the origin": stopping at `\tau_0^+` gives one
of the two bounds and an arbitrary stopping time the other, and the two differ only
by the terminal value at time `k+1`.

The comparison is carried out here on the dynamic-programming recursion
`V_\infty-u_{m+1}=\min\{V_\infty,P(V_\infty-u_m)\}` of
`infiniteGreenField_sub_odometer_succ` rather than on the stopping representation
`eq:dgt4-infinite-field-stopping` itself, which is the same argument read forwards:
the value of the strategy "stop at the origin if it is reached within `j` steps"
is `-\theta_+P_x(\tau_0\leq j)` with `\theta_+=\max(\theta,0)` and `-\theta=W(0)`,
and the induction on `j` compares the two at every site of the box of radius
`k+1-j`.  The hitting probabilities `P_x(\tau_0\leq j)` are `srwHitBy`, whose
recursion off the origin is the neighbour average.

Index convention: the comparison below carries `P_0(\tau_0^+\leq k+1)`, one step
more than the paper's `P_0(\tau_0^+\leq k_n)`; both converge to `1-G(0,0)^{-1}`,
which is all that `eq:dgt4-gaussian-boundary-profile` reads off them, and the
terminal term is the paper's `P^{k_n+1}|V_\infty-u_{n-k_n}+\E u_n(0)|(0)` exactly.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- Monotonicity of the neighbour average at a single site: only the `2d`
neighbours of `x` are compared. -/
theorem avg_mono_le_nbr {f g : Site d → ℝ} {x : Site d}
    (hp : ∀ i : Fin d, f (x + unit i) ≤ g (x + unit i))
    (hm : ∀ i : Fin d, f (x - unit i) ≤ g (x - unit i)) :
    avg f x ≤ avg g x := by
  show (∑ i : Fin d, (f (x + LatticeProb.unit i) + f (x - LatticeProb.unit i)))
        / (2 * (d : ℝ))
      ≤ (∑ i : Fin d, (g (x + LatticeProb.unit i) + g (x - LatticeProb.unit i)))
        / (2 * (d : ℝ))
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Finset.sum_le_sum fun i _ => add_le_add (hp i) (hm i)

/-- A neighbour of `x` is at box distance at most `boxDist x 0 + 1` from the origin. -/
theorem boxDist_add_unit_origin_le (x : Site d) (i : Fin d) :
    boxDist (x + unit i) 0 ≤ boxDist x 0 + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hj : (x j - (0 : Site d) j).natAbs ≤ boxDist x 0 :=
    Finset.le_sup (f := fun j => (x j - (0 : Site d) j).natAbs) (Finset.mem_univ j)
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  show ((x + unit i) j - (0 : Site d) j).natAbs ≤ boxDist x 0 + 1
  simp only [Pi.add_apply] at *
  rcases hu with hu | hu <;> rw [hu] <;> omega

/-- A backward neighbour of `x` is at box distance at most `boxDist x 0 + 1` from the
origin, the mirror of `boxDist_add_unit_origin_le`. -/
theorem boxDist_sub_unit_origin_le (x : Site d) (i : Fin d) :
    boxDist (x - unit i) 0 ≤ boxDist x 0 + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have hj : (x j - (0 : Site d) j).natAbs ≤ boxDist x 0 :=
    Finset.le_sup (f := fun j => (x j - (0 : Site d) j).natAbs) (Finset.mem_univ j)
  have hu : unit i j = 0 ∨ unit i j = 1 := by
    by_cases h : i = j
    · right; simp [unit, h]
    · left; simp [unit, Pi.single_eq_of_ne (Ne.symm h)]
  show ((x - unit i) j - (0 : Site d) j).natAbs ≤ boxDist x 0 + 1
  simp only [Pi.sub_apply] at *
  rcases hu with hu | hu <;> rw [hu] <;> omega

/-- The dynamic-programming value never exceeds the payoff. -/
theorem dpValue_le_payoff {W : Site d → ℝ} {F : ℕ → Site d → ℝ}
    (hF0 : ∀ x, F 0 x = W x)
    (hFs : ∀ (m : ℕ) (x : Site d), F (m + 1) x = min (W x) (avg (F m) x))
    (m : ℕ) (x : Site d) : F m x ≤ W x := by
  cases m with
  | zero => exact le_of_eq (hF0 x)
  | succ r => rw [hFs r x]; exact min_le_left _ _

/-- The value after `j` further steps is at most the `j`-step average of the value:
running the walk for `j` steps and continuing optimally is one of the strategies. -/
theorem dpValue_le_avgIterate {W : Site d → ℝ} {F : ℕ → Site d → ℝ}
    (hFs : ∀ (m : ℕ) (x : Site d), F (m + 1) x = min (W x) (avg (F m) x))
    (j m : ℕ) (x : Site d) : F (m + j) x ≤ (avg^[j] (F m)) x := by
  induction j generalizing x with
  | zero => simp
  | succ r ih =>
      have hstep : F (m + (r + 1)) x = min (W x) (avg (F (m + r)) x) := by
        have hmr : m + (r + 1) = (m + r) + 1 := by omega
        rw [hmr, hFs (m + r) x]
      rw [hstep, Function.iterate_succ_apply']
      exact (min_le_right _ _).trans (Sandpile.avg_mono_le (fun y => ih y) x)

/-- **The stopping comparison**, in its inductive form: at every site of the box of
radius `k+1-j` the value differs from `-\theta_+P_x(\tau_0\leq j)` by at most the
`j`-step average of the absolute value of the earlier value. -/
theorem abs_dpValue_add_hit_le (hd : 1 ≤ d) {W : Site d → ℝ} {F : ℕ → Site d → ℝ}
    {θ : ℝ} {k : ℕ}
    (hF0 : ∀ x, F 0 x = W x)
    (hFs : ∀ (m : ℕ) (x : Site d), F (m + 1) x = min (W x) (avg (F m) x))
    (hW0 : W 0 = -θ)
    (hWnn : ∀ z : Site d, z ≠ 0 → boxDist z 0 ≤ k + 1 → 0 ≤ W z) :
    ∀ j ≤ k + 1, ∀ (m : ℕ) (x : Site d), boxDist x 0 + j ≤ k + 1 →
      |F (m + j) x + LatticeProb.srwHitBy d j x * max θ 0|
        ≤ (avg^[j] (fun y => |F m y|)) x := by
  set c : ℝ := max θ 0 with hcdef
  have hc0 : (0 : ℝ) ≤ c := le_max_right _ _
  have hθc : θ ≤ c := le_max_left _ _
  intro j
  induction j with
  | zero =>
      intro _ m x _
      simp only [Nat.add_zero, Function.iterate_zero, id_eq]
      rw [LatticeProb.srwHitBy_zero]
      by_cases hx : x = 0
      · subst hx
        rw [if_pos rfl, one_mul]
        have hle : F m 0 ≤ W 0 := dpValue_le_payoff hF0 hFs m 0
        rw [hW0] at hle
        rcases le_total θ 0 with hθ | hθ
        · have hc : c = 0 := by rw [hcdef]; exact max_eq_right hθ
          rw [hc, add_zero]
        · have hc : c = θ := by rw [hcdef]; exact max_eq_left hθ
          rw [hc, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
      · rw [if_neg hx, zero_mul, add_zero]
  | succ j ih =>
      intro hjk m x hx
      have hj1 : j ≤ k + 1 := by omega
      have hxk : boxDist x 0 ≤ k + 1 := by omega
      set A : Site d → ℝ := avg^[j] (fun z => |F m z|) with hAdef
      have hAnn : ∀ y : Site d, 0 ≤ A y := by
        intro y
        have h := avg_iterate_mono (d := d) j (f := fun _ : Site d => (0 : ℝ))
          (g := fun z => |F m z|) (fun z => abs_nonneg _) y
        rwa [avg_iterate_zero] at h
      have hAavg : 0 ≤ avg A x := avg_nonneg hAnn x
      set q : Site d → ℝ := LatticeProb.srwHitBy d j with hqdef
      set G : Site d → ℝ := fun y => q y * (-c) with hGdef
      have hnb : ∀ y : Site d, boxDist y 0 ≤ boxDist x 0 + 1 →
          G y - A y ≤ F (m + j) y ∧ F (m + j) y ≤ G y + A y := by
        intro y hy
        have h : |F (m + j) y + q y * c| ≤ A y := ih hj1 m y (by omega)
        have h2 := abs_le.mp h
        rw [hGdef]
        constructor
        · simp only
          nlinarith [h2.1, h2.2]
        · simp only
          nlinarith [h2.1, h2.2]
      have hL : avg (fun y => G y - A y) x ≤ avg (F (m + j)) x :=
        avg_mono_le_nbr (fun i => (hnb _ (boxDist_add_unit_origin_le x i)).1)
          (fun i => (hnb _ (boxDist_sub_unit_origin_le x i)).1)
      have hU : avg (F (m + j)) x ≤ avg (fun y => G y + A y) x :=
        avg_mono_le_nbr (fun i => (hnb _ (boxDist_add_unit_origin_le x i)).2)
          (fun i => (hnb _ (boxDist_sub_unit_origin_le x i)).2)
      have hGavg : avg G x = avg q x * (-c) := LatticeProb.walkOp_mul_const _ _ _
      have hLavg : avg (fun y => G y - A y) x = avg G x - avg A x :=
        LatticeProb.walkOp_sub _ _ _
      have hUavg : avg (fun y => G y + A y) x = avg G x + avg A x := avg_add _ _ _
      have hqnn : 0 ≤ avg q x := avg_nonneg (fun y => LatticeProb.srwHitBy_nonneg j y) x
      have hq1 : avg q x ≤ 1 := by
        have h := Sandpile.avg_mono_le (f := q) (g := fun _ : Site d => (1 : ℝ))
          (fun y => LatticeProb.srwHitBy_le_one (by omega) j y) x
        have hconst : avg (fun _ : Site d => (1 : ℝ)) x = 1 := LatticeProb.walkOp_const hd 1 x
        linarith
      have hFrec : F (m + (j + 1)) x = min (W x) (avg (F (m + j)) x) := by
        have hmj : m + (j + 1) = (m + j) + 1 := by omega
        rw [hmj, hFs (m + j) x]
      have hiter : (avg^[j + 1] (fun z => |F m z|)) x = avg A x := by
        rw [Function.iterate_succ_apply', hAdef]
      rw [hiter, hFrec]
      refine abs_le.mpr ⟨?_, ?_⟩
      · -- lower bound
        have hW : -(LatticeProb.srwHitBy d (j + 1) x * c) - avg A x ≤ W x := by
          by_cases hx0 : x = 0
          · subst hx0
            rw [LatticeProb.srwHitBy_succ_origin, one_mul, hW0]
            linarith
          · have h1 : (0 : ℝ) ≤ W x := hWnn x hx0 hxk
            have h2 : 0 ≤ LatticeProb.srwHitBy d (j + 1) x :=
              LatticeProb.srwHitBy_nonneg (j + 1) x
            nlinarith
        have hP : -(LatticeProb.srwHitBy d (j + 1) x * c) - avg A x ≤ avg (F (m + j)) x := by
          have hstep : avg q x * c ≤ LatticeProb.srwHitBy d (j + 1) x * c := by
            by_cases hx0 : x = 0
            · subst hx0
              rw [LatticeProb.srwHitBy_succ_origin, one_mul]
              nlinarith
            · have hsw : LatticeProb.srwHitBy d (j + 1) x = avg q x := by
                rw [hqdef]
                exact LatticeProb.srwHitBy_succ_of_ne hx0 j
              rw [hsw]
          have := hL
          rw [hLavg, hGavg] at this
          nlinarith
        have := le_min hW hP
        linarith [this]
      · -- upper bound
        by_cases hx0 : x = 0
        · subst hx0
          rw [LatticeProb.srwHitBy_succ_origin, one_mul]
          rcases le_total θ 0 with hθ | hθ
          · have hc : c = 0 := by rw [hcdef]; exact max_eq_right hθ
            rw [hc, add_zero]
            have h1 : F (m + (j + 1)) 0 ≤ (avg^[j + 1] (F m)) 0 :=
              dpValue_le_avgIterate hFs (j + 1) m 0
            have h2 : (avg^[j + 1] (F m)) 0 ≤ (avg^[j + 1] (fun z => |F m z|)) 0 :=
              avg_iterate_mono (j + 1) (fun z => le_abs_self _) 0
            rw [hiter] at h2
            have h3 : min (W 0) (avg (F (m + j)) 0) = F (m + (j + 1)) 0 := hFrec.symm
            rw [h3]
            linarith
          · have hc : c = θ := by rw [hcdef]; exact max_eq_left hθ
            have h1 : min (W 0) (avg (F (m + j)) 0) ≤ -θ :=
              le_of_le_of_eq (min_le_left _ _) hW0
            rw [hc]
            linarith
        · have hstep : LatticeProb.srwHitBy d (j + 1) x = avg q x := by
            rw [hqdef]
            exact LatticeProb.srwHitBy_succ_of_ne hx0 j
          rw [hstep]
          have h1 : min (W x) (avg (F (m + j)) x) ≤ avg (F (m + j)) x := min_le_right _ _
          have := hU
          rw [hUavg, hGavg] at this
          nlinarith

/-- **The stopping comparison** (`eq:dgt4-gaussian-stopping-comparison`,
`sandpile.tex:5196-5205`): after one averaging step at the origin the value differs from
`-\theta_+\P_0(\tau_0^+\leq k+1)` by at most the terminal value
`P^{k+1}|F_m|(0)`. -/
theorem abs_avg_dpValue_add_hit_le (hd : 1 ≤ d) {W : Site d → ℝ} {F : ℕ → Site d → ℝ}
    {θ : ℝ} {k : ℕ}
    (hF0 : ∀ x, F 0 x = W x)
    (hFs : ∀ (m : ℕ) (x : Site d), F (m + 1) x = min (W x) (avg (F m) x))
    (hW0 : W 0 = -θ)
    (hWnn : ∀ z : Site d, z ≠ 0 → boxDist z 0 ≤ k + 1 → 0 ≤ W z)
    (m : ℕ) :
    |avg (F (m + k)) 0 + avg (LatticeProb.srwHitBy d k) 0 * max θ 0|
      ≤ (avg^[k + 1] (fun y => |F m y|)) 0 := by
  set c : ℝ := max θ 0 with hcdef
  set A : Site d → ℝ := avg^[k] (fun z => |F m z|) with hAdef
  set q : Site d → ℝ := LatticeProb.srwHitBy d k with hqdef
  have hnb : ∀ y : Site d, boxDist y 0 ≤ 1 →
      F (m + k) y + q y * c ≤ A y ∧ -(A y) ≤ F (m + k) y + q y * c := by
    intro y hy
    have h : |F (m + k) y + q y * c| ≤ A y :=
      abs_dpValue_add_hit_le hd hF0 hFs hW0 hWnn k (by omega) m y (by omega)
    exact ⟨(abs_le.mp h).2, (abs_le.mp h).1⟩
  have hnb1 : ∀ i : Fin d, boxDist ((0 : Site d) + unit i) 0 ≤ 1 := by
    intro i
    have h := boxDist_add_unit_origin_le (0 : Site d) i
    rw [boxDist_self] at h
    omega
  have hnb2 : ∀ i : Fin d, boxDist ((0 : Site d) - unit i) 0 ≤ 1 := by
    intro i
    have h := boxDist_sub_unit_origin_le (0 : Site d) i
    rw [boxDist_self] at h
    omega
  have hup : avg (fun y => F (m + k) y + q y * c) 0 ≤ avg A 0 :=
    avg_mono_le_nbr (fun i => (hnb _ (hnb1 i)).1) (fun i => (hnb _ (hnb2 i)).1)
  have hlo : avg (fun y => -(A y)) 0 ≤ avg (fun y => F (m + k) y + q y * c) 0 :=
    avg_mono_le_nbr (fun i => (hnb _ (hnb1 i)).2) (fun i => (hnb _ (hnb2 i)).2)
  have hsplit : avg (fun y => F (m + k) y + q y * c) 0
      = avg (F (m + k)) 0 + avg q 0 * c := by
    rw [avg_add]
    congr 1
    exact LatticeProb.walkOp_mul_const _ _ _
  have hneg : avg (fun y => -(A y)) 0 = -(avg A 0) := by
    have h : avg (fun y => (0 : ℝ) - A y) 0 = avg (fun _ : Site d => (0 : ℝ)) 0 - avg A 0 :=
      LatticeProb.walkOp_sub _ _ _
    have h0 : avg (fun _ : Site d => (0 : ℝ)) 0 = 0 := LatticeProb.walkOp_const hd 0 0
    simpa [h0] using h
  have hiter : (avg^[k + 1] (fun y => |F m y|)) 0 = avg A 0 := by
    rw [Function.iterate_succ_apply', hAdef]
  rw [hiter]
  rw [hsplit] at hup hlo
  rw [hneg] at hlo
  exact abs_le.mpr ⟨hlo, hup⟩

/-- The stopping comparison at the infinite Green field: `F_r=V_\infty-u_r+a` obeys the
dynamic-programming recursion of `infiniteGreenField_sub_odometer_succ` with payoff
`W=V_\infty+a`, so `eq:dgt4-gaussian-stopping-comparison` holds whenever the payoff is
nonnegative at every site of the punctured box of radius `k+1`. -/
theorem abs_avg_infiniteGreenField_stop_compare (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (a : ℝ) (k : ℕ)
    (hWnn : ∀ z : Site d, z ≠ 0 → boxDist z 0 ≤ k + 1 → 0 ≤ infiniteGreenField ζ z + a)
    (m : ℕ) :
    |avg (fun y => infiniteGreenField ζ y - odometerOf ζ (m + k) y + a) 0
        + avg (LatticeProb.srwHitBy d k) 0 * max (-(infiniteGreenField ζ 0 + a)) 0|
      ≤ (avg^[k + 1] (fun y => |infiniteGreenField ζ y - odometerOf ζ m y + a|)) 0 := by
  have hd1 : 1 ≤ d := by omega
  refine abs_avg_dpValue_add_hit_le hd1 (W := fun y => infiniteGreenField ζ y + a)
    (F := fun r y => infiniteGreenField ζ y - odometerOf ζ r y + a) ?_ ?_ ?_ hWnn m
  · intro x
    show infiniteGreenField ζ x - odometerOf ζ 0 x + a = infiniteGreenField ζ x + a
    simp [odometerOf]
  · intro r x
    have h := infiniteGreenField_sub_odometer_succ hd ζ hconv r x
    have havg : avg (fun y => infiniteGreenField ζ y - odometerOf ζ r y + a) x
        = avg (fun y => infiniteGreenField ζ y - odometerOf ζ r y) x + a := by
      have h1 : avg (fun y => (infiniteGreenField ζ y - odometerOf ζ r y) + a) x
          = avg (fun y => infiniteGreenField ζ y - odometerOf ζ r y) x
            + avg (fun _ : Site d => a) x := avg_add _ _ _
      have hconst : avg (fun _ : Site d => a) x = a := LatticeProb.walkOp_const hd1 a x
      rw [h1, hconst]
    show infiniteGreenField ζ x - odometerOf ζ (r + 1) x + a
        = min (infiniteGreenField ζ x + a)
          (avg (fun y => infiniteGreenField ζ y - odometerOf ζ r y + a) x)
    rw [h, havg]
    exact (min_add_add_right _ _ _).symm
  · show infiniteGreenField ζ 0 + a = -(-(infiniteGreenField ζ 0 + a))
    ring

/-- A pointwise limit passes through the neighbour average, which is a finite sum. -/
theorem tendsto_avg_of_tendsto {f : ℕ → Site d → ℝ} {g : Site d → ℝ} (x : Site d)
    (h : ∀ y : Site d, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => avg (f k) x) atTop (𝓝 (avg g x)) := by
  show Tendsto (fun k => (∑ i : Fin d, (f k (x + unit i) + f k (x - unit i))) / (2 * (d : ℝ)))
    atTop (𝓝 ((∑ i : Fin d, (g (x + unit i) + g (x - unit i))) / (2 * (d : ℝ))))
  exact (tendsto_finsetSum _ fun i _ => (h _).add (h _)).div_const _

/-- **`\P_0(\tau_0^+\leq k+1)\to1-G(0,0)^{-1}`** (`sandpile.tex:5205-5207`), in the form the
comparison above carries it: the probability of returning to the origin within `k+1` steps
is the neighbour average of the hitting probabilities, and those increase to
`G(\cdot,0)/G(0,0)`, whose neighbour average at the origin is `1-G(0,0)^{-1}`. -/
theorem tendsto_avg_srwHitBy (hd : 3 ≤ d) :
    Tendsto (fun k : ℕ => avg (LatticeProb.srwHitBy d k) 0) atTop
      (𝓝 (1 - 1 / green d 0 0)) := by
  have hpt : ∀ y : Site d, Tendsto (fun k => LatticeProb.srwHitBy d k y) atTop
      (𝓝 (LatticeProb.srwHitProb d y)) := by
    intro y
    have hs := (LatticeProb.summable_srwFirstHit (d := d) (by omega) y).hasSum.tendsto_sum_nat
    exact hs.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim := tendsto_avg_of_tendsto (0 : Site d) hpt
  have hval : avg (LatticeProb.srwHitProb d) (0 : Site d) = 1 - 1 / green d 0 0 := by
    have hG : (0 : ℝ) < green d 0 0 :=
      lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
    have hfun : (LatticeProb.srwHitProb d) = fun y : Site d => green d y 0 * (green d 0 0)⁻¹ := by
      funext y
      rw [LatticeProb.srwHitProb_eq_green_ratio hd, ← green_origin_eq_srwGreenInf,
        ← green_origin_eq_srwGreenInf, green_symm (by omega) 0 y, div_eq_mul_inv]
    rw [hfun]
    have h1 : avg (fun y : Site d => green d y 0 * (green d 0 0)⁻¹) 0
        = avg (fun y : Site d => green d y 0) 0 * (green d 0 0)⁻¹ :=
      LatticeProb.walkOp_mul_const _ _ _
    have h2 : avg (fun y : Site d => green d y 0) 0 = green d 0 0 - 1 := by
      simpa using avg_green hd 0 (0 : Site d)
    rw [h1, h2]
    field_simp
  rwa [hval] at hlim

end Sandpile
