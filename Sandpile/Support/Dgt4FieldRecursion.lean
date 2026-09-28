import Sandpile.Support.ExitGreen
import Sandpile.Support.InfiniteGreenField
import Sandpile.Support.RefinedIncrement
import Sandpile.Support.LinGaussField
import Sandpile.Support.MeanLocalization

/-!
# The recursion of the infinite Green field, and its optimal-stopping form

This file proves the recursion `V_∞ - PV_∞ = ζ` of the infinite Green field, the identity the
optimal-stopping representation of the first step of the Gaussian case rests on. The field is
the limit of the sums over the boxes `Q(0,n)`; the neighbour average commutes with each finite
sum, and the Green function is harmonic away from the diagonal, so the average of the partial
sum is the partial sum less the scenery at the site, as soon as the box contains that site, and
the recursion is the limit of that identity. From the recursion the file derives the
optimal-stopping representation `V_∞(x) - u_n(x) = inf_{τ≤n} 𝔼_x V_∞(X_τ)`, a coordinatewise
Lipschitz bound for `V_∞ - u_n` in the scenery, and the almost-sure form of the recursion at a
Gaussian scenery.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The partial sums converge to the field wherever they converge at all. -/
theorem tendsto_infiniteGreenFieldPartial {ζ : Site d → ℝ} {y : Site d}
    (h : ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L)) :
    Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop
      (𝓝 (infiniteGreenField ζ y)) := by
  rw [infiniteGreenField, dif_pos h]
  exact Classical.choose_spec h

/-- **The recursion for a partial sum.**  `PV_n(x)=V_n(x)-\zeta(x)` when the box contains
`x`, and `PV_n(x)=V_n(x)` when it does not. -/
theorem avg_infiniteGreenFieldPartial (hd : 3 ≤ d) (n : ℕ) (ζ : Site d → ℝ) (x : Site d) :
    Sandpile.avg (infiniteGreenFieldPartial n ζ) x
      = infiniteGreenFieldPartial n ζ x
        - Set.indicator (greenFieldBox d n) ζ x := by
  classical
  show LatticeProb.walkOp (fun y => ∑ z : greenFieldBox d n, green d y z * ζ z) x = _
  rw [show (fun y : Site d => ∑ z : greenFieldBox d n, green d y z * ζ z)
      = (fun y : Site d => ∑ z ∈ (Finset.univ : Finset (greenFieldBox d n)),
          (fun w : greenFieldBox d n => fun v : Site d => green d v (w : Site d) * ζ (w : Site d))
            z y) from rfl]
  rw [LatticeProb.walkOp_finsetSum]
  have hterm : ∀ z : greenFieldBox d n,
      LatticeProb.walkOp (fun v : Site d => green d v (z : Site d) * ζ (z : Site d)) x
        = (green d x (z : Site d) - (if x = (z : Site d) then 1 else 0)) * ζ (z : Site d) := by
    intro z
    rw [LatticeProb.walkOp_mul_const]
    congr 1
    exact avg_green hd x (z : Site d)
  rw [Finset.sum_congr rfl (fun z _ => hterm z)]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  by_cases hx : x ∈ greenFieldBox d n
  · rw [Set.indicator_of_mem hx,
      Finset.sum_eq_single (⟨x, hx⟩ : greenFieldBox d n) ?_ ?_]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Subtype.ext h.symm)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Set.indicator_of_notMem hx]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg (fun h : x = (b : Site d) => hx (by rw [h]; exact b.2)), zero_mul]

/-- **`V_\infty-PV_\infty=\zeta`** (`sandpile.tex:5037`), at every scenery whose Green field
converges at every site. -/
theorem avg_infiniteGreenField (hd : 3 ≤ d) (ζ : Site d → ℝ) (x : Site d)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L)) :
    Sandpile.avg (infiniteGreenField ζ) x = infiniteGreenField ζ x - ζ x := by
  classical
  have hconvpt : ∀ y : Site d, Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop
      (𝓝 (infiniteGreenField ζ y)) := fun y => tendsto_infiniteGreenFieldPartial (hconv y)
  have hsum : Tendsto (fun n => Sandpile.avg (infiniteGreenFieldPartial n ζ) x) atTop
      (𝓝 (Sandpile.avg (infiniteGreenField ζ) x)) := by
    show Tendsto (fun n => (∑ i : Fin d,
        (infiniteGreenFieldPartial n ζ (x + LatticeProb.unit i)
          + infiniteGreenFieldPartial n ζ (x - LatticeProb.unit i))) / (2 * (d : ℝ))) atTop
      (𝓝 ((∑ i : Fin d, (infiniteGreenField ζ (x + LatticeProb.unit i)
          + infiniteGreenField ζ (x - LatticeProb.unit i))) / (2 * (d : ℝ))))
    exact (tendsto_finsetSum _ fun i _ => (hconvpt _).add (hconvpt _)).div_const _
  have hev : ∀ᶠ n : ℕ in atTop, x ∈ greenFieldBox d n := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : Fin d, |x i| ≤ (N : ℤ) := by
      refine ⟨Finset.univ.sup fun i => (x i).natAbs, fun i => ?_⟩
      have h0 := Finset.le_sup (f := fun i : Fin d => (x i).natAbs) (Finset.mem_univ i)
      have h1 : ((x i).natAbs : ℤ) ≤ ((Finset.univ.sup fun i : Fin d => (x i).natAbs : ℕ) : ℤ) :=
        by exact_mod_cast h0
      rwa [Int.abs_eq_natAbs]
    filter_upwards [eventually_ge_atTop N] with n hn i
    exact le_trans (hN i) (by exact_mod_cast hn)
  have hrhs : Tendsto (fun n => infiniteGreenFieldPartial n ζ x
      - Set.indicator (greenFieldBox d n) ζ x) atTop (𝓝 (infiniteGreenField ζ x - ζ x)) := by
    refine Filter.Tendsto.congr' ?_ ((hconvpt x).sub (tendsto_const_nhds (x := ζ x)))
    filter_upwards [hev] with n hn
    rw [Set.indicator_of_mem hn]
  exact tendsto_nhds_unique
    (hsum.congr fun n => avg_infiniteGreenFieldPartial hd n ζ x) hrhs

/-- **`V_\infty-u_{n+1}=\min\{V_\infty,P(V_\infty-u_n)\}`** (`sandpile.tex:5047-5048`),
the recursion the first step of the Gaussian case iterates. -/
theorem infiniteGreenField_sub_odometer_succ (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) (x : Site d) :
    infiniteGreenField ζ x - odometerOf ζ (n + 1) x
      = min (infiniteGreenField ζ x)
        (Sandpile.avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) x) := by
  have hrec : Sandpile.avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) x
      = Sandpile.avg (infiniteGreenField ζ) x - Sandpile.avg (odometerOf ζ n) x :=
    LatticeProb.walkOp_sub _ _ x
  have hV := avg_infiniteGreenField hd ζ x hconv
  show infiniteGreenField ζ x - max 0 (ζ x + Sandpile.avg (odometerOf ζ n) x) = _
  rw [hrec, hV]
  rcases le_total 0 (ζ x + Sandpile.avg (odometerOf ζ n) x) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]
    ring
  · rw [max_eq_left h, min_eq_left (by linarith)]
    ring

/-- **The optimal-stopping representation of the field** (`sandpile.tex:5040-5041`): the
expected scenery sum up to a bounded stopping time is the field at the start less its
expectation at the stopping position. -/
theorem integral_sceneryPartialSum_eq_field_sub (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (x : Site d) (t : ℕ) {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x))
      = infiniteGreenField ζ x - ∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x) := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hzeta : (fun y : Site d => infiniteGreenField ζ y - Sandpile.avg (infiniteGreenField ζ) y)
      = ζ := by
    funext y
    rw [avg_infiniteGreenField hd ζ y hconv]
    ring
  have hp := Sandpile.integral_stopped_poisson hd1 x (infiniteGreenField ζ) t hτ hτt
  rw [hzeta] at hp
  rw [integral_add (Sandpile.integrable_stoppedScenery_walk hd1 x ζ t hτ hτt)
      (Sandpile.integrable_stopped_value hd1 x t (fun _ => infiniteGreenField ζ) hτ hτt)] at hp
  linarith

/-! ### The optimal-stopping form -/

/-- The expected field at a bounded stopping time is bounded below: the walk stays in the
box of radius `n` up to time `n`, and the field has a smallest value on that finite box. -/
theorem bddBelow_stoppedField (hd : 1 ≤ d) (ζ : Site d → ℝ) (x : Site d) (n : ℕ) :
    BddBelow {b : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      b = ∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x)} := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  have hne : (boxFinset x n).Nonempty := ⟨x, mem_boxFinset_iff.mpr (by simp [boxDist])⟩
  refine ⟨(boxFinset x n).inf' hne fun y => infiniteGreenField ζ y, ?_⟩
  rintro b ⟨τ, hτ, hτn, rfl⟩
  have hint := integrable_stopped_value hd x n (fun _ => infiniteGreenField ζ) hτ hτn
  have hle : ∀ᵐ X ∂(walkLaw d x),
      ((boxFinset x n).inf' hne fun y => infiniteGreenField ζ y)
        ≤ infiniteGreenField ζ (X (τ X)) := by
    filter_upwards [ae_boxDist_walk hd x] with X hX
    exact Finset.inf'_le _ (mem_boxFinset_iff.mpr (le_trans (hX (τ X)) (hτn X)))
  calc ((boxFinset x n).inf' hne fun y => infiniteGreenField ζ y)
      = ∫ _X, (boxFinset x n).inf' hne (fun y => infiniteGreenField ζ y) ∂(walkLaw d x) := by
        simp
    _ ≤ _ := integral_mono_ae (integrable_const _) hint hle

/-- **`V_\infty(x)-u_n(x)=\inf_{\tau\leq n}\E_x V_\infty(X_\tau)`**
(`sandpile.tex:5040-5041`). -/
theorem infiniteGreenField_sub_odometer_eq_sInf (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) (x : Site d) :
    infiniteGreenField ζ x - odometerOf ζ n x
      = sInf {b : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
          b = ∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x)} := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  set V : ℝ := infiniteGreenField ζ x with hV
  set S : Set ℝ := {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = ∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x)} with hS
  set T : Set ℝ := {b : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    b = ∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x)} with hT
  have hSne : S.Nonempty :=
    ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n, rfl⟩⟩
  have hTne : T.Nonempty :=
    ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n, rfl⟩⟩
  have hTbdd := bddBelow_stoppedField hd1 ζ x n
  obtain ⟨m, hm⟩ := id hTbdd
  have hSbdd : BddAbove S := by
    refine ⟨V - m, ?_⟩
    rintro a ⟨τ, hτ, hτn, rfl⟩
    have hb : (∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x)) ∈ T := ⟨τ, hτ, hτn, rfl⟩
    have := hm hb
    rw [integral_sceneryPartialSum_eq_field_sub hd ζ hconv x n hτ hτn]
    linarith
  have hsup : odometerOf ζ n x = sSup S :=
    (Sandpile.External.optimalStopping d hd1 ζ n x).1
  have h1 : sSup S ≤ V - sInf T := by
    refine csSup_le hSne ?_
    rintro a ⟨τ, hτ, hτn, rfl⟩
    have hb : (∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x)) ∈ T := ⟨τ, hτ, hτn, rfl⟩
    have := csInf_le hTbdd hb
    rw [integral_sceneryPartialSum_eq_field_sub hd ζ hconv x n hτ hτn]
    linarith
  have h2 : V - sSup S ≤ sInf T := by
    refine le_csInf hTne ?_
    rintro b ⟨τ, hτ, hτn, rfl⟩
    have ha : (∫ X, sceneryPartialSum ζ (τ X) X ∂(walkLaw d x)) ∈ S := ⟨τ, hτ, hτn, rfl⟩
    have := le_csSup hSbdd ha
    rw [integral_sceneryPartialSum_eq_field_sub hd ζ hconv x n hτ hτn] at this
    linarith
  rw [hsup]
  linarith

/-! ### The coordinatewise Lipschitz bound -/

/-- Changing the scenery at one site of the box changes a partial sum by the Green function
at that site. -/
theorem infiniteGreenFieldPartial_update (n : ℕ) (ζ : Site d → ℝ) (z : Site d) (v : ℝ)
    (hz : z ∈ greenFieldBox d n) (y : Site d) :
    infiniteGreenFieldPartial n (Function.update ζ z v) y
      = infiniteGreenFieldPartial n ζ y - green d y z * (ζ z - v) := by
  classical
  have key : (∑ w : greenFieldBox d n,
        green d y (w : Site d) * Function.update ζ z v (w : Site d))
      - (∑ w : greenFieldBox d n, green d y (w : Site d) * ζ (w : Site d))
      = green d y z * (v - ζ z) := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_eq_single (⟨z, hz⟩ : greenFieldBox d n)
        (fun b _ hb => by
          rw [Function.update_of_ne (fun h : (b : Site d) = z => hb (Subtype.ext h))]
          ring)
        (fun h => absurd (Finset.mem_univ _) h)]
    show green d y z * Function.update ζ z v z - green d y z * ζ z = _
    rw [Function.update_self]
    ring
  simp only [infiniteGreenFieldPartial]
  linarith

/-- The box eventually contains any given site. -/
theorem eventually_mem_greenFieldBox (z : Site d) :
    ∀ᶠ n : ℕ in atTop, z ∈ greenFieldBox d n := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : Fin d, |z i| ≤ (N : ℤ) := by
    refine ⟨Finset.univ.sup fun i => (z i).natAbs, fun i => ?_⟩
    have h0 := Finset.le_sup (f := fun i : Fin d => (z i).natAbs) (Finset.mem_univ i)
    have h1 : ((z i).natAbs : ℤ) ≤ ((Finset.univ.sup fun i : Fin d => (z i).natAbs : ℕ) : ℤ) :=
      by exact_mod_cast h0
    rwa [Int.abs_eq_natAbs]
  filter_upwards [eventually_ge_atTop N] with n hn i
  exact le_trans (hN i) (by exact_mod_cast hn)

/-- **The field is affine in one coordinate of the scenery**, with slope the Green function
at that site. -/
theorem infiniteGreenField_update (ζ : Site d → ℝ) (z : Site d) (v : ℝ) (y : Site d)
    (hconv : ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L)) :
    infiniteGreenField (Function.update ζ z v) y
      = infiniteGreenField ζ y - green d y z * (ζ z - v) := by
  have htend : Tendsto (fun n => infiniteGreenFieldPartial n (Function.update ζ z v) y) atTop
      (𝓝 (infiniteGreenField ζ y - green d y z * (ζ z - v))) := by
    refine Filter.Tendsto.congr' ?_
      ((tendsto_infiniteGreenFieldPartial hconv).sub
        (tendsto_const_nhds (x := green d y z * (ζ z - v))))
    filter_upwards [eventually_mem_greenFieldBox z] with n hn
    exact (infiniteGreenFieldPartial_update n ζ z v hn y).symm
  have hex : ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (Function.update ζ z v) y) atTop (𝓝 L) :=
    ⟨_, htend⟩
  exact tendsto_nhds_unique (tendsto_infiniteGreenFieldPartial hex) htend

/-- **The Green function is a supersolution**: its expectation at a bounded stopping time is
at most its value at the start. -/
theorem integral_green_stopped_le (hd : 3 ≤ d) (x z : Site d) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, green d (X (τ X)) z ∂(walkLaw d x)) ≤ green d x z := by
  classical
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hdelta : (fun w : Site d => green d w z - Sandpile.avg (fun w => green d w z) w)
      = fun w : Site d => if w = z then (1 : ℝ) else 0 := by
    funext w
    rw [avg_green hd w z]
    ring
  have hp := Sandpile.integral_stopped_poisson hd1 x (fun w => green d w z) t hτ hτt
  rw [hdelta] at hp
  rw [integral_add
      (Sandpile.integrable_stoppedScenery_walk hd1 x (fun w => if w = z then (1 : ℝ) else 0) t
        hτ hτt)
      (Sandpile.integrable_stopped_value hd1 x t (fun _ w => green d w z) hτ hτt)] at hp
  have hnn : (0 : ℝ) ≤ ∫ X, sceneryPartialSum (fun w : Site d => if w = z then (1 : ℝ) else 0)
      (τ X) X ∂(walkLaw d x) := by
    refine integral_nonneg fun X => ?_
    exact Finset.sum_nonneg fun k _ => by positivity
  linarith

/-- **`V_\infty-u_n` is Lipschitz in each coordinate of the scenery**, with coefficient the
Green function at that coordinate (`sandpile.tex:5058-5061`).  The field is affine in the
coordinate with slope `G(\cdot,z)`, the infimum over stopping times of two functions that
differ by at most a constant differs by at most that constant, and the expected slope at a
bounded stopping time is at most `G(x,z)` because `G(\cdot,z)` is a supersolution. -/
theorem abs_infiniteGreenField_sub_odometer_update_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (z : Site d) (v : ℝ) (n : ℕ) (x : Site d) :
    |(infiniteGreenField ζ x - odometerOf ζ n x)
        - (infiniteGreenField (Function.update ζ z v) x
            - odometerOf (Function.update ζ z v) n x)|
      ≤ green d x z * |ζ z - v| := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  set c : ℝ := green d x z * |ζ z - v| with hc
  have hcnn : 0 ≤ c := mul_nonneg (green_nonneg _ _) (abs_nonneg _)
  have hconv' : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m (Function.update ζ z v) y) atTop (𝓝 L) := by
    intro y
    refine ⟨infiniteGreenField ζ y - green d y z * (ζ z - v), ?_⟩
    refine Filter.Tendsto.congr' ?_
      ((tendsto_infiniteGreenFieldPartial (hconv y)).sub
        (tendsto_const_nhds (x := green d y z * (ζ z - v))))
    filter_upwards [eventually_mem_greenFieldBox z] with m hm
    exact (infiniteGreenFieldPartial_update m ζ z v hm y).symm
  have hsplit : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      (∫ X, infiniteGreenField (Function.update ζ z v) (X (τ X)) ∂(walkLaw d x))
        = (∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x))
          - (ζ z - v) * ∫ X, green d (X (τ X)) z ∂(walkLaw d x) := by
    intro τ hτ hτn
    have hfun : ∀ X : ℕ → Site d, infiniteGreenField (Function.update ζ z v) (X (τ X))
        = infiniteGreenField ζ (X (τ X)) - (ζ z - v) * green d (X (τ X)) z := by
      intro X
      rw [infiniteGreenField_update ζ z v (X (τ X)) (hconv _)]
      ring
    simp only [hfun]
    rw [integral_sub (integrable_stopped_value hd1 x n (fun _ => infiniteGreenField ζ) hτ hτn)
        ((integrable_stopped_value hd1 x n (fun _ w => green d w z) hτ hτn).const_mul _),
      integral_const_mul]
  have hgap : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      |(∫ X, infiniteGreenField ζ (X (τ X)) ∂(walkLaw d x))
        - ∫ X, infiniteGreenField (Function.update ζ z v) (X (τ X)) ∂(walkLaw d x)| ≤ c := by
    intro τ hτ hτn
    rw [hsplit τ hτ hτn]
    have hle := integral_green_stopped_le hd x z n hτ hτn
    have hnn : (0 : ℝ) ≤ ∫ X, green d (X (τ X)) z ∂(walkLaw d x) :=
      integral_nonneg fun X => green_nonneg _ _
    have : |(ζ z - v) * ∫ X, green d (X (τ X)) z ∂(walkLaw d x)| ≤ c := by
      rw [abs_mul, abs_of_nonneg hnn, hc, mul_comm (green d x z) |ζ z - v|]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    simpa using this
  have hkey : ∀ ξ η : Site d → ℝ,
      (∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun m => infiniteGreenFieldPartial m ξ y) atTop (𝓝 L)) →
      (∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
        (∫ X, infiniteGreenField ξ (X (τ X)) ∂(walkLaw d x))
          ≤ (∫ X, infiniteGreenField η (X (τ X)) ∂(walkLaw d x)) + c) →
      sInf {b : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
          b = ∫ X, infiniteGreenField ξ (X (τ X)) ∂(walkLaw d x)}
        ≤ sInf {b : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
          b = ∫ X, infiniteGreenField η (X (τ X)) ∂(walkLaw d x)} + c := by
    intro ξ η hξ hper
    rw [← sub_le_iff_le_add]
    refine le_csInf ⟨_, ⟨fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le n, rfl⟩⟩ ?_
    rintro b ⟨τ, hτ, hτn, rfl⟩
    have h1 := csInf_le (bddBelow_stoppedField hd1 ξ x n)
      (show (∫ X, infiniteGreenField ξ (X (τ X)) ∂(walkLaw d x)) ∈ _ from ⟨τ, hτ, hτn, rfl⟩)
    have h2 := hper τ hτ hτn
    linarith
  rw [infiniteGreenField_sub_odometer_eq_sInf hd ζ hconv n x,
    infiniteGreenField_sub_odometer_eq_sInf hd _ hconv' n x, abs_sub_le_iff]
  constructor
  · have := hkey ζ (Function.update ζ z v) hconv fun τ hτ hτn => by
      have h := abs_le.mp (hgap τ hτ hτn)
      linarith [h.2]
    linarith
  · have := hkey (Function.update ζ z v) ζ hconv' fun τ hτ hτn => by
      have h := abs_le.mp (hgap τ hτ hτn)
      linarith [h.1]
    linarith

/-! ### The recursion under the Gaussian scenery -/

/-- At a centred Gaussian scenery of any scale the box limit exists at every site at once. -/
theorem ae_forall_exists_tendsto_infiniteGreenFieldPartial (hd : 5 ≤ d) (c : ℝ) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)), ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n (fun z => c * ω z) y) atTop (𝓝 L) := by
  rw [ae_all_iff]
  intro y
  filter_upwards [ae_tendsto_greenPartialSum hd y] with ω hω
  have hpart : ∀ n : ℕ, infiniteGreenFieldPartial n (fun z => c * ω z) y
      = c * ∑ z ∈ boxFinset (0 : Site d) n, green d y z * ω z := by
    intro n
    rw [infiniteGreenFieldPartial,
      Finset.sum_set_coe (f := fun z : Site d => green d y z * (c * ω z)) (greenFieldBox d n),
      greenFieldBox_toFinset, Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ => by ring
  refine ⟨c * ⇑(LatticeProb.gaussIso (greenLp d hd y)) ω, ?_⟩
  simp only [hpart]
  exact hω.const_mul c

/-- **`V_\infty=\zeta+PV_\infty` at a Gaussian scenery**, at every site simultaneously. -/
theorem ae_avg_infiniteGreenField (hd : 5 ≤ d) (c : ℝ) :
    ∀ᵐ ω ∂(LatticeProb.gaussLaw (Site d)), ∀ x : Site d,
      Sandpile.avg (infiniteGreenField fun z => c * ω z) x
        = infiniteGreenField (fun z => c * ω z) x - c * ω x := by
  filter_upwards [ae_forall_exists_tendsto_infiniteGreenFieldPartial hd c] with ω hω x
  exact avg_infiniteGreenField (by omega) _ x hω

end Sandpile
