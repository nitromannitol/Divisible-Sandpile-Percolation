/-
Lemma of sandpile.tex representing the odometer minus the membrane field as an
optimal-stopping value, frozen.  `sandpile.tex:928-936`
(label `lem:difference-representation`):

  "For every $x\in\Z^d$ and every integer $t\geq0$,
   $u_t(x)-V_t(x) = \sup_{\tau\leq t}\mathbf E_x[-V_{t-\tau}(X_\tau)\mid\zeta]$,
   where the supremum is over stopping times of the walk."

The conditioning on `ζ` in the paper means that the identity holds for each
fixed scenery, so `ζ` is a deterministic real field bound before `t` and `x`,
and no measure on sceneries appears.  The paper's `u_t` is
`Sandpile.odometerOf ζ t`, its `V_t` is `Sandpile.membrane ζ t`, and the
supremum over stopping times bounded by `t` of `E_x` of a path functional is
`Sandpile.stoppingSup t x`, whose payoff sees both the stopping time and the
path, here `(k, X) ↦ -V_{t-k}(X_k)`.  The index `t - k` is a truncated
subtraction, which agrees with the paper because the supremum ranges only over
stopping times bounded by `t`.  The dimension carries `1 ≤ d` because at `d = 0`
the averaging operator behind `odometerOf` and `membrane` is a junk zero.

The paper's proof starts from the optimal-stopping representation, which is a
cited result rather than a theorem of the paper, so that result enters here as
the explicit hypothesis `hOS`, exactly as it does in the frozen `thm:RW`.
-/
import Sandpile.External.BPSH
import Sandpile.Support.Stopped

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.difference_representation
    (hOS : Sandpile.External.OptimalStopping)
    (d : ℕ) (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (t : ℕ) (x : Sandpile.Site d) :
    Sandpile.odometerOf ζ t x - Sandpile.membrane ζ t x =
      Sandpile.stoppingSup t x (fun k X => -(Sandpile.membrane ζ (t - k) (X k)))
-- FROZEN-STATEMENT-END
:= by
  rw [(hOS d hd ζ t x).1]
  show sSup {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, Sandpile.sceneryPartialSum ζ (τ X) X
        ∂(Sandpile.walkLaw d x)} - Sandpile.membrane ζ t x = _
  set A : Set ℝ := {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, Sandpile.sceneryPartialSum ζ (τ X) X
        ∂(Sandpile.walkLaw d x)} with hAdef
  have hAne : A.Nonempty :=
    ⟨_, ⟨fun _ => 0, Sandpile.isWalkStopping_zero, fun _ => Nat.zero_le t, rfl⟩⟩
  have hAbdd : BddAbove A := by
    refine ⟨t * Sandpile.sceneryBound x t ζ, ?_⟩
    rintro a ⟨τ, hτ, hτt, rfl⟩
    exact le_trans (le_abs_self _)
      (Sandpile.abs_integral_stoppedScenery_le hd x ζ t hτ hτt)
  have hB : {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, -(Sandpile.membrane ζ (t - τ X) (X (τ X)))
        ∂(Sandpile.walkLaw d x)} = (fun a => a - Sandpile.membrane ζ t x) '' A := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτt, rfl⟩
      exact ⟨_, ⟨τ, hτ, hτt, rfl⟩,
        (Sandpile.integral_neg_stoppedMembrane hd x ζ t hτ hτt).symm⟩
    · rintro ⟨b, ⟨τ, hτ, hτt, rfl⟩, rfl⟩
      exact ⟨τ, hτ, hτt, (Sandpile.integral_neg_stoppedMembrane hd x ζ t hτ hτt).symm⟩
  show _ = sSup {a : ℝ | ∃ τ : (ℕ → Sandpile.Site d) → ℕ, Sandpile.IsWalkStopping τ ∧
      (∀ X, τ X ≤ t) ∧ a = ∫ X, -(Sandpile.membrane ζ (t - τ X) (X (τ X)))
        ∂(Sandpile.walkLaw d x)}
  rw [hB, Sandpile.sSup_image_sub A hAne hAbdd]
