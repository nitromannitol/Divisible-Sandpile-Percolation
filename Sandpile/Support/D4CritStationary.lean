/-
Translation covariance of the finite-range field of `lem:d4-finite-range-lower-bound`
(`sandpile.tex:3861-3887`).  The killed Green field and the localized exit value
both commute with translation of the scenery, so the good-block process of the
coordinate plane is stationary under the i.i.d. scenery law, which is the
hypothesis of \citet[Corollary~1.4]{LSS} used at `sandpile.tex:3991-3995`.
-/
import Sandpile.Support.D4CritExitProb
import Sandpile.Support.LocalizationRecursion
import Sandpile.Support.ExitAverage
import Sandpile.Support.Translation

open MeasureTheory

noncomputable section
namespace Sandpile

variable {d : ℕ}

/-- The localized odometer commutes with translation of the scenery and of the
box. -/
theorem localizedOdometer_translate (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (y : Site d) : ∀ (t : ℕ) (x : Site d),
      localizedOdometer {w : Site d | w + y ∈ D} (shiftField y ζ) t x
        = localizedOdometer D ζ t (x + y) := by
  intro t
  induction t with
  | zero =>
      intro x
      rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
  | succ n ih =>
      intro x
      by_cases hx : x + y ∈ D
      · have hx' : x ∈ {w : Site d | w + y ∈ D} := hx
        rw [localizedOdometer_succ' hd _ _ n x hx',
          localizedOdometer_succ' hd D ζ n (x + y) hx]
        have hnb : Sandpile.avg
            (localizedOdometer {w : Site d | w + y ∈ D} (shiftField y ζ) n) x
            = Sandpile.avg (localizedOdometer D ζ n) (x + y) := by
          unfold Sandpile.avg LatticeProb.walkOp Sandpile.nbrSum
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          have e1 : x + unit i + y = x + y + unit i := by abel
          have e2 : x - unit i + y = x + y - unit i := by abel
          rw [ih (x + unit i), ih (x - unit i), e1, e2]
        rw [hnb]
        rfl
      · have hx' : x ∉ {w : Site d | w + y ∈ D} := hx
        rw [localizedOdometer_of_notMem _ _ _ hx',
          localizedOdometer_of_notMem D _ _ hx]

theorem measurable_pathTranslateFun (y : Site d) :
    Measurable (fun (X : ℕ → Site d) (k : ℕ) => y + X k) :=
  measurable_pi_lambda _ fun k => by fun_prop

/-- Translating the path space. -/
def pathTranslate (y : Site d) : (ℕ → Site d) ≃ᵐ (ℕ → Site d) where
  toFun X := fun k => y + X k
  invFun X := fun k => -y + X k
  left_inv := fun X => by funext k; simp
  right_inv := fun X => by funext k; simp
  measurable_toFun := measurable_pathTranslateFun y
  measurable_invFun := measurable_pathTranslateFun (-y)

theorem measurePreserving_pathTranslate (x y : Site d) :
    MeasurePreserving (pathTranslate y) (walkLaw d x) (walkLaw d (x + y)) := by
  refine ⟨(pathTranslate y).measurable, ?_⟩
  have hTx : Measurable (fun (X : ℕ → Site d) (k : ℕ) => x + X k) :=
    measurable_pi_lambda _ fun k => by fun_prop
  rw [walkLaw_translate d x, Measure.map_map (pathTranslate y).measurable hTx,
    walkLaw_translate d (x + y)]
  congr 1
  funext X k
  show y + (x + X k) = x + y + X k
  abel

/-- The cube about `x + y` seen from `y` is the cube about `x`. -/
theorem frCube_translate (x y : Site 4) (L : ℝ) :
    {w : Site 4 | y + w ∈ frCube (x + y) L} = frCube x L := by
  ext w
  simp only [frCube, Set.mem_setOf_eq, Pi.add_apply]
  constructor
  · intro h i
    have hi := h i
    have heq : ((y i + w i : ℤ) : ℝ) - ((x i + y i : ℤ) : ℝ)
        = ((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ) := by push_cast; ring
    rw [heq] at hi
    exact hi
  · intro h i
    have hi := h i
    have heq : ((y i + w i : ℤ) : ℝ) - ((x i + y i : ℤ) : ℝ)
        = ((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ) := by push_cast; ring
    rw [heq]
    exact hi

/-- The cube about `x + y` seen from `y`, written on the right. -/
theorem frCube_translate' (x y : Site 4) (L : ℝ) :
    {w : Site 4 | w + y ∈ frCube (x + y) L} = frCube x L := by
  ext w
  simp only [frCube, Set.mem_setOf_eq, Pi.add_apply]
  constructor
  · intro h i
    have hi := h i
    have heq : ((w i + y i : ℤ) : ℝ) - ((x i + y i : ℤ) : ℝ)
        = ((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ) := by push_cast; ring
    rw [heq] at hi
    exact hi
  · intro h i
    have hi := h i
    have heq : ((w i + y i : ℤ) : ℝ) - ((x i + y i : ℤ) : ℝ)
        = ((w i : ℤ) : ℝ) - ((x i : ℤ) : ℝ) := by push_cast; ring
    rw [heq]
    exact hi

/-- The killed Green field commutes with translation of the scenery. -/
theorem frGreenFieldTime_shiftField (r N : ℕ) (ζ : Site 4 → ℝ) (y x : Site 4) :
    frGreenFieldTime r N (shiftField y ζ) x = frGreenFieldTime r N ζ (x + y) := by
  unfold frGreenFieldTime
  refine tsum_congr fun u => ?_
  congr 1
  show ζ (x + u + y) = ζ (x + y + u)
  congr 1
  abel

/-- The localized exit value commutes with translation of the scenery. -/
theorem frExitValue_shiftField (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (ζ : Site 4 → ℝ)
    (y x : Site 4) :
    frExitValue Aex Aloc r (shiftField y ζ) x = frExitValue Aex Aloc r ζ (x + y) := by
  haveI : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hmp := measurePreserving_pathTranslate (d := 4) x y
  have hemb : MeasurableEmbedding (pathTranslate (d := 4) y) :=
    (pathTranslate (d := 4) y).measurableEmbedding
  rw [frExitValue, frExitValue, ← hmp.integral_comp hemb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hexit : exitTime (frCube (x + y) (r : ℝ)) (pathTranslate (d := 4) y X)
      = exitTime (frCube x (r : ℝ)) X := by
    show exitTime (frCube (x + y) (r : ℝ)) (fun k => y + X k) = _
    rw [← exitTime_translate (frCube (x + y) (r : ℝ)) y X, frCube_translate x y (r : ℝ)]
  set n : ℕ := (exitTime (frCube x (r : ℝ)) X).toNat with hn
  by_cases hmem : exitTime (frCube x (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)
  · have hmem1 : X ∈ {X : ℕ → Site 4 |
        exitTime (frCube x (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)} := hmem
    have hmem2 : pathTranslate (d := 4) y X ∈ {X : ℕ → Site 4 |
        exitTime (frCube (x + y) (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)} := by
      simpa only [Set.mem_setOf_eq, hexit] using hmem
    have e1 : Set.indicator {X : ℕ → Site 4 |
          exitTime (frCube x (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
        (fun X : ℕ → Site 4 => localizedOdometer
          (frCube (X (exitTime (frCube x (r : ℝ)) X).toNat) (Aloc * r)) (shiftField y ζ) (r ^ 2)
          (X (exitTime (frCube x (r : ℝ)) X).toNat)) X
        = localizedOdometer (frCube (X n) (Aloc * r)) (shiftField y ζ) (r ^ 2) (X n) :=
      Set.indicator_of_mem hmem1 _
    have e2 : Set.indicator {X : ℕ → Site 4 |
          exitTime (frCube (x + y) (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
        (fun X : ℕ → Site 4 => localizedOdometer
          (frCube (X (exitTime (frCube (x + y) (r : ℝ)) X).toNat) (Aloc * r)) ζ (r ^ 2)
          (X (exitTime (frCube (x + y) (r : ℝ)) X).toNat)) (pathTranslate (d := 4) y X)
        = localizedOdometer
            (frCube ((pathTranslate (d := 4) y X)
              (exitTime (frCube (x + y) (r : ℝ)) (pathTranslate (d := 4) y X)).toNat)
              (Aloc * r)) ζ (r ^ 2)
            ((pathTranslate (d := 4) y X)
              (exitTime (frCube (x + y) (r : ℝ)) (pathTranslate (d := 4) y X)).toNat) :=
      Set.indicator_of_mem hmem2 _
    have hval : (pathTranslate (d := 4) y X)
        (exitTime (frCube (x + y) (r : ℝ)) (pathTranslate (d := 4) y X)).toNat
        = X n + y := by
      rw [hexit]
      show y + X n = X n + y
      abel
    have hkey := localizedOdometer_translate (d := 4) (by norm_num)
      (frCube (X n + y) (Aloc * r)) ζ y (r ^ 2) (X n)
    rw [frCube_translate' (X n) y (Aloc * r)] at hkey
    show Set.indicator _ _ X = Set.indicator _ _ (pathTranslate (d := 4) y X)
    rw [e1, e2, hval]
    exact hkey
  · have hmem1 : X ∉ {X : ℕ → Site 4 |
        exitTime (frCube x (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)} := hmem
    have hmem2 : pathTranslate (d := 4) y X ∉ {X : ℕ → Site 4 |
        exitTime (frCube (x + y) (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)} := by
      simpa only [Set.mem_setOf_eq, hexit] using hmem
    have e1 : Set.indicator {X : ℕ → Site 4 |
          exitTime (frCube x (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
        (fun X : ℕ → Site 4 => localizedOdometer
          (frCube (X (exitTime (frCube x (r : ℝ)) X).toNat) (Aloc * r)) (shiftField y ζ) (r ^ 2)
          (X (exitTime (frCube x (r : ℝ)) X).toNat)) X = 0 :=
      Set.indicator_of_notMem hmem1 _
    have e2 : Set.indicator {X : ℕ → Site 4 |
          exitTime (frCube (x + y) (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
        (fun X : ℕ → Site 4 => localizedOdometer
          (frCube (X (exitTime (frCube (x + y) (r : ℝ)) X).toNat) (Aloc * r)) ζ (r ^ 2)
          (X (exitTime (frCube (x + y) (r : ℝ)) X).toNat)) (pathTranslate (d := 4) y X) = 0 :=
      Set.indicator_of_notMem hmem2 _
    show Set.indicator _ _ X = Set.indicator _ _ (pathTranslate (d := 4) y X)
    rw [e1, e2]

end Sandpile
