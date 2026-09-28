import Sandpile.Support.D23Box
import Sandpile.Support.LocalizationRecursion
import Sandpile.Support.OriginKilled
import Sandpile.Support.D4CritStationary

/-!
# The localized odometer field for the dimension-two and dimension-three argument

The localized odometer field of the dimension-two and dimension-three
percolation argument (`sandpile.tex:2600-2604`): the field
`u_{⌊R²T⌋}^{Q(x,R)}(x)` read in the coordinate plane, whose superlevel set at
`cR^{2-d/2}` is the paper's `𝒪_R`.  The three properties the block scheme needs
are collected here: the field is dominated by the odometer at the same time, it
commutes with translation of the scenery, and it reads the scenery only inside
its own box.
-/

open MeasureTheory

noncomputable section
namespace Sandpile

open scoped Classical

variable {d : ℕ}

/-- The localized odometer field of `sandpile.tex:2600-2604`, read in the
coordinate plane: `u_t^{Q(x,R)}(x)` at the plane site `x = planeSite u`. -/
def d23Field (d R t : ℕ) (ζ : Site d → ℝ) (u : Site 2) : ℝ :=
  localizedOdometer (d23Box R (planeSite u)) ζ t (planeSite u)

/-- The localized field is dominated by the odometer at the same time. -/
theorem d23Field_le_odometerOf (hd : 1 ≤ d) (R t : ℕ) (ζ : Site d → ℝ) (u : Site 2) :
    d23Field d R t ζ u ≤ odometerOf ζ t (planeSite u) :=
  localizedOdometer_le_full hd _ ζ t _

/-- The localized field `d23Field d R t` at the coarse site `u` is measurable in the
scenery, inherited from measurability of `localizedOdometer`. -/
theorem measurable_d23Field (hd : 1 ≤ d) (R t : ℕ) (u : Site 2) :
    Measurable (fun ζ : Site d → ℝ => d23Field d R t ζ u) :=
  measurable_localizedOdometer hd _ t _

/-- The localized field commutes with translation of the scenery. -/
theorem d23Field_shift (hd : 1 ≤ d) (R t : ℕ) (ζ : Site d → ℝ) (u c : Site 2) :
    d23Field d R t (shiftField (planeSite c) ζ) u = d23Field d R t ζ (u + c) := by
  have hadd : planeSite (d := d) (u + c) = planeSite (d := d) u + planeSite (d := d) c :=
    planeSite_add u c
  unfold d23Field
  rw [hadd, ← localizedOdometer_translate hd (d23Box R (planeSite (d := d) u
      + planeSite (d := d) c)) ζ (planeSite (d := d) c) t (planeSite (d := d) u),
    d23Box_translate]

/-- The scenery rebuilt from its restriction to `D`, by zero off `D`. -/
def extendOn (D : Set (Site d)) (ρ : D → ℝ) : Site d → ℝ :=
  fun y => if h : y ∈ D then ρ ⟨y, h⟩ else 0

/-- `extendOn D` is measurable, since each coordinate `y` is either the constant
function `0` (when `y ∉ D`) or a coordinate projection `ρ ↦ ρ ⟨y, h⟩` (when `y ∈ D`). -/
theorem measurable_extendOn (D : Set (Site d)) :
    Measurable (extendOn D : (D → ℝ) → Site d → ℝ) := by
  refine measurable_pi_lambda _ fun y => ?_
  by_cases h : y ∈ D
  · have he : (fun ρ : D → ℝ => extendOn D ρ y) = fun ρ : D → ℝ => ρ ⟨y, h⟩ := by
      funext ρ
      simp only [extendOn, dif_pos h]
    rw [he]
    exact measurable_pi_apply _
  · have he : (fun ρ : D → ℝ => extendOn D ρ y) = fun _ : D → ℝ => (0 : ℝ) := by
      funext ρ
      simp only [extendOn, dif_neg h]
    rw [he]
    exact measurable_const

/-- The localized odometer reads the scenery only inside its own box. -/
theorem localizedOdometer_congr_on (hd : 1 ≤ d) (D : Set (Site d)) (ζ ξ : Site d → ℝ)
    (h : ∀ y ∈ D, ζ y = ξ y) : ∀ (t : ℕ) (x : Site d),
      localizedOdometer D ζ t x = localizedOdometer D ξ t x := by
  intro t
  induction t with
  | zero =>
      intro x
      rw [localizedOdometer_zero hd, localizedOdometer_zero hd]
  | succ n ih =>
      intro x
      by_cases hx : x ∈ D
      · rw [localizedOdometer_succ' hd D ζ n x hx, localizedOdometer_succ' hd D ξ n x hx]
        have hnb : Sandpile.avg (localizedOdometer D ζ n) x
            = Sandpile.avg (localizedOdometer D ξ n) x := by
          unfold Sandpile.avg LatticeProb.walkOp Sandpile.nbrSum
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ih (x + unit i), ih (x - unit i)]
        rw [hnb, h x hx]
      · rw [localizedOdometer_of_notMem D ζ _ hx, localizedOdometer_of_notMem D ξ _ hx]

/-- The localized odometer is measurable for the scenery inside its own box. -/
theorem measurable_comap_localizedOdometer (hd : 1 ≤ d) (D : Set (Site d)) (t : ℕ)
    (x : Site d) :
    Measurable[MeasurableSpace.comap (fun ζ : Site d → ℝ => Set.restrict D ζ) inferInstance]
      (fun ζ : Site d → ℝ => localizedOdometer D ζ t x) := by
  have hfac : (fun ζ : Site d → ℝ => localizedOdometer D ζ t x)
      = (fun ρ : D → ℝ => localizedOdometer D (extendOn D ρ) t x)
        ∘ (fun ζ : Site d → ℝ => Set.restrict D ζ) := by
    funext ζ
    refine localizedOdometer_congr_on hd D ζ (extendOn D (Set.restrict D ζ)) ?_ t x
    intro y hy
    simp only [extendOn, dif_pos hy, Set.restrict_apply]
  rw [hfac]
  exact ((measurable_localizedOdometer hd D t x).comp (measurable_extendOn D)).comp
    (Measurable.of_comap_le le_rfl)

/-- The good block at a coarse site reads the field only through its own box. -/
theorem measurable_comap_d23Field (hd : 1 ≤ d) (R t : ℕ) (u : Site 2) :
    Measurable[MeasurableSpace.comap
      (fun ζ : Site d → ℝ => Set.restrict (d23Box R (planeSite (d := d) u)) ζ) inferInstance]
      (fun ζ : Site d → ℝ => d23Field d R t ζ u) :=
  measurable_comap_localizedOdometer hd _ t _

end Sandpile
