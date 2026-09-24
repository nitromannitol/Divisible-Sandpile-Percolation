/-
The plane symmetries of `sandpile.tex:2103` acting on the ball field.

  "The unit-scale field `𝒳_1` is stationary, sign-symmetric, invariant under
   rotations by `π/2` and coordinate reflections."

A symmetry of the plane lattice is a permutation of the two coordinates, a sign
on each, and a translation (`Sandpile.Continuum.PlaneSymmetry`).  It lifts to
`ℝ^d` by acting on the first two coordinates and fixing the rest; the lift is an
isometry, it preserves Lebesgue measure, and it carries `planePoint u` to
`planePoint (T u)`.  Since the ball kernel sees the ambient point only through
its distance to the centre, the change of variables along the lift shows that
the covariances of the ball field at `T u, T v` and at `u, v` agree; the sign on
the values contributes `ε² = 1`, and both fields are centred.

What is left to turn that into the equality of laws that
`Sandpile.Continuum.IsSymmetricField` asks for is the general fact that a centred
Gaussian process is determined in law by its covariance.  That fact is not the
paper's and not cited by it; it is standard, and it is carried as the explicit
hypothesis `Sandpile.External.GaussianLawDeterminedByCovariance`, which is also
requested of the shared library.
-/
import Sandpile.Support.CrossBallMemLp
import Sandpile.External.GaussianLawCovariance

open MeasureTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

open Sandpile.Continuum

/-- A sign, `1` or `-1`, as an isometry of the line. -/
noncomputable def sgnIso (a : ℝ) : ℝ ≃ₗᵢ[ℝ] ℝ :=
  if a = -1 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

theorem sgnIso_apply {a : ℝ} (h : a = 1 ∨ a = -1) (x : ℝ) : sgnIso a x = a * x := by
  rcases h with rfl | rfl
  · rw [sgnIso, if_neg (by norm_num)]
    simp
  · rw [sgnIso, if_pos rfl]
    simp

/-- The permutation of the coordinates of `ℝ^d` induced by a plane symmetry: its
permutation of the two plane coordinates, and the identity on the rest. -/
def liftPerm (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) : Equiv.Perm (Fin d) :=
  if T.perm 0 = 0 then Equiv.refl _ else Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩

theorem perm_fin_two_of_zero (T : PlaneSymmetry) (h : T.perm 0 = 0) : T.perm 1 = 1 := by
  by_contra hne
  have h1 : T.perm 1 = 0 := by omega
  have := T.perm.injective (h.trans h1.symm)
  exact absurd this (by decide)

theorem perm_fin_two_of_ne (T : PlaneSymmetry) (h : T.perm 0 ≠ 0) :
    T.perm 0 = 1 ∧ T.perm 1 = 0 := by
  have h0 : T.perm 0 = 1 := by omega
  refine ⟨h0, ?_⟩
  by_contra hne
  have h1 : T.perm 1 = 1 := by omega
  have := T.perm.injective (h0.trans h1.symm)
  exact absurd this (by decide)

theorem liftPerm_coe_lt (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) (k : Fin 2) :
    ((liftPerm d hd T ⟨(k : ℕ), by omega⟩ : Fin d) : ℕ) = ((T.perm k : Fin 2) : ℕ) := by
  unfold liftPerm
  by_cases h : T.perm 0 = 0
  · rw [if_pos h]
    fin_cases k
    · simpa using congrArg (fun j : Fin 2 => (j : ℕ)) h.symm
    · simpa using congrArg (fun j : Fin 2 => (j : ℕ)) (perm_fin_two_of_zero T h).symm
  · rw [if_neg h]
    obtain ⟨h0, h1⟩ := perm_fin_two_of_ne T h
    fin_cases k
    · rw [show ((⟨(0 : ℕ), by omega⟩ : Fin d)) = (⟨0, by omega⟩ : Fin d) from rfl,
        Equiv.swap_apply_left]
      simpa using congrArg (fun j : Fin 2 => (j : ℕ)) h0.symm
    · rw [show ((⟨(1 : ℕ), by omega⟩ : Fin d)) = (⟨1, by omega⟩ : Fin d) from rfl,
        Equiv.swap_apply_right]
      simpa using congrArg (fun j : Fin 2 => (j : ℕ)) h1.symm

theorem liftPerm_of_ge (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) {i : Fin d}
    (hi : ¬ ((i : ℕ) < 2)) : liftPerm d hd T i = i := by
  unfold liftPerm
  by_cases h : T.perm 0 = 0
  · rw [if_pos h]; rfl
  · rw [if_neg h]
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro hc; rw [hc] at hi; exact hi (by norm_num)
    · intro hc; rw [hc] at hi; exact hi (by norm_num)

/-- The signs a plane symmetry puts on the coordinates of `ℝ^d`. -/
noncomputable def liftSign (d : ℕ) (T : PlaneSymmetry) : Fin d → ℝ :=
  fun i => if h : (i : ℕ) < 2 then T.sign ⟨i, h⟩ else 1

theorem liftSign_eq_one_or (d : ℕ) (T : PlaneSymmetry) (i : Fin d) :
    liftSign d T i = 1 ∨ liftSign d T i = -1 := by
  unfold liftSign
  by_cases h : (i : ℕ) < 2
  · rw [dif_pos h]
    exact T.sign_eq _
  · rw [dif_neg h]
    exact Or.inl rfl

/-- The linear part of the lift of a plane symmetry to `ℝ^d`: it permutes the two
plane coordinates as the symmetry does and puts its signs on them. -/
noncomputable def liftLinear (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) :
    Sandpile.Continuum.Space d ≃ₗᵢ[ℝ] Sandpile.Continuum.Space d :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (liftPerm d hd T).symm).trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun i => sgnIso (liftSign d T i)))

theorem liftLinear_apply (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry)
    (y : Sandpile.Continuum.Space d) (i : Fin d) :
    liftLinear d hd T y i = liftSign d T i * y (liftPerm d hd T i) := by
  show sgnIso (liftSign d T i) (y (liftPerm d hd T i)) = _
  exact sgnIso_apply (liftSign_eq_one_or d T i) _

/-- The lift of a plane symmetry to `ℝ^d`. -/
noncomputable def liftSym (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry)
    (y : Sandpile.Continuum.Space d) : Sandpile.Continuum.Space d :=
  liftLinear d hd T y + planePoint (d := d) (WithLp.toLp 2 T.shift)

theorem liftSym_planePoint (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry)
    (u : Sandpile.Continuum.Space 2) :
    liftSym d hd T (planePoint (d := d) u) = planePoint (d := d) (T.toFun u) := by
  ext i
  show liftLinear d hd T (planePoint (d := d) u) i
      + planePoint (d := d) (WithLp.toLp 2 T.shift) i = planePoint (d := d) (T.toFun u) i
  rw [liftLinear_apply]
  by_cases h : (i : ℕ) < 2
  · have hp : ((liftPerm d hd T i : Fin d) : ℕ) = ((T.perm ⟨(i : ℕ), h⟩ : Fin 2) : ℕ) := by
      have := liftPerm_coe_lt d hd T ⟨(i : ℕ), h⟩
      simpa using this
    have hplane : (planePoint (d := d) u) (liftPerm d hd T i) = u (T.perm ⟨(i : ℕ), h⟩) := by
      have hlt : ((liftPerm d hd T i : Fin d) : ℕ) < 2 := by
        rw [hp]; exact (T.perm ⟨(i : ℕ), h⟩).isLt
      show (if h' : ((liftPerm d hd T i : Fin d) : ℕ) < 2 then
        u ⟨((liftPerm d hd T i : Fin d) : ℕ), h'⟩ else 0) = _
      rw [dif_pos hlt]
      have hfin : (⟨((liftPerm d hd T i : Fin d) : ℕ), hlt⟩ : Fin 2) = T.perm ⟨(i : ℕ), h⟩ :=
        Fin.ext hp
      rw [hfin]
    have hshift : (planePoint (d := d) (WithLp.toLp 2 T.shift)) i = T.shift ⟨(i : ℕ), h⟩ := by
      show (if h' : (i : ℕ) < 2 then (WithLp.toLp 2 T.shift) ⟨(i : ℕ), h'⟩ else 0) = _
      rw [dif_pos h]
    have hsign : liftSign d T i = T.sign ⟨(i : ℕ), h⟩ := by
      unfold liftSign
      rw [dif_pos h]
    have hrhs : (planePoint (d := d) (T.toFun u)) i = T.toFun u ⟨(i : ℕ), h⟩ := by
      show (if h' : (i : ℕ) < 2 then (T.toFun u) ⟨(i : ℕ), h'⟩ else 0) = _
      rw [dif_pos h]
    rw [hplane, hshift, hsign, hrhs, PlaneSymmetry.toFun_apply]
  · have hplane : (planePoint (d := d) u) (liftPerm d hd T i) = 0 := by
      have hge : ¬ ((liftPerm d hd T i : Fin d) : ℕ) < 2 := by
        rw [liftPerm_of_ge d hd T h]
        exact h
      show (if h' : ((liftPerm d hd T i : Fin d) : ℕ) < 2 then
        u ⟨((liftPerm d hd T i : Fin d) : ℕ), h'⟩ else 0) = 0
      rw [dif_neg hge]
    have hshift : (planePoint (d := d) (WithLp.toLp 2 T.shift)) i = 0 := by
      show (if h' : (i : ℕ) < 2 then (WithLp.toLp 2 T.shift) ⟨(i : ℕ), h'⟩ else 0) = 0
      rw [dif_neg h]
    have hrhs : (planePoint (d := d) (T.toFun u)) i = 0 := by
      show (if h' : (i : ℕ) < 2 then (T.toFun u) ⟨(i : ℕ), h'⟩ else 0) = 0
      rw [dif_neg h]
    rw [hplane, hshift, hrhs, mul_zero, add_zero]

theorem norm_liftSym_sub (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry)
    (a b : Sandpile.Continuum.Space d) :
    ‖liftSym d hd T a - liftSym d hd T b‖ = ‖a - b‖ := by
  have h : liftSym d hd T a - liftSym d hd T b = liftLinear d hd T (a - b) := by
    unfold liftSym
    rw [map_sub]
    abel
  rw [h, LinearIsometryEquiv.norm_map]

theorem measurePreserving_liftSym (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) :
    MeasurePreserving (liftSym d hd T)
      (volume : Measure (Sandpile.Continuum.Space d)) volume := by
  have h1 : MeasurePreserving (liftLinear d hd T)
      (volume : Measure (Sandpile.Continuum.Space d)) volume :=
    LinearIsometryEquiv.measurePreserving _
  have h2 : MeasurePreserving
      (fun y : Sandpile.Continuum.Space d => y + planePoint (d := d) (WithLp.toLp 2 T.shift))
      volume volume := measurePreserving_add_right volume _
  exact h2.comp h1

theorem measurableEmbedding_liftSym (d : ℕ) (hd : 2 ≤ d) (T : PlaneSymmetry) :
    MeasurableEmbedding (liftSym d hd T) := by
  have h1 : MeasurableEmbedding (liftLinear d hd T) :=
    (liftLinear d hd T).toHomeomorph.measurableEmbedding
  have h2 : MeasurableEmbedding
      (fun y : Sandpile.Continuum.Space d => y + planePoint (d := d) (WithLp.toLp 2 T.shift)) :=
    (Homeomorph.addRight (planePoint (d := d) (WithLp.toLp 2 T.shift))).measurableEmbedding
  exact h2.comp h1

/-- The covariance of the ball field at two points is unchanged by a
measure-preserving map of the ambient space that carries the two centres
correctly: the kernel sees the ambient point only through its distance to the
centre. -/
theorem cov_ballKernel_comp {d : ℕ} (s : ℝ) (Φ : Sandpile.Continuum.Space d → Sandpile.Continuum.Space d)
    (hmp : MeasurePreserving Φ volume volume) (hme : MeasurableEmbedding Φ)
    (u' v' u v : Sandpile.Continuum.Space 2)
    (hu : ∀ y, ‖planePoint (d := d) u' - Φ y‖ = ‖planePoint (d := d) u - y‖)
    (hv : ∀ y, ‖planePoint (d := d) v' - Φ y‖ = ‖planePoint (d := d) v - y‖) :
    ∫ y, ballKernel d s u' y * ballKernel d s v' y
      = ∫ y, ballKernel d s u y * ballKernel d s v y := by
  have h := hmp.integral_comp hme (fun y => ballKernel d s u' y * ballKernel d s v' y)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ballKernel d s u' (Φ y) * ballKernel d s v' (Φ y)
    = ballKernel d s u y * ballKernel d s v y
  unfold ballKernel
  rw [hu y, hv y]


/-- The covariance of the ball field is invariant under the plane symmetries of
`sandpile.tex:2103`: the lift of the symmetry to `ℝ^d` is an isometry that
preserves Lebesgue measure and carries the centre of one kernel to the centre of
the other, and the kernel sees the ambient point only through its distance to
its centre. -/
theorem cov_ballKernel_symmetry {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (T : PlaneSymmetry)
    (u v : Sandpile.Continuum.Space 2) :
    ∫ y, ballKernel d s (T.toFun u) y * ballKernel d s (T.toFun v) y
      = ∫ y, ballKernel d s u y * ballKernel d s v y := by
  refine cov_ballKernel_comp s (liftSym d hd T) (measurePreserving_liftSym d hd T)
    (measurableEmbedding_liftSym d hd T) (T.toFun u) (T.toFun v) u v ?_ ?_
  · intro y
    rw [← liftSym_planePoint d hd T u, norm_liftSym_sub]
  · intro y
    rw [← liftSym_planePoint d hd T v, norm_liftSym_sub]

/-- The same for the field itself, with the sign flip of the values included:
the two fields whose laws `Sandpile.Continuum.IsSymmetricField` compares are
centred Gaussian fields with the same covariance. -/
theorem cov_ballField_symmetry {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    (T : PlaneSymmetry) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (u v : Sandpile.Continuum.Space 2) :
    ∫ ω, (ε * ballField d W s (T.toFun u) ω) * (ε * ballField d W s (T.toFun v) ω) ∂P
      = ∫ ω, ballField d W s u ω * ballField d W s v ω ∂P := by
  have hd2 : 2 ≤ d := by rcases hd with rfl | rfl <;> norm_num
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hstep : ∫ ω, (ε * ballField d W s (T.toFun u) ω) * (ε * ballField d W s (T.toFun v) ω) ∂P
      = ∫ ω, ballField d W s (T.toFun u) ω * ballField d W s (T.toFun v) ω ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      show (ε * ballField d W s (T.toFun u) ω) * (ε * ballField d W s (T.toFun v) ω)
        = ballField d W s (T.toFun u) ω * ballField d W s (T.toFun v) ω
      have hrw : (ε * ballField d W s (T.toFun u) ω) * (ε * ballField d W s (T.toFun v) ω)
          = (ε * ε) * (ballField d W s (T.toFun u) ω * ballField d W s (T.toFun v) ω) := by
        ring
      rw [hrw, hε2, one_mul])
  rw [hstep]
  show ∫ ω, W (ballKernel d s (T.toFun u)) ω * W (ballKernel d s (T.toFun v)) ω ∂P
      = ∫ ω, W (ballKernel d s u) ω * W (ballKernel d s v) ω ∂P
  rw [hW.cov _ _ (memLp_ballKernel hd hs _) (memLp_ballKernel hd hs _),
    cov_ballKernel_symmetry hd2 s T u v,
    ← hW.cov _ _ (memLp_ballKernel hd hs _) (memLp_ballKernel hd hs _)]

/-- The two fields are also both centred. -/
theorem mean_ballField_symmetry {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s)
    (T : PlaneSymmetry) (ε : ℝ) (u : Sandpile.Continuum.Space 2) :
    ∫ ω, ε * ballField d W s (T.toFun u) ω ∂P = 0 := by
  rw [integral_const_mul]
  show ε * ∫ ω, W (ballKernel d s (T.toFun u)) ω ∂P = 0
  rw [hW.mean _ (memLp_ballKernel hd hs _), mul_zero]

/-- The ball field is symmetric in law, granted that a centred Gaussian field is
determined in law by its covariance.  Everything else is proved: both fields are
Gaussian, both are centred, and their covariances agree by the change of
variables `cov_ballField_symmetry`. -/
theorem isSymmetricField_ballField
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : d = 2 ∨ d = 3) {W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ}
    (hW : Sandpile.Continuum.IsWhiteNoise d W P) {s : ℝ} (hs : 0 < s) :
    Sandpile.Continuum.IsSymmetricField P (ballField d W s) := by
  intro T ε hε
  have hgauss := isGaussianProcess_ballField hW s
  refine hGauss Ω P (fun u ω => ε * ballField d W s (T.toFun u) ω) (ballField d W s)
    ((hgauss.comp_right T.toFun).smul (fun _ => ε)) hgauss
    (fun u => (hW.meas _ (memLp_ballKernel hd hs _)).const_mul ε)
    (fun u => hW.meas _ (memLp_ballKernel hd hs _))
    (fun u => mean_ballField_symmetry hd hW hs T ε u)
    (fun u => hW.mean _ (memLp_ballKernel hd hs _))
    (fun u v => cov_ballField_symmetry hd hW hs T hε u v)

end Sandpile.Frozen.FixedScaleCrossings
