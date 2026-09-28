import Sandpile.Support.Dgt4AGaussIndep

/-!
# Families of isonormal images as a Gaussian process

The isonormal picture of `Sandpile.Support.LinGaussIso` is reorganised here as a Gaussian
process, so that independence is available for infinite index families and not only for the
finite ones already treated. Every finite-dimensional marginal of a family of isonormal
images `LatticeProb.gaussIso` is a Gaussian vector, via the Gram-matrix identification
transported along an equivalence with `Fin m`, which makes `IsGaussianProcess` the right
vocabulary; consequently two such families with pairwise orthogonal coefficients are
independent as processes. The isonormal image of a unit coordinate family is identified with
that coordinate itself, connecting the abstract construction to the scenery's coordinates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {ι : Type*} [Countable ι]

omit [Countable ι] in
/-- The isonormal image of the unit coefficient family at a site is the coordinate
of the standard Gaussian product at that site. -/
theorem gaussIso_single [DecidableEq ι] (z : ι) :
    LatticeProb.gaussIso (lp.single 2 z (1 : ℝ)) = LatticeProb.gaussCoord z := by
  refine (LatticeProb.hasSum_gaussIso (lp.single 2 z (1 : ℝ))).unique ?_
  have h : ∀ i : ι, i ≠ z →
      ((lp.single 2 z (1 : ℝ) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i • LatticeProb.gaussCoord i
        = 0 := by
    intro i hi
    simp [hi]
  have hs := hasSum_single (f := fun i : ι =>
    ((lp.single 2 z (1 : ℝ) : lp (fun _ : ι => ℝ) 2) : ι → ℝ) i • LatticeProb.gaussCoord i) z h
  simpa using hs

omit [Countable ι] in
/-- The isonormal image of the unit coefficient family at a site is almost surely the
coordinate at that site. -/
theorem coeFn_gaussIso_single [DecidableEq ι] (z : ι) :
    ⇑(LatticeProb.gaussIso (lp.single 2 z (1 : ℝ))) =ᵐ[LatticeProb.gaussLaw ι]
      fun ω : ι → ℝ => ω z := by
  rw [gaussIso_single]
  exact (LatticeProb.memLp_eval z).coeFn_toLp

/-- A finite family of isonormal images is a Gaussian vector, at an arbitrary finite
index type. -/
theorem hasGaussianLaw_gaussIso_fintype {κ : Type*} [Fintype κ]
    (gs : κ → lp (fun _ : ι => ℝ) 2) :
    HasGaussianLaw (fun ω (i : κ) => ⇑(LatticeProb.gaussIso (gs i)) ω)
      (LatticeProb.gaussLaw ι) := by
  classical
  set e := Fintype.equivFin κ with he
  have h := hasGaussianLaw_gaussIso_pi (fun j : Fin (Fintype.card κ) => gs (e.symm j))
  have hL : HasGaussianLaw
      ((ContinuousLinearMap.pi (fun i : κ =>
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Fintype.card κ) => ℝ) (e i))) ∘
        (fun ω (j : Fin (Fintype.card κ)) => ⇑(LatticeProb.gaussIso (gs (e.symm j))) ω))
      (LatticeProb.gaussLaw ι) :=
    HasGaussianLaw.map_of_measurable _ h (by fun_prop)
  convert hL using 1
  funext ω
  funext i
  simp [he]

/-- **A family of isonormal images is a Gaussian process.** -/
theorem isGaussianProcess_gaussIso {T : Type*} (gs : T → lp (fun _ : ι => ℝ) 2) :
    IsGaussianProcess (fun t ω => ⇑(LatticeProb.gaussIso (gs t)) ω) (LatticeProb.gaussLaw ι) :=
  ⟨fun I => hasGaussianLaw_gaussIso_fintype (fun i : I => gs (i : T))⟩

/-- **Two families of isonormal images with orthogonal coefficients are independent as
processes.**  This is the splitting the conditioning of `sandpile.tex:5100-5104` rests on:
the residual family is independent of the direction that is being conditioned on. -/
theorem indepFun_gaussIso_process {S T : Type*} (fs : S → lp (fun _ : ι => ℝ) 2)
    (gs : T → lp (fun _ : ι => ℝ) 2) (h : ∀ s t, (inner ℝ (fs s) (gs t) : ℝ) = 0) :
    IndepFun (fun ω s => ⇑(LatticeProb.gaussIso (fs s)) ω)
      (fun ω t => ⇑(LatticeProb.gaussIso (gs t)) ω) (LatticeProb.gaussLaw ι) := by
  have hXY : IsGaussianProcess
      (Sum.elim (fun s ω => ⇑(LatticeProb.gaussIso (fs s)) ω)
        (fun t ω => ⇑(LatticeProb.gaussIso (gs t)) ω)) (LatticeProb.gaussLaw ι) := by
    have hall := isGaussianProcess_gaussIso (Sum.elim fs gs)
    convert hall using 1
    funext p
    cases p <;> rfl
  refine hXY.indepFun_of_covariance_eq_zero ?_ ?_ ?_
  · exact fun s => (Lp.aestronglyMeasurable _).aemeasurable
  · exact fun t => (Lp.aestronglyMeasurable _).aemeasurable
  · intro s t
    rw [covariance_gaussIso (fs s) (gs t)]
    exact h s t

end Sandpile
