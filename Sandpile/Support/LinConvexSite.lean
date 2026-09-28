import Sandpile.Frozen.ConvexLinearBound
import Sandpile.Support.LinL2Split
import LatticeProb.Prob.FiniteMarginal

/-!
# The convex-linear bound read on a finite set of sites of the lattice field

The frozen bound `Sandpile.Frozen.convex_linear_bound` is stated for a functional of `N`
independent real coordinates, while the tested field of the linearization argument is a
functional of the whole scenery `V → ℝ` that reads only the finitely many sites the
odometer can see. This file carries the bound across that gap: a measurable functional of
`V → ℝ` that reads only the sites of a finite set `S`, coordinatewise convex with right
derivatives between `0` and `b v` on `S`, obeys the same inequality under
`Measure.infinitePi`, with the sums running over `S`. The transport uses the reading map
`ω ↦ (ω (e j))_{j < |S|}`, which sends the infinite product measure to a finite one, and
its section `x ↦ (v ↦ if v ∈ S then x (S.equivFin v) else 0)`, which inverts it on the
coordinates the functional reads; the right derivative is local for the same reason the
functional is, since the derivative of a function is determined by the function.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- The universal constant of `lem:convex-linear-bound`. -/
noncomputable def convexLinearConst : ℝ := Classical.choose Sandpile.Frozen.convex_linear_bound

/-- `convexLinearConst` is positive, being the constant of `Sandpile.Frozen.convex_linear_bound`. -/
theorem convexLinearConst_pos : 0 < convexLinearConst :=
  (Classical.choose_spec Sandpile.Frozen.convex_linear_bound).1

/-- The defining property of `convexLinearConst`: the convex-linear bound of
`Sandpile.Frozen.convex_linear_bound`, unpacked as an explicit statement about a
measurable, coordinatewise convex functional `F` of `N` independent real coordinates
with right derivatives `D i` bounded between `0` and `b i`. -/
theorem convexLinearConst_spec :
    ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
      Integrable (fun z => z ^ 2) ν →
      ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
      ∀ D : Fin N → (Fin N → ℝ) → ℝ, (∀ i, Measurable (D i)) →
        (∀ (i : Fin N) (ξ : Fin N → ℝ),
          ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ξ i y)) →
        (∀ (i : Fin N) (ξ : Fin N → ℝ),
          HasDerivWithinAt (fun y => F (Function.update ξ i y)) (D i ξ)
            (Set.Ici (ξ i)) (ξ i)) →
      ∀ b : Fin N → ℝ,
        (∀ᵐ ξ ∂(Measure.pi fun _ : Fin N => ν), ∀ i : Fin N, 0 ≤ D i ξ ∧ D i ξ ≤ b i) →
        ∀ L : ℝ, 0 < L →
          ∫ ξ, (F ξ - (∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)) -
              ∑ i, (∫ η, D i η ∂(Measure.pi fun _ : Fin N => ν)) * ξ i) ^ 2
              ∂(Measure.pi fun _ : Fin N => ν) ≤
            convexLinearConst * L ^ 2 *
                (∑ i, variance (D i) (Measure.pi fun _ : Fin N => ν)) +
              convexLinearConst * Sandpile.truncatedGap ν L * ∑ i, b i ^ 2 :=
  (Classical.choose_spec Sandpile.Frozen.convex_linear_bound).2

variable {V : Type*} [DecidableEq V]

/-- The right derivative of a functional that reads only the sites of `S` reads
only those sites as well. -/
theorem local_deriv_of_local {S : Finset V} {F : (V → ℝ) → ℝ}
    (hloc : ∀ ω η : V → ℝ, (∀ v ∈ S, ω v = η v) → F ω = F η)
    {D : V → (V → ℝ) → ℝ}
    (hderiv : ∀ (v : V) (ω : V → ℝ),
      HasDerivWithinAt (fun y => F (Function.update ω v y)) (D v ω) (Set.Ici (ω v)) (ω v))
    {v : V} (hv : v ∈ S) (ω η : V → ℝ) (h : ∀ w ∈ S, ω w = η w) :
    D v ω = D v η := by
  have hfun : (fun y => F (Function.update ω v y)) = fun y => F (Function.update η v y) := by
    funext y
    refine hloc _ _ fun w hw => ?_
    by_cases hwv : w = v
    · subst hwv; simp
    · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]
      exact h w hw
  have hpt : ω v = η v := h v hv
  have h1 : D v ω = derivWithin (fun y => F (Function.update ω v y)) (Set.Ici (ω v)) (ω v) :=
    ((hderiv v ω).derivWithin (uniqueDiffWithinAt_Ici _)).symm
  have h2 : D v η = derivWithin (fun y => F (Function.update η v y)) (Set.Ici (η v)) (η v) :=
    ((hderiv v η).derivWithin (uniqueDiffWithinAt_Ici _)).symm
  rw [h1, h2, hfun, hpt]

/-- **`lem:convex-linear-bound` for a functional of the field that reads only a
finite set of sites.** -/
theorem convex_linear_bound_local
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (S : Finset V) (F : (V → ℝ) → ℝ) (hFm : Measurable F)
    (hloc : ∀ ω η : V → ℝ, (∀ v ∈ S, ω v = η v) → F ω = F η)
    (D : V → (V → ℝ) → ℝ) (hDm : ∀ v, Measurable (D v))
    (hconv : ∀ (v : V) (ω : V → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y))
    (hderiv : ∀ (v : V) (ω : V → ℝ),
      HasDerivWithinAt (fun y => F (Function.update ω v y)) (D v ω) (Set.Ici (ω v)) (ω v))
    (b : V → ℝ)
    (hDb : ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν), ∀ v ∈ S, 0 ≤ D v ω ∧ D v ω ≤ b v)
    (L : ℝ) (hL : 0 < L) :
    ∫ ω, (F ω - (∫ η, F η ∂(Measure.infinitePi fun _ : V => ν))
          - ∑ v ∈ S, (∫ η, D v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v) ^ 2
        ∂(Measure.infinitePi fun _ : V => ν)
      ≤ convexLinearConst * L ^ 2 *
          (∑ v ∈ S, variance (D v) (Measure.infinitePi fun _ : V => ν))
        + convexLinearConst * Sandpile.truncatedGap ν L * ∑ v ∈ S, b v ^ 2 := by
  classical
  set P : Measure (V → ℝ) := Measure.infinitePi (fun _ : V => ν) with hP
  haveI : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set k := S.card with hk
  set e : Fin k → V := fun j => ((S.equivFin.symm j : S) : V) with he
  have hein : ∀ j, e j ∈ S := fun j => (S.equivFin.symm j).2
  have heinj : Function.Injective e := by
    intro a c hac
    have : (S.equivFin.symm a) = (S.equivFin.symm c) := Subtype.ext hac
    exact S.equivFin.symm.injective this
  set T : (V → ℝ) → (Fin k → ℝ) := fun ω j => ω (e j) with hT
  have hTmeas : Measurable T := measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hTmap : P.map T = Measure.pi (fun _ : Fin k => ν) :=
    LatticeProb.infinitePi_map_comp ν e heinj
  set sp : (Fin k → ℝ) → (V → ℝ) :=
    fun x v => if h : v ∈ S then x (S.equivFin ⟨v, h⟩) else 0 with hsp
  have hspmeas : Measurable sp := by
    refine measurable_pi_lambda _ fun v => ?_
    by_cases hv : v ∈ S
    · simp only [hsp, hv, dif_pos]
      exact measurable_pi_apply _
    · simp only [hsp, hv, dif_neg, not_false_iff]
      exact measurable_const
  have hspe : ∀ (x : Fin k → ℝ) (j : Fin k), sp x (e j) = x j := by
    intro x j
    simp only [hsp, hein j, dif_pos]
    congr 1
    exact S.equivFin.apply_symm_apply j
  have hspT : ∀ (ω : V → ℝ) (v : V), v ∈ S → sp (T ω) v = ω v := by
    intro ω v hv
    simp only [hsp, hv, dif_pos, hT]
    congr 1
    exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨v, hv⟩)
  have hspupd : ∀ (x : Fin k → ℝ) (j : Fin k) (y : ℝ),
      sp (Function.update x j y) = Function.update (sp x) (e j) y := by
    intro x j y
    funext v
    by_cases hv : v = e j
    · subst hv
      rw [hspe, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hv]
      by_cases hvS : v ∈ S
      · have hne : S.equivFin ⟨v, hvS⟩ ≠ j := by
          intro hEq
          apply hv
          have := congrArg (fun m => ((S.equivFin.symm m : S) : V)) hEq
          simpa [he] using this
        simp only [hsp, hvS, dif_pos, Function.update_of_ne hne]
      · simp only [hsp, hvS, dif_neg, not_false_iff]
  set G : (Fin k → ℝ) → ℝ := fun x => F (sp x) with hG
  have hGm : Measurable G := hFm.comp hspmeas
  have hGT : ∀ ω : V → ℝ, G (T ω) = F ω := fun ω => hloc _ _ fun v hv => hspT ω v hv
  set D' : Fin k → (Fin k → ℝ) → ℝ := fun j x => D (e j) (sp x) with hD'
  have hD'm : ∀ j, Measurable (D' j) := fun j => (hDm (e j)).comp hspmeas
  have hD'T : ∀ (j : Fin k) (ω : V → ℝ), D' j (T ω) = D (e j) ω := by
    intro j ω
    exact local_deriv_of_local hloc hderiv (hein j) _ ω fun w hw => hspT ω w hw
  have hGconv : ∀ (j : Fin k) (x : Fin k → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => G (Function.update x j y) := by
    intro j x
    have : (fun y => G (Function.update x j y))
        = fun y => F (Function.update (sp x) (e j) y) := by
      funext y; simp only [hG, hspupd]
    rw [this]
    exact hconv (e j) (sp x)
  have hGderiv : ∀ (j : Fin k) (x : Fin k → ℝ),
      HasDerivWithinAt (fun y => G (Function.update x j y)) (D' j x) (Set.Ici (x j)) (x j) := by
    intro j x
    have hfun : (fun y => G (Function.update x j y))
        = fun y => F (Function.update (sp x) (e j) y) := by
      funext y; simp only [hG, hspupd]
    have hpt : sp x (e j) = x j := hspe x j
    have := hderiv (e j) (sp x)
    rw [hpt] at this
    rw [hfun]
    exact this
  have hD'b : ∀ᵐ x ∂(Measure.pi fun _ : Fin k => ν),
      ∀ j : Fin k, 0 ≤ D' j x ∧ D' j x ≤ b (e j) := by
    have hset : MeasurableSet {x : Fin k → ℝ | ∀ j : Fin k, 0 ≤ D' j x ∧ D' j x ≤ b (e j)} := by
      have : {x : Fin k → ℝ | ∀ j : Fin k, 0 ≤ D' j x ∧ D' j x ≤ b (e j)}
          = ⋂ j : Fin k, ({x | 0 ≤ D' j x} ∩ {x | D' j x ≤ b (e j)}) := by
        ext x; simp [Set.mem_iInter, Set.mem_setOf_eq, forall_and]
      rw [this]
      exact MeasurableSet.iInter fun j =>
        (measurableSet_le measurable_const (hD'm j)).inter
          (measurableSet_le (hD'm j) measurable_const)
    rw [← hTmap, ae_map_iff hTmeas.aemeasurable hset]
    filter_upwards [hDb] with ω hω
    intro j
    rw [hD'T j ω]
    exact hω (e j) (hein j)
  have hmain := convexLinearConst_spec k ν inferInstance hmean hsq G hGm D' hD'm hGconv hGderiv
    (fun j => b (e j)) hD'b L hL
  -- transport the three integrals and the variance
  have hint : ∀ f : (Fin k → ℝ) → ℝ, AEStronglyMeasurable f (Measure.pi fun _ : Fin k => ν) →
      ∫ x, f x ∂(Measure.pi fun _ : Fin k => ν) = ∫ ω, f (T ω) ∂P := by
    intro f hf
    rw [← hTmap, integral_map hTmeas.aemeasurable (by rwa [hTmap])]
  have hGmean : ∫ x, G x ∂(Measure.pi fun _ : Fin k => ν) = ∫ ω, F ω ∂P := by
    rw [hint G hGm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hGT ω)
  have hD'mean : ∀ j : Fin k,
      ∫ x, D' j x ∂(Measure.pi fun _ : Fin k => ν) = ∫ ω, D (e j) ω ∂P := by
    intro j
    rw [hint (D' j) (hD'm j).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hD'T j ω)
  have hD'var : ∀ j : Fin k,
      variance (D' j) (Measure.pi fun _ : Fin k => ν) = variance (D (e j)) P := by
    intro j
    rw [← hTmap, variance_map (by rw [hTmap]; exact (hD'm j).aemeasurable) hTmeas.aemeasurable]
    have : (D' j ∘ T) = D (e j) := by funext ω; exact hD'T j ω
    rw [this]
  have hsumS : ∀ f : V → ℝ, ∑ j : Fin k, f (e j) = ∑ v ∈ S, f v := by
    intro f
    rw [← Finset.sum_coe_sort S f]
    exact Fintype.sum_equiv S.equivFin.symm _ _ fun j => rfl
  have hLHS : ∫ x, (G x - (∫ η, G η ∂(Measure.pi fun _ : Fin k => ν)) -
        ∑ j, (∫ η, D' j η ∂(Measure.pi fun _ : Fin k => ν)) * x j) ^ 2
        ∂(Measure.pi fun _ : Fin k => ν)
      = ∫ ω, (F ω - (∫ η, F η ∂P) - ∑ v ∈ S, (∫ η, D v η ∂P) * ω v) ^ 2 ∂P := by
    rw [hint _ (by
      exact ((hGm.sub measurable_const).sub
        (Finset.measurable_sum _ fun j _ => measurable_const.mul
          (measurable_pi_apply j))).pow_const 2 |>.aestronglyMeasurable)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have h1 : G (T ω) = F ω := hGT ω
    have h2 : ∑ j : Fin k, (∫ η, D' j η ∂(Measure.pi fun _ : Fin k => ν)) * (T ω) j
        = ∑ v ∈ S, (∫ η, D v η ∂P) * ω v := by
      have : ∀ j : Fin k, (∫ η, D' j η ∂(Measure.pi fun _ : Fin k => ν)) * (T ω) j
          = (fun v => (∫ η, D v η ∂P) * ω v) (e j) := by
        intro j; rw [hD'mean j]
      rw [Finset.sum_congr rfl fun j _ => this j]
      exact hsumS (fun v => (∫ η, D v η ∂P) * ω v)
    simp only [h1, hGmean, h2]
  rw [hLHS, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hD'var j)] at hmain
  rw [hsumS (fun v => variance (D v) P)] at hmain
  rw [hsumS (fun v => b v ^ 2)] at hmain
  exact hmain

/-- `η(L) = E[(ξ-ξ')² 1{|ξ-ξ'|>L}]` of `lem:convex-linear-bound` tends to zero as
`L → ∞`, by dominated convergence on the product of two copies of the one-site law. -/
theorem tendsto_truncatedGap (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun z => z ^ 2) ν) :
    Tendsto (Sandpile.truncatedGap ν) atTop (𝓝 0) := by
  have hfst : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (ν.prod ν) :=
    ((MeasureTheory.measurePreserving_fst (μ := ν) (ν := ν)).integrable_comp
      (by fun_prop)).mpr hsq
  have hsnd : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (ν.prod ν) :=
    ((MeasureTheory.measurePreserving_snd (μ := ν) (ν := ν)).integrable_comp
      (by fun_prop)).mpr hsq
  have hgint : Integrable (fun p : ℝ × ℝ => (p.1 - p.2) ^ 2) (ν.prod ν) := by
    refine Integrable.mono' ((hfst.const_mul 2).add (hsnd.const_mul 2)) (by fun_prop) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (p.1 + p.2)]
  have hmeasL : ∀ L : ℝ, Measurable
      (fun p : ℝ × ℝ => if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) := by
    intro L
    exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
      measurable_const
  have hintL : ∀ L : ℝ, Integrable
      (fun p : ℝ × ℝ => if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) (ν.prod ν) := by
    intro L
    refine Integrable.mono' hgint (hmeasL L).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs]
    by_cases h : L < |p.1 - p.2| <;> simp [h, abs_of_nonneg (sq_nonneg (p.1 - p.2)), sq_nonneg]
  have hrepr : ∀ L : ℝ, Sandpile.truncatedGap ν L
      = ∫ p, (if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) ∂(ν.prod ν) := by
    intro L
    rw [Sandpile.truncatedGap]
    exact integral_integral (f := fun y z : ℝ => if L < |y - z| then (y - z) ^ 2 else 0)
      (hintL L)
  have key : Tendsto (fun L : ℝ =>
      ∫ p, (if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0) ∂(ν.prod ν)) atTop (𝓝 0) := by
    have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := ν.prod ν) (l := (atTop : Filter ℝ))
      (F := fun (L : ℝ) (p : ℝ × ℝ) => if L < |p.1 - p.2| then (p.1 - p.2) ^ 2 else 0)
      (f := fun _ : ℝ × ℝ => (0 : ℝ))
      (bound := fun p : ℝ × ℝ => (p.1 - p.2) ^ 2)
      (Filter.Eventually.of_forall fun L => (hmeasL L).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun L => Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        by_cases h : L < |p.1 - p.2| <;>
          simp [h, abs_of_nonneg (sq_nonneg (p.1 - p.2)), sq_nonneg])
      hgint
      (Filter.Eventually.of_forall fun p => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop |p.1 - p.2|] with L hL
        rw [if_neg (not_lt.2 hL.le)])
    simpa using h
  exact (Filter.Tendsto.congr (fun L => (hrepr L).symm) key)


/-- The second moment of a linear functional of finitely many sites of the field, bounded
by the variance of the scenery times the square of the sum of the absolute values of the
coefficients.  This is `Sandpile.integral_sq_linear_le` read on `Measure.infinitePi`. -/
theorem integral_sq_linear_le_site {V : Type*} [DecidableEq V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (S : Finset V) (c : V → ℝ) :
    ∫ ω, (∑ v ∈ S, c v * ω v) ^ 2 ∂(Measure.infinitePi fun _ : V => ν)
      ≤ (∫ z, z ^ 2 ∂ν) * (∑ v ∈ S, |c v|) ^ 2 := by
  classical
  set P : Measure (V → ℝ) := Measure.infinitePi (fun _ : V => ν) with hP
  set k := S.card with hk
  set e : Fin k → V := fun j => ((S.equivFin.symm j : S) : V) with he
  have heinj : Function.Injective e := by
    intro a c' hac
    have : (S.equivFin.symm a) = (S.equivFin.symm c') := Subtype.ext hac
    exact S.equivFin.symm.injective this
  set T : (V → ℝ) → (Fin k → ℝ) := fun ω j => ω (e j) with hT
  have hTmeas : Measurable T := measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hTmap : P.map T = Measure.pi (fun _ : Fin k => ν) :=
    LatticeProb.infinitePi_map_comp ν e heinj
  have hsumS : ∀ f : V → ℝ, ∑ j : Fin k, f (e j) = ∑ v ∈ S, f v := by
    intro f
    rw [← Finset.sum_coe_sort S f]
    exact Fintype.sum_equiv S.equivFin.symm _ _ fun j => rfl
  have hmeasf : Measurable fun x : Fin k → ℝ => (∑ j, c (e j) * x j) ^ 2 :=
    (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)).pow_const 2
  have hint : ∫ x, (∑ j, c (e j) * x j) ^ 2 ∂(Measure.pi fun _ : Fin k => ν)
      = ∫ ω, (∑ v ∈ S, c v * ω v) ^ 2 ∂P := by
    rw [← hTmap, integral_map hTmeas.aemeasurable
      (by rw [hTmap]; exact hmeasf.aestronglyMeasurable)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg (fun t => t ^ 2) (hsumS (fun v => c v * ω v))
  rw [← hint]
  have h := integral_sq_linear_le ν hmean hsq (fun j => c (e j))
  rwa [hsumS (fun v => |c v|)] at h


/-- The right derivative of a coordinatewise convex functional of the field is a
measurable function of the field. -/
theorem measurable_rightDeriv_update {V : Type*} [DecidableEq V]
    (F : (V → ℝ) → ℝ) (hFm : Measurable F) (v : V)
    (hconv : ∀ ω : V → ℝ, ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y)) :
    Measurable (fun ω : V → ℝ =>
      derivWithin (fun y => F (Function.update ω v y)) (Set.Ioi (ω v)) (ω v)) := by
  have hupd : ∀ c : ℝ, Measurable (fun ω : V → ℝ => F (Function.update ω v (ω v + c))) := by
    intro c
    refine hFm.comp ?_
    refine measurable_pi_lambda _ fun w => ?_
    by_cases hw : w = v
    · subst hw
      simp only [Function.update_self]
      have h : Measurable fun ω : V → ℝ => ω w := measurable_pi_apply w
      exact h.add_const c
    · simp only [Function.update_of_ne hw]
      exact measurable_pi_apply w
  refine measurable_of_tendsto_metrizable' (atTop : Filter ℕ)
    (f := fun n : ℕ => fun ω : V → ℝ =>
      (F (Function.update ω v (ω v + 1 / ((n : ℝ) + 1))) - F ω) * ((n : ℝ) + 1))
    (fun n => ((hupd _).sub hFm).mul_const _) ?_
  rw [tendsto_pi_nhds]
  intro ω
  set g : ℝ → ℝ := fun y => F (Function.update ω v y) with hg
  have hgx : g (ω v) = F ω := by simp [hg]
  have hderiv : HasDerivWithinAt g (derivWithin g (Set.Ioi (ω v)) (ω v)) (Set.Ioi (ω v)) (ω v) :=
    (hconv ω).hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)
  have hslope : Tendsto (slope g (ω v)) (𝓝[>] (ω v))
      (𝓝 (derivWithin g (Set.Ioi (ω v)) (ω v))) := by
    have := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    simpa using this
  have hseq : Tendsto (fun n : ℕ => ω v + 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (ω v)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add h1
    · refine Filter.Eventually.of_forall fun n => ?_
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa using this
  have hcomp := hslope.comp hseq
  refine hcomp.congr fun n => ?_
  have hden : ω v + 1 / ((n : ℝ) + 1) - ω v = 1 / ((n : ℝ) + 1) := by ring
  simp only [Function.comp_apply, slope_def_field, hg, Function.update_eq_self, hden]
  field_simp

/-- The right derivative of `F` in the coordinate `v`, the paper's `∂_v^+F`. -/
noncomputable def rightDerivField {V : Type*} [DecidableEq V]
    (F : (V → ℝ) → ℝ) (v : V) (ω : V → ℝ) : ℝ :=
  derivWithin (fun y => F (Function.update ω v y)) (Set.Ioi (ω v)) (ω v)

/-- A coordinatewise convex functional has the right derivative at every point of
every coordinate. -/
theorem hasDerivWithinAt_rightDerivField {V : Type*} [DecidableEq V]
    (F : (V → ℝ) → ℝ) (v : V) (ω : V → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y)) :
    HasDerivWithinAt (fun y => F (Function.update ω v y)) (rightDerivField F v ω)
      (Set.Ici (ω v)) (ω v) :=
  hasDerivWithinAt_Ioi_iff_Ici.mp
    (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp))

/-- `rightDerivField F v` is measurable, whenever `F` is measurable and coordinatewise
convex in the coordinate `v`. -/
theorem measurable_rightDerivField {V : Type*} [DecidableEq V]
    (F : (V → ℝ) → ℝ) (hFm : Measurable F) (v : V)
    (hconv : ∀ ω : V → ℝ, ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y)) :
    Measurable (rightDerivField F v) :=
  measurable_rightDeriv_update F hFm v hconv

/-- **`lem:convex-linear-bound` for a coordinatewise convex functional of the
field that reads only a finite set of sites**, with the paper's right derivative
`∂_v^+F` supplied by convexity rather than assumed. -/
theorem convex_linear_bound_convex {V : Type*} [DecidableEq V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (S : Finset V) (F : (V → ℝ) → ℝ) (hFm : Measurable F)
    (hloc : ∀ ω η : V → ℝ, (∀ v ∈ S, ω v = η v) → F ω = F η)
    (hconv : ∀ (v : V) (ω : V → ℝ),
      ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y))
    (b : V → ℝ)
    (hDb : ∀ᵐ ω ∂(Measure.infinitePi fun _ : V => ν),
      ∀ v ∈ S, 0 ≤ rightDerivField F v ω ∧ rightDerivField F v ω ≤ b v)
    (L : ℝ) (hL : 0 < L) :
    ∫ ω, (F ω - (∫ η, F η ∂(Measure.infinitePi fun _ : V => ν))
          - ∑ v ∈ S, (∫ η, rightDerivField F v η ∂(Measure.infinitePi fun _ : V => ν)) * ω v) ^ 2
        ∂(Measure.infinitePi fun _ : V => ν)
      ≤ convexLinearConst * L ^ 2 *
          (∑ v ∈ S, variance (rightDerivField F v) (Measure.infinitePi fun _ : V => ν))
        + convexLinearConst * Sandpile.truncatedGap ν L * ∑ v ∈ S, b v ^ 2 :=
  convex_linear_bound_local ν hmean hsq S F hFm hloc (rightDerivField F)
    (fun v => measurable_rightDerivField F hFm v fun ω => hconv v ω) hconv
    (fun v ω => hasDerivWithinAt_rightDerivField F v ω (hconv v ω)) b hDb L hL

/-- The slope of the section tends to the right derivative from the right. -/
theorem tendsto_slope_rightDerivField (F : (V → ℝ) → ℝ) (v : V) (ω : V → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y)) :
    Tendsto (slope (fun y => F (Function.update ω v y)) (ω v)) (𝓝[>] (ω v))
      (𝓝 (rightDerivField F v ω)) := by
  have h := (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior (x := ω v) (by simp))
  have h2 := hasDerivWithinAt_iff_tendsto_slope.mp h
  simpa [rightDerivField] using h2

/-- A coordinatewise nondecreasing functional has nonnegative right derivative. -/
theorem rightDerivField_nonneg (F : (V → ℝ) → ℝ) (v : V) (ω : V → ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y))
    (hmono : ∀ y : ℝ, ω v ≤ y → F ω ≤ F (Function.update ω v y)) :
    0 ≤ rightDerivField F v ω := by
  refine ge_of_tendsto (tendsto_slope_rightDerivField F v ω hconv) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : ω v < y := hy
  have hval : F (Function.update ω v (ω v)) = F ω := by simp
  rw [slope_def_field, hval]
  exact div_nonneg (by linarith [hmono y hy'.le]) (by linarith)

/-- A coordinatewise `c`-Lipschitz functional has right derivative at most `c`. -/
theorem rightDerivField_le (F : (V → ℝ) → ℝ) (v : V) (ω : V → ℝ) (c : ℝ)
    (hconv : ConvexOn ℝ (Set.univ : Set ℝ) fun y => F (Function.update ω v y))
    (hlip : ∀ y : ℝ, ω v ≤ y → F (Function.update ω v y) - F ω ≤ c * (y - ω v)) :
    rightDerivField F v ω ≤ c := by
  refine le_of_tendsto (tendsto_slope_rightDerivField F v ω hconv) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : ω v < y := hy
  have hval : F (Function.update ω v (ω v)) = F ω := by simp
  rw [slope_def_field, hval, div_le_iff₀ (by linarith)]
  exact hlip y hy'.le

/-- The section of a convex functional in one coordinate is convex. -/
theorem convexOn_section {f : (V → ℝ) → ℝ}
    (hf : ConvexOn ℝ (Set.univ : Set (V → ℝ)) f) (ω : V → ℝ) (v : V) :
    ConvexOn ℝ (Set.univ : Set ℝ) fun y => f (Function.update ω v y) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ t₁ t₂ ht₁ ht₂ ht => ?_⟩
  have hup : Function.update ω v (t₁ • y₁ + t₂ • y₂)
      = t₁ • Function.update ω v y₁ + t₂ • Function.update ω v y₂ := by
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · simp only [Function.update_of_ne hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← add_mul, ht, one_mul]
  show f (Function.update ω v (t₁ • y₁ + t₂ • y₂)) ≤ _
  rw [hup]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ht₁ ht₂ ht

/-- The exact second moment `∫ (∑ i, d i * ζ i) ^ 2 = (∫ z ^ 2 ∂ν) * ∑ i, d i ^ 2` of a
linear functional of finitely many independent coordinates under `Measure.pi`, computed
from the variance of a sum of independent scaled copies of the one-site coordinate. -/
theorem integral_sq_linear_eq_pi (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    {N : ℕ} (d : Fin N → ℝ) :
    ∫ ζ, (∑ i, d i * ζ i) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
      = (∫ z, z ^ 2 ∂ν) * ∑ i, d i ^ 2 := by
  have hmem : ∀ i : Fin N, MemLp (fun z : ℝ => d i * z) 2 ν := fun i => hsq.const_mul (d i)
  have hvar : variance (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i) (Measure.pi fun _ : Fin N => ν)
      = ∑ i, variance (fun z : ℝ => d i * z) ν := by
    have h := variance_sum_pi (μ := fun _ : Fin N => ν) (X := fun i => fun z : ℝ => d i * z) hmem
    have hfun : (∑ i, fun ω : Fin N → ℝ => d i * ω i)
        = fun ξ : Fin N → ℝ => ∑ i, d i * ξ i := by
      funext ξ; simp [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hvi : variance (fun z : ℝ => z) ν = ∫ z, z ^ 2 ∂ν := by
    show variance (id : ℝ → ℝ) ν = ∫ z, z ^ 2 ∂ν
    rw [variance_eq_integral measurable_id.aemeasurable]
    simp only [id_eq]
    rw [hmean]
    simp
  have hsum : ∑ i, variance (fun z : ℝ => d i * z) ν = (∑ i, d i ^ 2) * ∫ z, z ^ 2 ∂ν := by
    rw [Finset.sum_congr rfl fun i _ => by rw [variance_const_mul, hvi], Finset.sum_mul]
  have heval : ∀ i : Fin N, ∫ ξ : Fin N → ℝ, ξ i ∂(Measure.pi fun _ : Fin N => ν) = ∫ z, z ∂ν :=
    fun i => integral_comp_eval (μ := fun _ : Fin N => ν) (i := i) (f := id)
      measurable_id.aestronglyMeasurable
  have hint : ∀ i : Fin N, Integrable (fun ξ : Fin N → ℝ => d i * ξ i)
      (Measure.pi fun _ : Fin N => ν) := by
    intro i
    have h1 : Integrable (fun ξ : Fin N → ℝ => (fun z : ℝ => d i * z) (ξ i))
        (Measure.pi fun _ : Fin N => ν) :=
      ((measurePreserving_eval (fun _ : Fin N => ν) i).integrable_comp
        (hmem i).aestronglyMeasurable).mpr ((hmem i).integrable (by norm_num))
    simpa using h1
  have hmean0 : ∫ ξ, (∑ i, d i * ξ i) ∂(Measure.pi fun _ : Fin N => ν) = 0 := by
    rw [integral_finsetSum Finset.univ (f := fun i (ξ : Fin N → ℝ) => d i * ξ i)
      (fun i _ => hint i)]
    simp only [integral_const_mul, heval, hmean, mul_zero, Finset.sum_const_zero]
  have hmeas : AEMeasurable (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i)
      (Measure.pi fun _ : Fin N => ν) :=
    (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)).aemeasurable
  have hsq_eq : ∫ ξ, (∑ i, d i * ξ i) ^ 2 ∂(Measure.pi fun _ : Fin N => ν)
      = variance (fun ξ : Fin N → ℝ => ∑ i, d i * ξ i) (Measure.pi fun _ : Fin N => ν) := by
    rw [variance_eq_integral hmeas, hmean0]
    simp
  rw [hsq_eq, hvar, hsum, mul_comm]

/-- The sharp form of the second moment of a linear functional of finitely many
sites: the `ℓ²` norm of the coefficients, not the square of their `ℓ¹` norm.
This is the form `eq:dgt4-linear-coefficient-replacement` needs, since the
paper's `R^{-4}` comes from `∑_x a_R(x)²` and not from `∑_x a_R(x)`. -/
theorem integral_sq_linear_eq_site {V : Type*} [DecidableEq V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (S : Finset V) (c : V → ℝ) :
    ∫ ω, (∑ v ∈ S, c v * ω v) ^ 2 ∂(Measure.infinitePi fun _ : V => ν)
      = (∫ z, z ^ 2 ∂ν) * ∑ v ∈ S, c v ^ 2 := by
  classical
  set P : Measure (V → ℝ) := Measure.infinitePi (fun _ : V => ν) with hP
  set k := S.card with hk
  set e : Fin k → V := fun j => ((S.equivFin.symm j : S) : V) with he
  have heinj : Function.Injective e := by
    intro x y hxy
    have : (S.equivFin.symm x) = (S.equivFin.symm y) := Subtype.ext hxy
    exact S.equivFin.symm.injective this
  set T : (V → ℝ) → (Fin k → ℝ) := fun ω j => ω (e j) with hT
  have hTmeas : Measurable T := measurable_pi_lambda _ fun j => measurable_pi_apply (e j)
  have hTmap : P.map T = Measure.pi (fun _ : Fin k => ν) :=
    LatticeProb.infinitePi_map_comp ν e heinj
  have hsumS : ∀ f : V → ℝ, ∑ j : Fin k, f (e j) = ∑ v ∈ S, f v := by
    intro f
    rw [← Finset.sum_coe_sort S f]
    exact Fintype.sum_equiv S.equivFin.symm _ _ fun j => rfl
  have hmeasf : Measurable fun x : Fin k → ℝ => (∑ j, c (e j) * x j) ^ 2 :=
    (Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)).pow_const 2
  have hint : ∫ x, (∑ j, c (e j) * x j) ^ 2 ∂(Measure.pi fun _ : Fin k => ν)
      = ∫ ω, (∑ v ∈ S, c v * ω v) ^ 2 ∂P := by
    rw [← hTmap, integral_map hTmeas.aemeasurable
      (by rw [hTmap]; exact hmeasf.aestronglyMeasurable)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact congrArg (fun t => t ^ 2) (hsumS (fun v => c v * ω v))
  rw [← hint, integral_sq_linear_eq_pi ν hmean hsq (fun j => c (e j)),
    hsumS (fun v => c v ^ 2)]

end Sandpile
