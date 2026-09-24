/-
A mod-two boundary or flux with two endpoints forces graph connectivity between them.
-/
import Mathlib

open scoped BigOperators
namespace Sandpile

lemma reachable_of_mod_two_flux {V E : Type*} [Fintype E]
    (G : SimpleGraph V) (src dst : E → V) (weight : E → ZMod 2) (a b : V)
    (hedge : ∀ e, weight e ≠ 0 → G.Reachable (src e) (dst e))
    (hflux : ∀ f : V → ZMod 2, (∑ e, weight e * (f (src e) + f (dst e))) = f a + f b) :
    G.Reachable a b := by
  classical
  by_contra hab
  let c (x : V) : ZMod 2 := if G.Reachable a x then 1 else 0
  have he (e : E) : weight e * (c (src e) + c (dst e)) = 0 := by
    by_cases hw : weight e = 0
    · rw [hw, zero_mul]
    have hh := hedge e hw
    have hiff : G.Reachable a (src e) ↔ G.Reachable a (dst e) :=
      ⟨fun h => h.trans hh, fun h => h.trans hh.symm⟩
    by_cases hs : G.Reachable a (src e)
    · simp [c, hs, hiff.mp hs, CharTwo.add_self_eq_zero]
    · have hd : ¬G.Reachable a (dst e) := fun hd => hs (hiff.mpr hd)
      simp [c, hs, hd]
  have hh := hflux c
  rw [Finset.sum_congr rfl (fun e _ => he e), Finset.sum_const_zero] at hh
  simp [c, hab] at hh

lemma reachable_of_mod_two_boundary {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : SimpleGraph V) (src dst : E → V) (weight : E → ZMod 2) (a b : V)
    (hedge : ∀ e, weight e ≠ 0 → G.Reachable (src e) (dst e))
    (hboundary : ∀ x, (∑ e, weight e *
      ((if src e = x then 1 else 0) + (if dst e = x then 1 else 0))) =
        (if x = a then 1 else 0) + (if x = b then 1 else 0)) : G.Reachable a b := by
  classical
  by_contra hab
  let c (x : V) : ZMod 2 := if G.Reachable a x then 1 else 0
  have he (e : E) : weight e * (c (src e) + c (dst e)) = 0 := by
    by_cases hw : weight e = 0
    · rw [hw, zero_mul]
    have hh := hedge e hw
    have hiff : G.Reachable a (src e) ↔ G.Reachable a (dst e) :=
      ⟨fun h => h.trans hh, fun h => h.trans hh.symm⟩
    by_cases hs : G.Reachable a (src e)
    · simp [c, hs, hiff.mp hs, CharTwo.add_self_eq_zero]
    · have hd : ¬G.Reachable a (dst e) := fun hd => hs (hiff.mpr hd)
      simp [c, hs, hd]
  have hsum : (∑ x, c x * (∑ e, weight e *
      ((if src e = x then 1 else 0) + (if dst e = x then 1 else 0)))) =
        ∑ e, weight e * (c (src e) + c (dst e)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    calc
      _ = ∑ x, weight e * ((if src e = x then c x else 0) + (if dst e = x then c x else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]; simp [eq_comm]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hboundary x])] at hsum
  have hleft : (∑ x, c x * ((if x = a then 1 else 0) + (if x = b then 1 else 0))) = 1 := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp [c, hab]
  rw [hleft, Finset.sum_congr rfl (fun e _ => he e), Finset.sum_const_zero] at hsum
  exact one_ne_zero hsum

end Sandpile
