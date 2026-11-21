import JSP000930PositiveForcingProjectionPullback
import Mathlib.Order.UpperLower.CompleteLattice

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion

universe u v w

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

theorem mem_ro_iInf {A : Type u} [Preorder A] {I : Sort w}
    (f : I → RO A) (a : A) :
    a ∈ ((⨅ i, f i : RO A) : LowerSet A) ↔
      ∀ i, a ∈ (f i : LowerSet A) := by
  have e : ((⨅ i, f i : RO A) : LowerSet A) = ⨅ i, (f i : LowerSet A) :=
    Heyting.Regular.gi.gc.u_iInf
  rw [e, LowerSet.mem_iInf_iff]

theorem ForcingProjection.pull_iInf (F : ForcingProjection P Q)
    {I : Sort w} (f : I → RO Q) :
    F.pull (⨅ i, f i) = ⨅ i, F.pull (f i) := by
  apply Heyting.Regular.coe_injective
  ext p
  change F.toFun p ∈ ((⨅ i, f i : RO Q) : LowerSet Q) ↔
    p ∈ ((⨅ i, F.pull (f i) : RO P) : LowerSet P)
  rw [mem_ro_iInf f (F.toFun p), mem_ro_iInf (fun i => F.pull (f i)) p]
  rfl

theorem ForcingProjection.pull_iSup (F : ForcingProjection P Q)
    {I : Sort w} (f : I → RO Q) :
    F.pull (⨆ i, f i) = ⨆ i, F.pull (f i) := by
  calc
    F.pull (⨆ i, f i) = F.pull ((⨅ i, (f i)ᶜ)ᶜ) := by
      rw [compl_iInf]
      simp only [compl_compl]
    _ = ⨆ i, F.pull (f i) := by
      rw [F.pull_compl, F.pull_iInf, compl_iInf]
      simp only [F.pull_compl, compl_compl]

theorem ForcingProjection.pull_inf (F : ForcingProjection P Q)
    (U V : RO Q) : F.pull (U ⊓ V) = F.pull U ⊓ F.pull V := by
  apply Heyting.Regular.coe_injective
  ext p
  rfl

theorem ForcingProjection.pull_injective_of_weak_surj
    (F : ForcingProjection P Q)
    (h : ∀ q, ∃ p, F.toFun p ≤ q ∧ q ≤ F.toFun p) :
    Function.Injective F.pull := by
  intro U V huv
  apply Heyting.Regular.coe_injective
  ext q
  obtain ⟨p,hpq,hqp⟩ := h q
  have e : p ∈ (F.pull U : LowerSet P) ↔ p ∈ (F.pull V : LowerSet P) :=
    Iff.of_eq (congrArg (fun z : RO P => p ∈ (z : LowerSet P)) huv)
  change F.toFun p ∈ (U : LowerSet Q) ↔ F.toFun p ∈ (V : LowerSet Q) at e
  exact ⟨fun hu => (V : LowerSet Q).lower hqp (e.mp ((U : LowerSet Q).lower hpq hu)),
    fun hv => (U : LowerSet Q).lower hqp (e.mpr ((V : LowerSet Q).lower hpq hv))⟩

end JSP000930.Positive.Cohen
