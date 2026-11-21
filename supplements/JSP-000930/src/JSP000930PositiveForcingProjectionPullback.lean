import JSP000933BooleanCompletion

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion

universe u v

structure ForcingProjection (P : Type u) (Q : Type v) [Preorder P] [Preorder Q] where
  toFun : P → Q
  mono : Monotone toFun
  liftBelow : ∀ (p : P) (q : Q), q ≤ toFun p →
    ∃ r : P, r ≤ p ∧ toFun r ≤ q

variable {P : Type u} {Q : Type v} [Preorder P] [Preorder Q]

def ForcingProjection.lowerPull (F : ForcingProjection P Q) (U : LowerSet Q) :
    LowerSet P :=
  ⟨{p | F.toFun p ∈ U}, fun _ _ hpq hq => U.lower (F.mono hpq) hq⟩

theorem ForcingProjection.lowerPull_compl (F : ForcingProjection P Q)
    (U : LowerSet Q) : (F.lowerPull U)ᶜ = F.lowerPull Uᶜ := by
  ext p
  change p ∈ (F.lowerPull U)ᶜ ↔ F.toFun p ∈ Uᶜ
  rw [mem_pseudoCompl_r50, mem_pseudoCompl_r50]
  constructor
  · intro h q hq hU
    obtain ⟨r,hrp,hrq⟩ := F.liftBelow p q hq
    exact h r hrp (U.lower hrq hU)
  · intro h r hr hrU
    exact h (F.toFun r) (F.mono hr) hrU

def ForcingProjection.pull (F : ForcingProjection P Q) (U : RO Q) : RO P :=
  ⟨F.lowerPull (U : LowerSet Q), by
    change (F.lowerPull (U : LowerSet Q))ᶜᶜ = _
    rw [F.lowerPull_compl, F.lowerPull_compl, U.prop.eq]⟩

theorem ForcingProjection.pull_compl (F : ForcingProjection P Q) (U : RO Q) :
    F.pull Uᶜ = (F.pull U)ᶜ := by
  apply Heyting.Regular.coe_injective
  exact (F.lowerPull_compl (U : LowerSet Q)).symm

theorem ForcingProjection.pull_top (F : ForcingProjection P Q) :
    F.pull ⊤ = ⊤ := by
  apply Heyting.Regular.coe_injective
  ext p
  rfl

theorem ForcingProjection.pull_mono (F : ForcingProjection P Q) :
    Monotone F.pull := by
  intro U V h
  apply Heyting.Regular.coe_le_coe.mp
  intro p hp
  exact (Heyting.Regular.coe_le_coe.mpr h) hp

theorem ForcingProjection.pull_injective (F : ForcingProjection P Q)
    (h : Function.Surjective F.toFun) : Function.Injective F.pull := by
  intro U V huv
  apply Heyting.Regular.coe_injective
  ext q
  obtain ⟨p,rfl⟩ := h q
  have hv := congrArg (fun z : RO P => p ∈ (z : LowerSet P)) huv
  exact Iff.of_eq hv

end JSP000930.Positive.Cohen
