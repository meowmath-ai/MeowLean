import JSP000933NativeBasePrefixCoherence

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion

structure DenseForcingMap (P Q : Type) [Preorder P] [Preorder Q] where
  map : P → Q
  monotone : Monotone map
  dense : ∀ q : Q, ∃ p : P, map p ≤ q
  reflect_compatible : ∀ {p p' : P}, Compatible (map p) (map p') → Compatible p p'

namespace DenseForcingMap

variable {P Q : Type} [Preorder P] [Preorder Q] (F : DenseForcingMap P Q)

theorem liftBelow (p : P) (q : Q) (hq : q ≤ F.map p) :
    ∃ r ≤ p, F.map r ≤ q := by
  obtain ⟨u,hu⟩ := F.dense q
  obtain ⟨r,hru,hrp⟩ := F.reflect_compatible
    ⟨F.map u,le_rfl,hu.trans hq⟩
  exact ⟨r,hrp,(F.monotone hru).trans hu⟩

def pullLower (U : LowerSet Q) : LowerSet P :=
  ⟨{p | F.map p ∈ U},fun _ _ h hp => U.lower (F.monotone h) hp⟩

theorem pullLower_compl (U : LowerSet Q) :
    F.pullLower Uᶜ = (F.pullLower U)ᶜ := by
  ext p
  change F.map p ∈ (Uᶜ : LowerSet Q) ↔ p ∈ ((F.pullLower U)ᶜ : LowerSet P)
  rw [mem_pseudoCompl_r50,mem_pseudoCompl_r50]
  constructor
  · intro h r hr
    exact h (F.map r) (F.monotone hr)
  · intro h q hq hU
    obtain ⟨r,hr,hrq⟩ := F.liftBelow p q hq
    exact h r hr (U.lower hrq hU)

def pull (U : RO Q) : RO P :=
  ⟨F.pullLower (U : LowerSet Q),by
    change (F.pullLower (U : LowerSet Q))ᶜᶜ = F.pullLower (U : LowerSet Q)
    rw [← F.pullLower_compl,← F.pullLower_compl,U.prop.eq]⟩

theorem pull_compl (U : RO Q) : F.pull Uᶜ = (F.pull U)ᶜ := by
  apply Heyting.Regular.coe_injective
  exact F.pullLower_compl (U : LowerSet Q)

theorem mem_pull (U : RO Q) (p : P) :
    p ∈ (F.pull U : LowerSet P) ↔ F.map p ∈ (U : LowerSet Q) := Iff.rfl

theorem pull_le_iff {U V : RO Q} : F.pull U ≤ F.pull V ↔ U ≤ V := by
  constructor
  · intro h
    by_contra hn
    have hN : U ⊓ Vᶜ ≠ ⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨q,hq⟩ := imageCondition_dense_r50 _ hN
    obtain ⟨p,hp⟩ := F.dense q
    have hU : imageCondition (F.map p) ≤ U :=
      (imageCondition_mono_r50 hp).trans (hq.trans inf_le_left)
    have hVc : imageCondition (F.map p) ≤ Vᶜ :=
      (imageCondition_mono_r50 hp).trans (hq.trans inf_le_right)
    have hP : p ∈ (F.pull U : LowerSet P) :=
      (F.mem_pull U p).mpr ((image_le_iff_member _ _).mp hU)
    have hV : (F.map p) ∈ (V : LowerSet Q) :=
      (F.mem_pull V p).mp ((Heyting.Regular.coe_le_coe.mpr h) hP)
    exact imageCondition_ne_bot_r50 (F.map p) (disjoint_compl_right.out _
      ((image_le_iff_member _ _).mpr hV) hVc)
  · intro h
    apply Heyting.Regular.coe_le_coe.mp
    intro p hp
    exact (F.mem_pull V p).mpr ((Heyting.Regular.coe_le_coe.mpr h) ((F.mem_pull U p).mp hp))

noncomputable def push (U : RO P) : RO Q :=
  ⨆ p : {p : P // p ∈ (U : LowerSet P)}, imageCondition (F.map p.val)

theorem pull_push (U : RO P) : F.pull (F.push U) = U := by
  classical
  apply le_antisymm
  · apply Heyting.Regular.coe_le_coe.mp
    intro p hp
    by_contra hn
    have hN : p ∉ ((U : LowerSet P)ᶜᶜ : LowerSet P) := by
      rw [U.prop.eq]
      exact hn
    rw [mem_doublePseudoCompl_r50] at hN
    push Not at hN
    obtain ⟨r,hr,hNo⟩ := hN
    have hFront : imageCondition (F.map r) ≤ F.push U :=
      (imageCondition_mono_r50 (F.monotone hr)).trans
        ((image_le_iff_member _ _).mpr ((F.mem_pull _ _).mp hp))
    have hZero : imageCondition (F.map r) ⊓ F.push U ≤ ⊥ := by
      simp only [push,inf_iSup_eq]
      apply iSup_le
      intro s
      refine disjoint_iff_inf_le.mp ?_
      by_contra hc
      have hx := (compatible_iff_not_disjoint_r50 _ _).mpr hc
      obtain ⟨t,htr,hts⟩ := F.reflect_compatible hx
      exact hNo t htr ((U : LowerSet P).lower hts s.property)
    exact imageCondition_ne_bot_r50 (F.map r) (le_bot_iff.mp ((le_inf le_rfl hFront).trans hZero))
  · apply Heyting.Regular.coe_le_coe.mp
    intro p hp
    apply (F.mem_pull _ _).mpr
    apply (image_le_iff_member _ _).mp
    exact le_iSup (fun q : {q : P // q ∈ (U : LowerSet P)} => imageCondition (F.map q.val)) ⟨p,hp⟩

noncomputable def pullIso : RO Q ≃o RO P where
  toEquiv := Equiv.ofBijective F.pull
    ⟨fun _ _ h => le_antisymm (F.pull_le_iff.mp h.le) (F.pull_le_iff.mp h.ge),
      fun U => ⟨F.push U,F.pull_push U⟩⟩
  map_rel_iff' := F.pull_le_iff

end DenseForcingMap
end ForcingTransport
end JSP000933
