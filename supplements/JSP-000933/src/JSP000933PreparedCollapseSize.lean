import JSP000933PreparedCHBase

open Cardinal Flypitch

namespace JSP000933
namespace PreparedModel

def collapseGraph {X Y : Type} (q : CollapsePoset X Y (Order.succ (ℵ₀ : Cardinal))) :
    Set (X×Y) := {z | z.2∈q.f z.1}

theorem collapseGraph_injective_r391 {X Y : Type} :
    Function.Injective (collapseGraph (X := X) (Y := Y)) := by
  intro p q h
  have hpq : CPFun.le p.f q.f := by
    intro x y hy
    change (x,y)∈collapseGraph p at hy
    rw [h] at hy
    exact hy
  have hqp : CPFun.le q.f p.f := by
    intro x y hy
    change (x,y)∈collapseGraph q at hy
    rw [←h] at hy
    exact hy
  have hf := CPFun.le_antisymm hpq hqp
  cases p
  cases q
  cases hf
  rfl

theorem collapseGraph_countable_bound_r391 {X Y : Type}
    (q : CollapsePoset X Y (Order.succ (ℵ₀ : Cardinal))) :
    Cardinal.mk (collapseGraph q)≤ℵ₀ := by
  let E (z : ↥(collapseGraph q)) : ↥(PFun.Dom q.f) :=
    ⟨z.val.1,CPFun.mem_Dom_of_mem z.property⟩
  have hE : Function.Injective E := by
    intro a b he
    have h1 : a.val.1=b.val.1 := congrArg Subtype.val he
    apply Subtype.ext
    apply Prod.ext h1
    have ha : a.val.2∈q.f a.val.1 := a.property
    have hb' : b.val.2∈q.f b.val.1 := b.property
    have hb : b.val.2∈q.f a.val.1 := by simpa only [h1] using hb'
    have hd : a.val.1∈PFun.Dom q.f := CPFun.mem_Dom_of_mem ha
    exact (CPFun.fn_eq_of_mem ha hd).symm.trans (CPFun.fn_eq_of_mem hb hd)
  exact (Cardinal.mk_le_of_injective hE).trans (Order.lt_succ_iff.mp q.Hc)

theorem countableCollapseBasic_card_bound_r391 (X Y : Type) [Infinite (X×Y)] :
    Cardinal.mk (CollapsePoset X Y (Order.succ (ℵ₀ : Cardinal))) ≤ Cardinal.mk (X×Y)^ℵ₀ := by
  let f (q : CollapsePoset X Y (Order.succ (ℵ₀ : Cardinal))) :
      {S : Set (X×Y) // Cardinal.mk S≤ℵ₀} := ⟨collapseGraph q,collapseGraph_countable_bound_r391 q⟩
  have hf : Function.Injective f := fun _ _ h => collapseGraph_injective_r391 (congrArg Subtype.val h)
  exact (Cardinal.mk_le_of_injective hf).trans (Cardinal.mk_bounded_set_le_of_infinite (X×Y) ℵ₀)

theorem baseOmegaOne_type_card_r391 : Cardinal.mk BaseOmegaOne.Type=ℵ₁ := by
  simp [BaseOmegaOne,pSet_aleph1,PSet.mk_type_mk_eq''']

theorem baseGroundReals_type_card_r391 : Cardinal.mk BaseGroundReals.Type=𝔠 := by
  change Cardinal.mk (Set (PSet.omega : PSet.{0}).Type)=𝔠
  rw [Cardinal.mk_set,PSet.mk_omega_eq_mk_omega,Cardinal.two_power_aleph0]

theorem baseCollapseBasic_card_le_continuum_r391 : Cardinal.mk BaseCollapseBasic≤𝔠 := by
  have hX : Cardinal.mk BaseOmegaOne.Type=ℵ₁ := baseOmegaOne_type_card_r391
  have hY : Cardinal.mk BaseGroundReals.Type=𝔠 := baseGroundReals_type_card_r391
  have hXY : Cardinal.mk (BaseOmegaOne.Type×BaseGroundReals.Type)≤𝔠 := by
    rw [Cardinal.mk_prod,hX,hY]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul_left Cardinal.aleph_one_le_continuum _).trans_eq Cardinal.continuum_mul_self
  letI : Infinite (BaseOmegaOne.Type×BaseGroundReals.Type) := Cardinal.infinite_iff.mpr (by
    rw [Cardinal.mk_prod,hX,hY]
    simp only [Cardinal.lift_id]
    exact (Cardinal.aleph0_le_mul_iff).mpr
      ⟨ne_of_gt (Cardinal.aleph0_pos.trans PSet.omega_lt_aleph_one),Cardinal.continuum_ne_zero,
        Or.inr Cardinal.aleph0_le_continuum⟩)
  exact (countableCollapseBasic_card_bound_r391 BaseOmegaOne.Type BaseGroundReals.Type).trans
    ((Cardinal.power_le_power_right hXY).trans_eq Cardinal.continuum_power_aleph0)

end PreparedModel
end JSP000933
