import JSP000933NativeGroundTailCarriers
import Mathlib.SetTheory.Cardinal.Arithmetic

open Cardinal

namespace JSP000933
namespace ForcingTransport
namespace RawTail

open FiniteSupport

variable {A T : Type} {allowed : A→Prop}

private noncomputable def graphEntry_r490 (r : RawTail T allowed)
    (i : {i : A // i∈r.scope}) : {i : A // allowed i}×T :=
  let h := (mem_scope r i.val).mp i.property
  (⟨i.val,r.bounded i.val h⟩,Classical.choose h)

private theorem graphEntry_spec_r490 (r : RawTail T allowed)
    (i : {i : A // i∈r.scope}) :
    r.trace i.val=some (graphEntry_r490 r i).2 :=
  Classical.choose_spec ((mem_scope r i.val).mp i.property)

noncomputable def finiteGraph_r490 (r : RawTail T allowed) :
    Finset ({i : A // allowed i}×T) := by
  classical
  exact r.scope.attach.image (graphEntry_r490 r)

theorem mem_finiteGraph_r490 (r : RawTail T allowed) (a : {i : A // allowed i}) (t : T) :
    (a,t)∈finiteGraph_r490 r ↔ r.trace a.val=some t := by
  classical
  unfold finiteGraph_r490
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    have h1 : i.val=a.val := congrArg (fun z : {i : A // allowed i}×T => z.1.val) hi
    have h2 : (graphEntry_r490 r i).2=t := congrArg Prod.snd hi
    have hs := graphEntry_spec_r490 r i
    rw [h1,h2] at hs
    exact hs
  · intro h
    let i : {i : A // i∈r.scope} := ⟨a.val,(mem_scope r a.val).mpr ⟨t,h⟩⟩
    refine Finset.mem_image.mpr ⟨i,Finset.mem_attach _ _,Prod.ext ?_ ?_⟩
    · apply Subtype.ext
      rfl
    · apply Option.some.inj
      exact (graphEntry_spec_r490 r i).symm.trans h

theorem finiteGraph_injective_r490 :
    Function.Injective (finiteGraph_r490 : RawTail T allowed→_) := by
  intro r s h
  apply extTrace
  funext i
  have step (r s : RawTail T allowed) (h : finiteGraph_r490 r=finiteGraph_r490 s)
      (t : T) (ht : r.trace i=some t) : s.trace i=some t := by
    let a : {i : A // allowed i} := ⟨i,r.bounded i ⟨t,ht⟩⟩
    have hm := (mem_finiteGraph_r490 r a t).mpr ht
    rw [h] at hm
    exact (mem_finiteGraph_r490 s a t).mp hm
  cases hr : r.trace i with
  | some t => exact (step r s h t hr).symm
  | none =>
    cases hs : s.trace i with
    | none => rfl
    | some t =>
      have hh := step s r h.symm t hs
      rw [hr] at hh
      cases hh

theorem card_le_r490 {c : Cardinal} (hc : ℵ₀≤c)
    (hA : Cardinal.mk {i : A // allowed i}≤c) (hT : Cardinal.mk T≤c) :
    Cardinal.mk (RawTail T allowed)≤c := by
  classical
  apply (Cardinal.mk_le_of_injective finiteGraph_injective_r490).trans
  apply (Cardinal.mk_le_of_surjective List.toFinset_surjective).trans
  exact (Cardinal.mk_list_le_max _).trans
    (max_le hc (by simpa only [Cardinal.mk_prod,Cardinal.lift_id] using Cardinal.mul_le_of_le hc hA hT))

end RawTail
end ForcingTransport
end JSP000933
