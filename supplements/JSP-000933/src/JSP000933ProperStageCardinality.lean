import JSP000933GlobalIterationCCC
import Mathlib.SetTheory.Cardinal.Arithmetic

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing

variable {A T : Type} [LinearOrder A] {a : A} {V : PrefixValidator a T}

noncomputable def encodePrefix (p : GoodPrefix V) : Finset (↥(Set.Iio a) × T) := by
  classical
  exact p.finite.toFinset.attach.image (fun i : ↥p.finite.toFinset =>
    let hi : present p.trace i.1 := p.finite.mem_toFinset.mp i.2
    (⟨i.1,p.bounded i.1 hi⟩,Classical.choose hi))

theorem mem_encodePrefix_r97 (p : GoodPrefix V) (i : ↥(Set.Iio a)) (t : T) :
    (i,t) ∈ encodePrefix p ↔ p.trace i.1 = some t := by
  classical
  unfold encodePrefix
  constructor
  · intro h
    obtain ⟨j,hj,h⟩ := Finset.mem_image.mp h
    have hjPresent := p.finite.mem_toFinset.mp j.2
    have hjEval : p.trace j.1 = some (Classical.choose hjPresent) := Classical.choose_spec hjPresent
    have hLoc : j.1 = i.1 := congrArg (fun x : ↥(Set.Iio a) × T => x.1.1) h
    have hVal : Classical.choose hjPresent = t := congrArg Prod.snd h
    exact hLoc ▸ (hjEval.trans (congrArg some hVal))
  · intro h
    have hi : present p.trace i.1 := ⟨t,h⟩
    let j : ↥(p.finite.toFinset) := ⟨i.1,p.finite.mem_toFinset.mpr hi⟩
    refine Finset.mem_image.mpr ⟨j,Finset.mem_attach p.finite.toFinset j,?_⟩
    apply Prod.ext
    · exact Subtype.ext rfl
    · have hJ := Classical.choose_spec (p.finite.mem_toFinset.mp j.2)
      exact Option.some.inj (hJ.symm.trans h)

theorem encodePrefix_injective_r97 : Function.Injective (encodePrefix : GoodPrefix V → _) := by
  intro p q h
  have hTrace : p.trace = q.trace := by
    funext i
    cases hp : p.trace i with
    | none =>
      cases hq : q.trace i with
      | none => rfl
      | some t =>
        let j : ↥(Set.Iio a) := ⟨i,q.bounded i ⟨t,hq⟩⟩
        have hh := (mem_encodePrefix_r97 q j t).mpr hq
        rw [← h] at hh
        have hBad := (mem_encodePrefix_r97 p j t).mp hh
        change p.trace i = some t at hBad
        rw [hp] at hBad
        cases hBad
    | some t =>
      let j : ↥(Set.Iio a) := ⟨i,p.bounded i ⟨t,hp⟩⟩
      have hh := (mem_encodePrefix_r97 p j t).mpr hp
      rw [h] at hh
      exact ((mem_encodePrefix_r97 q j t).mp hh).symm
  rcases p with ⟨p,hpF,hpB,hpV⟩
  rcases q with ⟨q,hqF,hqB,hqV⟩
  change p = q at hTrace
  cases hTrace
  rfl

theorem mk_GoodPrefix_le_alephOne_r97
    (hA : Cardinal.mk (↥(Set.Iio a)) ≤ ℵ₁) (hT : Cardinal.mk T ≤ ℵ₁) :
    Cardinal.mk (GoodPrefix V) ≤ ℵ₁ := by
  classical
  have hInf := Cardinal.isRegular_aleph_one.1
  have hProd : Cardinal.mk (↥(Set.Iio a) × T) ≤ ℵ₁ := by
    rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id,← Cardinal.mul_eq_self hInf]
    exact mul_le_mul' hA hT
  calc
    Cardinal.mk (GoodPrefix V) ≤ Cardinal.mk (Finset (↥(Set.Iio a) × T)) :=
      Cardinal.mk_le_of_injective encodePrefix_injective_r97
    _ ≤ Cardinal.mk (List (↥(Set.Iio a) × T)) :=
      Cardinal.mk_le_of_surjective List.toFinset_surjective
    _ ≤ max ℵ₀ (Cardinal.mk (↥(Set.Iio a) × T)) := Cardinal.mk_list_le_max _
    _ ≤ ℵ₁ := max_le hInf hProd

theorem mk_omegaTwo_properPrefix_le_alephOne_r97 (a : OmegaTwoIndex) :
    Cardinal.mk (↥(Set.Iio a)) ≤ ℵ₁ := by
  let e := Ordinal.ToType.mk (o := (Order.succ (ℵ₁ : Cardinal)).ord)
  let x := e.symm a
  let f (i : ↥(Set.Iio a)) : x.1.ToType :=
    Ordinal.ToType.mk ⟨(e.symm i.1).1,e.symm.strictMono i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun y : Set.Iio x.1 => y.val) ((Ordinal.ToType.mk (o := x.1)).injective hij)
  apply Order.lt_succ_iff.mp
  apply (Cardinal.mk_le_of_injective hf).trans_lt
  rw [Cardinal.mk_toType]
  exact Cardinal.lt_ord.mp x.2

theorem mk_groundCliqueLabels_r97 :
    Cardinal.mk ((Finset OmegaOneIndex)ᵒᵈ) = ℵ₁ := by
  letI : Infinite OmegaOneIndex := by
    by_contra h
    letI : Finite OmegaOneIndex := not_infinite_iff_finite.mp h
    exact OmegaOneIndex_not_countable_r61 inferInstance
  change Cardinal.mk (Finset OmegaOneIndex) = ℵ₁
  rw [Cardinal.mk_finset_of_infinite,mk_OmegaOneIndex_r61]

end FiniteSupport
end JSP000933
