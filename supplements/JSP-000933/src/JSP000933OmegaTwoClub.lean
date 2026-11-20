import JSP000933CountableReflection

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing

theorem omegaTwo_smallSet_bounded_r108 (S : Set OmegaTwoIndex)
    (hS : Cardinal.mk (↥S) ≤ ℵ₁) :
    ∃ a : OmegaTwoIndex, ∀ i ∈ S, i < a := by
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  let t := Ordinal.ToType.mk (o := o)
  let f (i : S) : Ordinal := (t.symm i.1).1 + 1
  have hReg : (Order.succ (ℵ₁ : Cardinal)).IsRegular :=
    Cardinal.isRegular_succ Cardinal.isRegular_aleph_one.1
  have hCof : Cardinal.mk S < o.cof := by
    rw [show o.cof = Order.succ (ℵ₁ : Cardinal) from hReg.cof_ord]
    exact hS.trans_lt (Order.lt_succ _)
  have hδ : (⨆ i, f i) < o :=
    Ordinal.iSup_lt_of_lt_cof hCof (fun i =>
      (Cardinal.isSuccLimit_ord hReg.1).add_one_lt (t.symm i.1).2)
  refine ⟨t ⟨_,hδ⟩,fun i hi => ?_⟩
  have h' : (t.symm i).1 < ⨆ i, f i :=
    ((Order.add_one_le_iff).mp (le_rfl : f ⟨i,hi⟩ ≤ f ⟨i,hi⟩)).trans_le
      (Ordinal.le_iSup f ⟨i,hi⟩)
  have h'' : t.symm i < (⟨_,hδ⟩ : ↥(Set.Iio o)) := h'
  have ht := t.strictMono h''
  rw [t.apply_symm_apply i] at ht
  exact ht

def stageClosedUnder (f : OmegaTwoIndex → OmegaTwoIndex) : Set OmegaTwoIndex :=
  {a | ∀ i < a, f i < a}

def OrdinalClub (C : Set OmegaTwoIndex) : Prop :=
  (∀ a, ∃ b, a < b ∧ b ∈ C) ∧
  (∀ δ, (∃ i, i < δ) → (∀ i < δ, ∃ a, i < a ∧ a < δ ∧ a ∈ C) → δ ∈ C)

theorem stageClosedUnder_isClub_r108 (f : OmegaTwoIndex → OmegaTwoIndex) :
    OrdinalClub (stageClosedUnder f) := by
  classical
  constructor
  · intro a
    have hStep (x : OmegaTwoIndex) : ∃ y, x < y ∧ ∀ i < x, f i < y := by
      let S := f '' Set.Iio x
      let funS (i : ↥(Set.Iio x)) : ↥S := ⟨f i.1,⟨i.1,i.2,rfl⟩⟩
      have hSurj : Function.Surjective funS := by
        rintro ⟨b,⟨i,hi,rfl⟩⟩
        exact ⟨⟨i,hi⟩,rfl⟩
      have hCard := (Cardinal.mk_le_of_surjective hSurj).trans
        (mk_omegaTwo_properPrefix_le_alephOne_r97 x)
      obtain ⟨y,hy⟩ := omegaTwo_smallSet_bounded_r108 S hCard
      obtain ⟨z,hz⟩ := OmegaTwoIndex_finite_bounded_r89 {x,y}
      exact ⟨z,hz x (Finset.mem_insert_self ..),fun i hi =>
        (hy (f i) ⟨i,hi,rfl⟩).trans (hz y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))⟩
    let next (i : OmegaTwoIndex) := Classical.choose (hStep i)
    let s : ℕ → OmegaTwoIndex := Nat.rec a (fun _ x => next x)
    have hs (n : ℕ) : s n < s (n+1) ∧ ∀ i < s n, f i < s (n+1) :=
      Classical.choose_spec (hStep (s n))
    let o := (Order.succ (ℵ₁ : Cardinal)).ord
    let t := Ordinal.ToType.mk (o := o)
    let v (n : ℕ) : Ordinal := (t.symm (s n)).1
    have hvlt (n : ℕ) : v n < o := (t.symm (s n)).2
    have hReg : (Order.succ (ℵ₁ : Cardinal)).IsRegular :=
      Cardinal.isRegular_succ Cardinal.isRegular_aleph_one.1
    have hCof : Cardinal.mk ℕ < o.cof := by
      rw [Cardinal.mk_nat,show o.cof = Order.succ (ℵ₁ : Cardinal) from hReg.cof_ord]
      exact Cardinal.isRegular_aleph_one.1.trans_lt (Order.lt_succ _)
    have hδ : (⨆ n, v n) < o := Ordinal.iSup_lt_of_lt_cof hCof hvlt
    let δ := t ⟨_,hδ⟩
    have hBound (n : ℕ) : s n ≤ δ := by
      have hh : t.symm (s n) ≤ (⟨_,hδ⟩ : ↥(Set.Iio o)) := Ordinal.le_iSup v n
      have ht := t.monotone hh
      rw [t.apply_symm_apply (s n)] at ht
      exact ht
    refine ⟨δ,(hs 0).1.trans_le (hBound 1),?_⟩
    intro i hi
    have hLt : (t.symm i).1 < ⨆ n, v n := by
      have hh := t.symm.strictMono hi
      change t.symm i < t.symm (t ⟨_,hδ⟩) at hh
      rw [t.symm_apply_apply] at hh
      exact hh
    have hIndex : ∃ n, (t.symm i).1 < v n := by
      by_contra hn
      have hLe : (⨆ n, v n) ≤ (t.symm i).1 :=
        Ordinal.iSup_le (fun n => le_of_not_gt (fun h => hn ⟨n,h⟩))
      exact (not_le_of_gt hLt) hLe
    obtain ⟨n,hn⟩ := hIndex
    have hn' : t.symm i < t.symm (s n) := hn
    have hi' : i < s n := by
      have ht := t.strictMono hn'
      rw [t.apply_symm_apply i, t.apply_symm_apply (s n)] at ht
      exact ht
    exact ((hs n).2 i hi').trans_le (hBound (n+1))
  · intro δ _ h i hi
    obtain ⟨a,hia,haδ,ha⟩ := h i hi
    exact (ha i hia).trans haδ

end FiniteSupport
end JSP000933
