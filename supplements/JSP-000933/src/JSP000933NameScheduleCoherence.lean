import JSP000933InteriorNameReflection

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

theorem wholeReduction_coherent_r110 {A : Type} [LinearOrder A] {N : A → Type}
    {R : Rules N} {a b : A} (hab : a ≤ b) (U : RO (Before R a)) :
    (wholeReduction b).boolPullback ((prefixReduction hab).boolPullback U) =
      (wholeReduction a).boolPullback U := by
  apply Heyting.Regular.coe_injective
  ext p
  change (restrict (restrict p b).1 a) ∈ (U : LowerSet (Before R a)) ↔
    restrict p a ∈ (U : LowerSet (Before R a))
  rw [restrict_restrict_r92 p hab]

theorem mk_OmegaTwoIndex_r110 : Cardinal.mk OmegaTwoIndex = Order.succ (ℵ₁ : Cardinal) := by
  simp only [OmegaTwoIndex,Cardinal.mk_toType,Cardinal.card_ord]

theorem exists_pairStageNameCode_r110 :
    Nonempty ((OmegaTwoIndex × OmegaOneIndex) ↪ OmegaTwoIndex) := by
  apply (Cardinal.le_def _ _).mp
  let κ := Order.succ (ℵ₁ : Cardinal)
  have hInf : (ℵ₀ : Cardinal) ≤ κ := Cardinal.isRegular_aleph_one.1.trans (Order.le_succ _)
  rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id,mk_OmegaTwoIndex_r110,mk_OmegaOneIndex_r61]
  exact (mul_le_mul' (le_rfl : κ ≤ κ) (Order.le_succ _)).trans_eq (Cardinal.mul_eq_self hInf)

theorem exists_stagePairCodes_bounded_r110 (f : OmegaTwoIndex × OmegaOneIndex → OmegaTwoIndex)
    (a : OmegaTwoIndex) : ∃ b, ∀ i : OmegaOneIndex, f (a,i) < b := by
  let g (i : OmegaOneIndex) := f (a,i)
  let r (i : OmegaOneIndex) : ↥(Set.range g) := ⟨g i,Set.mem_range_self i⟩
  have hSurj : Function.Surjective r := by
    rintro ⟨y,⟨i,rfl⟩⟩
    exact ⟨i,rfl⟩
  have hCard : Cardinal.mk (↥(Set.range g)) ≤ ℵ₁ :=
    (Cardinal.mk_le_of_surjective hSurj).trans_eq mk_OmegaOneIndex_r61
  obtain ⟨b,hb⟩ := omegaTwo_smallSet_bounded_r108 (Set.range g) hCard
  exact ⟨b,fun i => hb _ (Set.mem_range_self i)⟩

end FiniteSupport
end JSP000933
