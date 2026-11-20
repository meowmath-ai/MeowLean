import JSP000933RelativeTraceEnumeration

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing OpenGraphForcing

variable {B N I : Type} [CompleteBooleanAlgebra B]
variable [Preorder I] [WellFoundedLT I]

noncomputable def greedyTraceStep (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) (prev : ∀ j:I,j< i→N→B) (n : N) : B :=
  (E.cell i n⊓(Q.valid n⊓traceAccept Q x n))⊓
    ⨅ j : ↥(Set.Iio i),⨅ k : N,(prev j.val j.property k⊓commonRefinementValue Q n k)ᶜ

noncomputable def greedyTraceWeight (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) : I→N→B :=
  WellFounded.fix wellFounded_lt (greedyTraceStep Q E x)

theorem greedyTraceWeight_eq_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) :
    greedyTraceWeight Q E x i=greedyTraceStep Q E x i (fun j _ => greedyTraceWeight Q E x j) :=
  WellFounded.fix_eq wellFounded_lt (greedyTraceStep Q E x) i

theorem greedyTraceWeight_cell_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) (n : N) :
    greedyTraceWeight Q E x i n≤E.cell i n := by
  rw [greedyTraceWeight_eq_r465]
  exact inf_le_left.trans inf_le_left

theorem greedyTraceWeight_valid_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) (n : N) :
    greedyTraceWeight Q E x i n≤Q.valid n := by
  rw [greedyTraceWeight_eq_r465]
  exact inf_le_left.trans (inf_le_right.trans inf_le_left)

theorem greedyTraceWeight_accepted_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i : I) (n : N) :
    greedyTraceWeight Q E x i n≤traceAccept Q x n := by
  rw [greedyTraceWeight_eq_r465]
  exact inf_le_left.trans (inf_le_right.trans inf_le_right)

theorem greedyTraceWeight_apart_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) (i j : I) (hij : i<j) (n k : N) :
    (greedyTraceWeight Q E x i n⊓greedyTraceWeight Q E x j k)⊓commonRefinementValue Q n k=⊥ := by
  let w := greedyTraceWeight Q E x
  have hC : w j k≤(w i n⊓commonRefinementValue Q k n)ᶜ := by
    change greedyTraceWeight Q E x j k≤_
    rw [greedyTraceWeight_eq_r465 Q E x j]
    exact inf_le_right.trans ((iInf_le _ ⟨i,hij⟩).trans (iInf_le _ n))
  rw [commonRefinementValue_comm_r464 Q k n] at hC
  apply le_bot_iff.mp
  exact (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (inf_le_left.trans (inf_le_right.trans hC))).trans_eq inf_compl_eq_bot'

noncomputable def greedyTraceValue (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) : TotalBA Q :=
  ⨆ i,⨆ n,traceRectangle Q n (greedyTraceWeight Q E x i n)

theorem greedyTraceValue_le_r465 (Q : ValuedPoset B N) (E : MixedEnumeration I N B)
    (x : TotalBA Q) : greedyTraceValue Q E x≤x := by
  apply iSup_le
  intro i
  apply iSup_le
  intro n
  exact (traceRectangle_accept_iff_r464 Q x n _).mpr (greedyTraceWeight_accepted_r465 Q E x i n)

theorem omegaOne_greedyWeight_bounded_r465 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (E : MixedEnumeration OmegaOneIndex N B) (x : TotalBA Q) :
    unboundedValue (fun i => ⨆ n,greedyTraceWeight Q E x i n)=⊥ :=
  hQ (greedyTraceWeight Q E x) (greedyTraceWeight_valid_r465 Q E x) (greedyTraceWeight_apart_r465 Q E x)

end RelativeOCA
end JSP000933
