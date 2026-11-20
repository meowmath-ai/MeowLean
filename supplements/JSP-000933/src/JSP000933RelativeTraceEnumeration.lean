import JSP000933RelativeJoinedLabelWeights
import JSP000933RelativeGenericUnboundedSupport

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing OpenGraphForcing

variable {B N I : Type} [CompleteBooleanAlgebra B]

structure MixedEnumeration (I N B : Type) [CompleteBooleanAlgebra B] where
  cell : I→N→B
  rowFull : ∀ i,(⨆ n,cell i n)=⊤
  colFull : ∀ n,(⨆ i,cell i n)=⊤
  rowApart : ∀ i,Pairwise (fun n k => Disjoint (cell i n) (cell i k))

noncomputable def traceRectangle (Q : ValuedPoset B N) (n : N) (b : B) : TotalBA Q :=
  baseEmbed Q b⊓traceValue Q n

noncomputable def traceAccept (Q : ValuedPoset B N) (x : TotalBA Q) (n : N) : B :=
  forcedByBase Q (traceValue Q n⇨x)

theorem traceRectangle_accept_iff_r464 (Q : ValuedPoset B N) (x : TotalBA Q) (n : N) (b : B) :
    traceRectangle Q n b≤x ↔ b≤traceAccept Q x n := by
  unfold traceRectangle traceAccept
  rw [← le_himp_iff,baseEmbed_le_iff_forced_r428]

theorem traceRectangle_mono_r464 (Q : ValuedPoset B N) (n : N) :
    Monotone (traceRectangle Q n) :=
  fun _ _ h => inf_le_inf (baseEmbed_mono_r427 Q h) le_rfl

theorem traceRectangle_zero_r464 (Q : ValuedPoset B N) (n : N) :
    traceRectangle Q n ⊥=⊥ := by simp only [traceRectangle,baseEmbed_bot_r427,bot_inf_eq]

theorem traceRectangle_pair_support_r464 (Q : ValuedPoset B N) (n k : N) (b c : B) :
    supportProjection Q (traceRectangle Q n b⊓traceRectangle Q k c)=
      commonRefinementValue Q n k⊓(b⊓c) := by
  have h : traceRectangle Q n b⊓traceRectangle Q k c=
      (traceValue Q n⊓traceValue Q k)⊓baseEmbed Q (b⊓c) := by
    unfold traceRectangle
    rw [baseEmbed_meets_r429]
    ac_rfl
  rw [h,projected_masked_pair_r430]

theorem commonRefinementValue_comm_r464 (Q : ValuedPoset B N) (n k : N) :
    commonRefinementValue Q n k=commonRefinementValue Q k n := by
  unfold commonRefinementValue
  apply congrArg (fun f : N→B => iSup f)
  funext r
  exact inf_comm _ _

end RelativeOCA
end JSP000933
