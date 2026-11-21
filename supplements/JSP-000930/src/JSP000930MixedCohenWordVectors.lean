import JSP000930FreshCohenWordVector
import JSP000930PositiveMixedFreshRowDensity

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Cohen JSP000933.BooleanCompletion JSP000933.MarkedForcing
  JSP000933.ForcingTransport JSP000933.CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B]

abbrev WordVector (F : Finset I) := {i : I // i ∈ F} → List Bool

def vectorAppend {F : Finset I} (u v : WordVector F) : WordVector F :=
  fun i => u i ++ v i

noncomputable def wordVectorValue (B : Type) [CompleteBooleanAlgebra B]
    (F : Finset I) (w : WordVector F) : CohenBA B (I × ℕ) :=
  ⨅ i : {i : I // i ∈ F}, wordValue B i.1 (w i)

theorem fresh_vector_meets_mixed_dense_words
    (S : Set (I × ℕ)) (F : Finset I) (hFresh : ∀ i ∈ F, ∀ n, (i,n) ∉ S)
    (p : CohenBlockBA B S) (D : WordVector F → CohenBlockBA B S)
    (hD : ∀ u, p ≤ ⨆ v, D (vectorAppend u v)) :
    blockEmbed B S p ≤ ⨆ w, wordVectorValue B F w ⊓ blockEmbed B S (D w) := by
  classical
  let z : CohenBA B (I × ℕ) := ⨆ w, wordVectorValue B F w ⊓ blockEmbed B S (D w)
  change blockEmbed B S p ≤ z
  by_contra hz
  let bad := blockEmbed B S p ⊓ zᶜ
  have hNZ : bad ≠ ⊥ := fun e =>
    hz (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  obtain ⟨t, ht⟩ := imageCondition_dense_r50 bad hNZ
  let p₀ := restrictTotal t S
  have h₀ : imageCondition p₀ ≤ p := by
    apply (image_le_iff_member _ _).mpr
    have ht' : t ∈ (blockEmbed B S p : LowerSet (CohenTotal B (I × ℕ))) :=
      (image_le_iff_member _ _).mp (ht.trans inf_le_left)
    exact ht'
  let u : WordVector F := fun i => completeRowWord t.trace i.1
  have hc : imageCondition p₀ ≤ ⨆ v, D (vectorAppend u v) := h₀.trans (hD u)
  obtain ⟨v,d,hd,hd₀,hdv⟩ := exists_nonzero_below_choice_r135
    (imageCondition p₀) (imageCondition_ne_bot_r50 p₀)
    (fun v => D (vectorAppend u v)) hc
  obtain ⟨s₀,hs₀⟩ := imageCondition_dense_r50 d hd
  obtain ⟨s,hss,hsp⟩ := exists_joint_of_image_le_r429 (hs₀.trans hd₀)
  let v₀ : I → List Bool := fun i => if hi : i ∈ F then v ⟨i,hi⟩ else []
  obtain ⟨q,hq,hVec,hNoNew⟩ := exists_refine_vector_only_rows t.trace F v₀
  let tq : CohenTotal B (I × ℕ) := ⟨t.mask,q,t.nonzero,le_top⟩
  have htq : tq ≤ t := (cohen_total_le_iff _ _).mpr ⟨le_rfl,hq⟩
  have hR : (restrict t.trace S).1 ≤ (restrict q S).1 := by
    change Extends (restrict t.trace S).1.1 (restrict q S).1.1
    have hpq : Extends q.1 t.trace.1 := hq
    refine ⟨?_,?_⟩
    · intro x hx
      obtain ⟨hxq,hxS⟩ := (restrict_mem_dom q S x).mp hx
      have hxF : x.1 ∉ F := fun h => hFresh x.1 h x.2
        (show (x.1,x.2) ∈ S from hxS)
      exact (restrict_mem_dom t.trace S x).mpr ⟨hNoNew x hxq hxF, hxS⟩
    · intro x hx
      obtain ⟨hxq,hxS⟩ := (restrict_mem_dom q S x).mp hx
      have hxF : x.1 ∉ F := fun h => hFresh x.1 h x.2
        (show (x.1,x.2) ∈ S from hxS)
      have hp := hNoNew x hxq hxF
      rw [restrict_bit_eq t.trace S x hp hxS, restrict_bit_eq q S x hxq hxS]
      exact (hpq.2 x hp).symm
  have hr : p₀ ≤ restrictTotal tq S := by
    change p₀.1 ≤ (restrictTotal tq S).1
    exact (cohen_total_le_iff _ _).mpr ⟨le_rfl,hR⟩
  obtain ⟨a,haq,has⟩ := lift_stronger_total_block tq S s (hsp.trans hr)
  let w := vectorAppend u v
  have hWordW : imageCondition a ≤ wordVectorValue B F w := by
    apply le_iInf
    intro i
    have hWi : WordMatches tq.trace i.1 (w i) := by
      simpa only [tq,w,vectorAppend,u,v₀,dite_eq_left i.2] using hVec i.1 i.2
    exact (imageCondition_mono_r50 haq).trans (image_le_wordValue tq i.1 (w i) hWi)
  have hSetW : imageCondition a ≤ blockEmbed B S (D w) := by
    apply (imageCondition_mono_r50 has).trans
    rw [← blockEmbed_image]
    exact (cohenBlockProjection B S).pull_mono
      ((imageCondition_mono_r50 hss).trans (hs₀.trans hdv))
  have hW : imageCondition a ≤ z := le_iSup_of_le w (le_inf hWordW hSetW)
  have hN : imageCondition a ≤ zᶜ :=
    (imageCondition_mono_r50 (haq.trans htq)).trans (ht.trans inf_le_right)
  exact imageCondition_ne_bot_r50 a (disjoint_compl_right.out _ hW hN)

end JSP000930.Negative.Cohen
