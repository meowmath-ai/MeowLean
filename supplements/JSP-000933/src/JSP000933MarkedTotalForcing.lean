import JSP000933BooleanCompletion

namespace JSP000933
namespace MarkedForcing

open BooleanCompletion

structure ValuedPoset (B N : Type) [CompleteBooleanAlgebra B] where
  valid : N→B
  refines : N→N→B
  refine_valid : ∀ n m,refines n m≤valid n⊓valid m
  refl : ∀ n,valid n≤refines n n
  trans : ∀ n m k,refines n m⊓refines m k≤refines n k
  weakest : N
  weakest_valid : valid weakest=⊤
  weaker : ∀ n,valid n≤refines n weakest

variable {B N : Type} [CompleteBooleanAlgebra B]

structure TotalCondition (Q : ValuedPoset B N) where
  mask : B
  trace : N
  nonzero : mask≠⊥
  valid : mask≤Q.valid trace

variable {Q : ValuedPoset B N}

def TotalCondition.Stronger (p q : TotalCondition Q) : Prop :=
  p.mask≤q.mask ∧ p.mask≤Q.refines p.trace q.trace

instance : Preorder (TotalCondition Q) where
  le := TotalCondition.Stronger
  le_refl p := ⟨le_rfl,p.valid.trans (Q.refl p.trace)⟩
  le_trans _ _ _ hp hq := ⟨hp.1.trans hq.1,
    (le_inf hp.2 (hp.1.trans hq.2)).trans (Q.trans _ _ _)⟩

def weakenToBase (Q : ValuedPoset B N) (b : B) (hb : b≠⊥) : TotalCondition Q :=
  ⟨b,Q.weakest,hb,Q.weakest_valid.symm ▸ le_top⟩

theorem below_weakenToBase_r426 (p : TotalCondition Q) {b : B} (hb : b≠⊥) :
    p≤weakenToBase Q b hb ↔ p.mask≤b :=
  ⟨fun h => h.1,fun h => ⟨h,p.valid.trans (Q.weaker _)⟩⟩

noncomputable def intersectMask (p : TotalCondition Q) (b : B) (h : p.mask⊓b≠⊥) :
    TotalCondition Q :=
  ⟨p.mask⊓b,p.trace,h,inf_le_left.trans p.valid⟩

theorem intersectMask_le_r426 (p : TotalCondition Q) (b : B) (h : p.mask⊓b≠⊥) :
    intersectMask p b h≤p :=
  ⟨inf_le_left,(inf_le_left.trans p.valid).trans (Q.refl p.trace)⟩

noncomputable def commonRefinementValue (Q : ValuedPoset B N) (n m : N) : B :=
  ⨆ r : N,Q.refines r n⊓Q.refines r m

theorem commonRefinementValue_forcesValid_r426 (Q : ValuedPoset B N) (n m : N) :
    commonRefinementValue Q n m≤Q.valid n⊓Q.valid m := by
  apply iSup_le
  intro r
  exact le_inf (inf_le_left.trans ((Q.refine_valid r n).trans inf_le_right))
    (inf_le_right.trans ((Q.refine_valid r m).trans inf_le_right))

theorem totalCompatible_iff_r426 (p q : TotalCondition Q) :
    Compatible p q ↔ (p.mask⊓q.mask)⊓commonRefinementValue Q p.trace q.trace≠⊥ := by
  classical
  constructor
  · rintro ⟨r,hrp,hrq⟩ he
    have h : r.mask≤(p.mask⊓q.mask)⊓commonRefinementValue Q p.trace q.trace :=
      le_inf (le_inf hrp.1 hrq.1) (le_iSup_of_le r.trace (le_inf hrp.2 hrq.2))
    exact r.nonzero (le_bot_iff.mp (h.trans_eq he))
  · intro h
    have hOne : ∃ r : N,(p.mask⊓q.mask)⊓(Q.refines r p.trace⊓Q.refines r q.trace)≠⊥ := by
      by_contra hn
      apply h
      rw [commonRefinementValue,inf_iSup_eq]
      have he (r : N) : (p.mask⊓q.mask)⊓(Q.refines r p.trace⊓Q.refines r q.trace)=⊥ := by
        by_contra hne
        exact hn ⟨r,hne⟩
      simp only [he,iSup_bot]
    obtain ⟨r,hr⟩ := hOne
    let a := (p.mask⊓q.mask)⊓(Q.refines r p.trace⊓Q.refines r q.trace)
    have ha1 : a≤Q.refines r p.trace := inf_le_right.trans inf_le_left
    have ha2 : a≤Q.refines r q.trace := inf_le_right.trans inf_le_right
    let S : TotalCondition Q :=
      ⟨a,r,hr,ha1.trans ((Q.refine_valid r p.trace).trans inf_le_left)⟩
    exact ⟨S,⟨inf_le_left.trans inf_le_left,ha1⟩,⟨inf_le_left.trans inf_le_right,ha2⟩⟩

end MarkedForcing
end JSP000933
