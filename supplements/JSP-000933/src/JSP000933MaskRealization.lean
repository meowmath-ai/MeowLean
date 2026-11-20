import JSP000933CompleteDiagramLimit

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion BooleanNames CompleteDiagram

structure MaskRealization (B P : Type) [CompleteBooleanAlgebra B] [Preorder P] where
  mask : P → B
  positive : ∀ p, mask p ≠ ⊥
  monotone : Monotone mask
  realizes : ∀ b : B, b ≠ ⊥ → ∃ p, mask p = b
  cut : ∀ p b, mask p ⊓ b ≠ ⊥ → ∃ q ≤ p, mask q = mask p ⊓ b

namespace MaskRealization

variable {B P : Type} [CompleteBooleanAlgebra B] [Preorder P] (M : MaskRealization B P)

noncomputable def embed (b : B) : RO P :=
  ⨆ p : {p : P // M.mask p ≤ b}, imageCondition p.val

theorem image_le (p : P) (b : B) (h : M.mask p ≤ b) :
    imageCondition p ≤ M.embed b :=
  le_iSup (fun q : {q : P // M.mask q ≤ b} => imageCondition q.val) ⟨p,h⟩

theorem embed_disjoint {a b : B} (h : Disjoint a b) :
    Disjoint (M.embed a) (M.embed b) := by
  apply disjoint_iff_inf_le.mpr
  simp only [embed,iSup_inf_iSup]
  refine iSup_le fun ⟨p,q⟩ => disjoint_iff_inf_le.mp ?_
  by_contra hn
  obtain ⟨r,hrp,hrq⟩ := (compatible_iff_not_disjoint_r50 p.val q.val).mpr hn
  exact M.positive r (h.out _ ((M.monotone hrp).trans p.property)
    ((M.monotone hrq).trans q.property))

theorem image_le_iff (p : P) (b : B) : imageCondition p ≤ M.embed b ↔ M.mask p ≤ b := by
  constructor
  · intro h
    by_contra hn
    have hN : M.mask p ⊓ bᶜ ≠ ⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨r,hr,he⟩ := M.cut p bᶜ hN
    have h1 := (imageCondition_mono_r50 hr).trans h
    have h2 := M.image_le r bᶜ (he.trans_le inf_le_right)
    exact imageCondition_ne_bot_r50 r
      ((M.embed_disjoint (disjoint_compl_right : Disjoint b bᶜ)).out _ h1 h2)
  · exact M.image_le p b

theorem embed_mono : Monotone M.embed := by
  intro a b h
  apply iSup_le
  intro p
  exact M.image_le p.val b (p.property.trans h)

theorem reflect_order {a b : B} : M.embed a ≤ M.embed b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases ha : a = ⊥
    · rw [ha]; exact bot_le
    · obtain ⟨p,hp⟩ := M.realizes a ha
      exact hp.symm.trans_le ((M.image_le_iff p b).mp ((M.image_le p a hp.le).trans h))
  · intro h
    exact M.embed_mono h

theorem embed_top : M.embed ⊤ = ⊤ := by
  apply top_unique
  by_contra hn
  have hN : (M.embed ⊤)ᶜ ≠ ⊥ := fun he => hn (compl_eq_bot.mp he).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
  exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _ (M.image_le p ⊤ le_top) hp)

theorem embed_bot : M.embed ⊥ = ⊥ := by
  apply le_bot_iff.mp
  apply iSup_le
  intro p
  exact False.elim (M.positive p.val (le_bot_iff.mp p.property))

theorem embed_joins {D : Type} (v : D → B) : M.embed (⨆ d,v d) = ⨆ d,M.embed (v d) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    apply image_le_of_dense p.val
    intro q hqp
    have hQ : M.mask q ≤ ⨆ d,v d := (M.monotone hqp).trans p.property
    have hc : ∃ d, M.mask q ⊓ v d ≠ ⊥ := by
      by_contra hn
      have hZ (d : D) : M.mask q ⊓ v d = ⊥ := by
        by_contra hz
        exact hn ⟨d,hz⟩
      apply M.positive q
      calc
        M.mask q = M.mask q ⊓ (⨆ d,v d) := (inf_eq_left.mpr hQ).symm
        _ = ⨆ d,M.mask q ⊓ v d := inf_iSup_eq _ _
        _ = ⊥ := by simp only [hZ,iSup_bot]
    obtain ⟨d,hd⟩ := hc
    obtain ⟨r,hr,he⟩ := M.cut q (v d) hd
    exact ⟨r,hr,le_iSup_of_le d (M.image_le r _ (he.trans_le inf_le_right))⟩
  · exact iSup_le fun d => M.embed_mono (le_iSup v d)

theorem embed_compl (a : B) : M.embed aᶜ = (M.embed a)ᶜ := by
  classical
  symm
  apply IsCompl.compl_eq
  refine ⟨M.embed_disjoint disjoint_compl_right,codisjoint_iff_le_sup.mpr ?_⟩
  let v (d : Bool) : B := if d then aᶜ else a
  have hv : (⨆ d,v d) = ⊤ := by
    apply top_unique
    have h1 : a ≤ ⨆ d,v d := le_iSup_of_le false (by simp [v])
    have h2 : aᶜ ≤ ⨆ d,v d := le_iSup_of_le true (by simp [v])
    exact (sup_compl_eq_top (x := a)).symm.trans_le (sup_le h1 h2)
  calc
    (⊤ : RO P) = M.embed ⊤ := M.embed_top.symm
    _ = M.embed (⨆ d,v d) := congrArg M.embed hv.symm
    _ = ⨆ d,M.embed (v d) := M.embed_joins v
    _ ≤ _ := by
      apply iSup_le
      intro d
      cases d
      · simpa [v] using (le_sup_left : M.embed a ≤ M.embed a ⊔ M.embed aᶜ)
      · simpa [v] using (le_sup_right : M.embed aᶜ ≤ M.embed a ⊔ M.embed aᶜ)

theorem embed_inf (a b : B) : M.embed (a ⊓ b) = M.embed a ⊓ M.embed b := by
  apply le_antisymm
  · exact le_inf (M.embed_mono inf_le_left) (M.embed_mono inf_le_right)
  · by_contra hn
    have hN : (M.embed a ⊓ M.embed b) ⊓ (M.embed (a ⊓ b))ᶜ ≠ ⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
    have hA := (M.image_le_iff p a).mp (hp.trans (inf_le_left.trans inf_le_left))
    have hB := (M.image_le_iff p b).mp (hp.trans (inf_le_left.trans inf_le_right))
    exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _
      (M.image_le p _ (le_inf hA hB)) (hp.trans inf_le_right))

end MaskRealization

section Nontrivial
variable {B P : Type} [NontrivialCompleteBooleanAlgebra B] [Preorder P] [Nonempty P]
  (M : MaskRealization B P)

noncomputable def MaskRealization.nameCoefficients : NameCoefficients B (RO P) where
  map := M.embed
  map_top := M.embed_top
  map_inf := M.embed_inf
  map_compl := M.embed_compl
  map_iSup := M.embed_joins

noncomputable def MaskRealization.completeValueMap : CompleteValueMap B (RO P) where
  toFun := M.embed
  injective := fun _ _ h => le_antisymm (M.reflect_order.mp h.le) (M.reflect_order.mp h.ge)
  monotone := M.embed_mono
  map_bot := M.embed_bot
  map_top := M.embed_top
  map_compl := M.embed_compl
  map_inf := M.embed_inf
  map_iSup := M.embed_joins
  map_iInf := M.nameCoefficients.map_iInf

end Nontrivial
end ForcingTransport
end JSP000933
