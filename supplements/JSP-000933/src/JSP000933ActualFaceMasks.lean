import JSP000933ActualClosedTailDichotomy

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def namedFacePoint (free fixed x : ℕ → B) (m : ℕ) : B :=
  (free m⊓x m)⊔((free m)ᶜ⊓fixed m)

def NamedPrefixMap (f : (ℕ → B) → ℕ → B) : Prop :=
  ∀ (p : B) (N : ℕ) (x y : ℕ → B), (∀ m<N, p⊓x m=p⊓y m) →
    ∀ m<N, p⊓f x m=p⊓f y m

theorem namedFacePoint_prefixMap_r305 (free fixed : ℕ → B) :
    NamedPrefixMap (namedFacePoint free fixed) := by
  intro p N x y he m hm
  exact mask_sup_congr_r211 (mask_inf_congr_r126 rfl (he m hm)) rfl

theorem NamedContinuousOn.comp_prefix_r305 {p : B} {f g : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) (hg : NamedPrefixMap g) :
    NamedContinuousOn p (fun x => f (g x)) := by
  intro x N q hq hqp
  obtain ⟨r,u,hr,hrq,hG,hM⟩ := h (g x) N q hq hqp
  obtain ⟨v,hv,t,ht,htr,hV⟩ := exists_decided_initialWord_r136 x u.length r hr
  refine ⟨t,v,ht,htr.trans hrq,hV,?_⟩
  intro y s hst hy
  have he : ∀ m<u.length, s⊓g x m=s⊓g y m :=
    hg s u.length x y (fun m hm => sameCylinder_mask_r261 (hst.trans hV) hy m (hv.symm ▸ hm))
  have hGx : s≤cylinderValue (g x) u := hst.trans (htr.trans hG)
  have hGy : s≤cylinderValue (g y) u :=
    ((le_inf le_rfl hGx).trans_eq (mask_cylinder_bounded_r278 u he)).trans inf_le_right
  exact hM (g y) s (hst.trans htr) hGy

theorem namedFacePoint_bit_of_free_r305 (free fixed x : ℕ → B) (m : ℕ) :
    free m⊓namedFacePoint free fixed x m=free m⊓x m := by
  unfold namedFacePoint
  rw [inf_sup_left]
  simp only [← inf_assoc,inf_idem,inf_compl_eq_bot',bot_inf_eq,sup_bot_eq]

theorem namedFacePoint_bit_of_fixed_r305 (free fixed x : ℕ → B) (m : ℕ) :
    (free m)ᶜ⊓namedFacePoint free fixed x m=(free m)ᶜ⊓fixed m := by
  unfold namedFacePoint
  rw [inf_sup_left]
  have hc : (free m)ᶜ⊓free m=⊥ := (inf_comm _ _).trans inf_compl_eq_bot'
  simp only [← inf_assoc,inf_idem,hc,bot_inf_eq,bot_sup_eq]

theorem namedFacePoint_mask_comm_r305 (free fixed x : ℕ → B) (m : ℕ) :
    namedFacePoint free fixed x m=namedFacePoint (bitsComplement free) x fixed m := by
  simp only [namedFacePoint,bitsComplement,compl_compl,sup_comm]

end SetLanguage
end JSP000933
