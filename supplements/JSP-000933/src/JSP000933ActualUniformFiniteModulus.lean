import JSP000933ActualPastStabilizer

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def boundedOpenCode (K : Word → B) (b : ℕ) (w : Word) : B := if w.length≤b then K w else ⊥

theorem boundedOpenCode_mono_r350 (K : Word → B) {a b : ℕ} (h : a≤b) (x : ℕ → B) :
    openValue (boundedOpenCode K a) x≤openValue (boundedOpenCode K b) x := by
  apply openValue_monoCode_r280
  intro w
  by_cases ha : w.length≤a
  · rw [boundedOpenCode,ite_eq_left ha,boundedOpenCode,ite_eq_left (ha.trans h)]
  · rw [boundedOpenCode,ite_eq_right ha]
    exact bot_le

theorem openValue_le_boundedCover_r350 (K : Word → B) (x : ℕ → B) :
    openValue K x≤⨆ b : ℕ, openValue (boundedOpenCode K b) x := by
  apply iSup_le
  intro w
  apply le_iSup_of_le w.length
  apply le_iSup_of_le w
  rw [boundedOpenCode,ite_eq_left le_rfl]

theorem actualOpenCover_has_boundedSubcover_r350 (K : Word → B) {p : B}
    (hK : ∀ x : ℕ → B, p≤openValue K x) :
    p≤⨆ b : ℕ, ⨅ x : ℕ → B, openValue (boundedOpenCode K b) x := by
  let U := fun b => ⨅ x : ℕ → B, openValue (boundedOpenCode K b) x
  let V := ⨆ b : ℕ, U b
  let q := p⊓Vᶜ
  have hQ : q≤⊥ := by
    by_contra hN
    have hPot : q≤closedPotential (boundedOpenCode K) [] := by
      apply le_iInf
      intro n
      have hq : q≤(U n)ᶜ := inf_le_right.trans (compl_le_compl (le_iSup _ n))
      rw [show (U n)ᶜ=⨆ x : ℕ → B, (openValue (boundedOpenCode K n) x)ᶜ by
        unfold U
        rw [compl_iInf]] at hq
      apply hq.trans
      apply iSup_le
      intro x
      apply le_iSup_of_le x
      apply le_inf
      · simp [cylinderValue]
      · exact le_iInf (fun i => compl_le_compl (boundedOpenCode_mono_r350 K i.isLt.le x))
    obtain ⟨x,_,hAll⟩ := exists_namedReal_allClosed_r225 q [] (boundedOpenCode K) hPot
    have hX := ((show q≤p from inf_le_left).trans (hK x)).trans (openValue_le_boundedCover_r350 K x)
    have hY : q≤(⨆ b : ℕ, openValue (boundedOpenCode K b) x)ᶜ := by
      rw [compl_iSup]
      exact le_iInf hAll
    exact hN ((le_inf hX hY).trans_eq inf_compl_eq_bot')
  exact (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hQ)).trans_eq (compl_compl V)

noncomputable def sameOutputPrefixValue (L : (ℕ → B) → ℕ → B) (n : ℕ) (x y : ℕ → B) : B :=
  ⨅ m : Fin n, bitEq (L x m.val) (L y m.val)

noncomputable def uniformOutputCylinderCode (L : (ℕ → B) → ℕ → B) (n : ℕ) (w : Word) : B :=
  ⨅ x : ℕ → B, ⨅ y : ℕ → B,
    imp (cylinderValue x w⊓cylinderValue y w) (sameOutputPrefixValue L n x y)

theorem uniformOutputCylinderCode_covers_r350 {p : B} {L : (ℕ → B) → ℕ → B}
    (hC : NamedContinuousOn p L) (n : ℕ) (x : ℕ → B) :
    p≤openValue (uniformOutputCylinderCode L n) x := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨r,u,hr,hrq,hU,hSame⟩ := hC x n q hq hqp
  refine ⟨r,hr,hrq,le_iSup_of_le u (le_inf ?_ hU)⟩
  apply le_iInf
  intro y
  apply le_iInf
  intro z
  apply (le_materialImp_iff_r126 _ _ _).mpr
  let s := r⊓(cylinderValue y u⊓cylinderValue z u)
  apply le_iInf
  intro m
  apply (le_bitEq_iff_r126 _ _ _).mpr
  exact (hSame y s inf_le_left (inf_le_right.trans inf_le_left) m.val m.isLt).symm.trans
    (hSame z s inf_le_left (inf_le_right.trans inf_le_right) m.val m.isLt)

def NamedOutputPrefixBound (L : (ℕ → B) → ℕ → B) (p : B) (b n : ℕ) : Prop :=
  ∀ (s : B), s≤p → ∀ x y : ℕ → B,
    (∀ m<b, s⊓x m=s⊓y m) → ∀ m<n, s⊓L x m=s⊓L y m

theorem exists_actualOutputPrefixBound_refinement_r350 {p q : B} {L : (ℕ → B) → ℕ → B}
    (hC : NamedContinuousOn p L) (n : ℕ) (hq : q≠⊥) (hqp : q≤p) :
    ∃ (b : ℕ) (r : B), r≠⊥ ∧ r≤q ∧ NamedOutputPrefixBound L r b n := by
  let K := uniformOutputCylinderCode L n
  have hc : q≤⨆ b : ℕ, ⨅ x : ℕ → B, openValue (boundedOpenCode K b) x :=
    hqp.trans (actualOpenCover_has_boundedSubcover_r350 K (uniformOutputCylinderCode_covers_r350 hC n))
  obtain ⟨b,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun b => ⨅ x : ℕ → B, openValue (boundedOpenCode K b) x) hc
  refine ⟨b,r,hr,hrq,?_⟩
  intro s hsr x y he m hm
  apply (le_bitEq_iff_r126 _ _ _).mp
  apply le_of_dense_named_refinements_r219
  intro t ht hts
  have hT : t≤openValue (boundedOpenCode K b) x := hts.trans (hsr.trans (hR.trans (iInf_le _ x)))
  obtain ⟨w,v,hv,hvt,hV⟩ := exists_nonzero_below_choice_r135 t ht
    (fun w => boundedOpenCode K b w⊓cylinderValue x w) hT
  have hLen : w.length≤b := by
    by_contra hn
    have h0 : v≤boundedOpenCode K b w := hV.trans inf_le_left
    rw [boundedOpenCode,ite_eq_right hn] at h0
    exact hv (le_bot_iff.mp h0)
  have hW : v≤K w := by
    simpa only [boundedOpenCode,ite_eq_left hLen] using (hV.trans inf_le_left : v≤boundedOpenCode K b w)
  have hx : v≤cylinderValue x w := hV.trans inf_le_right
  have hxy := mask_cylinder_bounded_r278 w
    (fun i hi => mask_under_r302 (hvt.trans hts) (he i (hi.trans_le hLen)))
  have hy : v≤cylinderValue y w := ((le_inf le_rfl hx).trans_eq hxy).trans inf_le_right
  have hl := (hW.trans (iInf_le _ x)).trans (iInf_le _ y)
  have hxy' : v ≤ sameOutputPrefixValue L n x y :=
    (le_inf le_rfl (le_inf hx hy)).trans ((le_materialImp_iff_r126 _ _ _).mp hl)
  exact ⟨v,hv,hvt,hxy'.trans (iInf_le _ (⟨m,hm⟩ : Fin n))⟩

end SetLanguage
end JSP000933
