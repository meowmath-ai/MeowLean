import JSP000933IndependentCrossingSmall

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def interleaveCrossQuad (a b c d : ℕ → B) : ℕ → B :=
  interleave4 (fun i => if i=0 then a else if i=1 then b else if i=2 then c else d)

@[simp] theorem crossCap_interleaveCrossQuad_r271 (a b c d : ℕ → B) :
    crossCap (interleaveCrossQuad a b c d)=a := by
  simp [crossCap,interleaveCrossQuad]

@[simp] theorem crossPay_interleaveCrossQuad_r271 (a b c d : ℕ → B) :
    crossPay (interleaveCrossQuad a b c d)=b := by
  simp [crossPay,interleaveCrossQuad]

@[simp] theorem crossOutCap_interleaveCrossQuad_r271 (a b c d : ℕ → B) :
    crossOutCap (interleaveCrossQuad a b c d)=c := by
  simp [crossOutCap,interleaveCrossQuad]

@[simp] theorem crossOutPay_interleaveCrossQuad_r271 (a b c d : ℕ → B) :
    crossOutPay (interleaveCrossQuad a b c d)=d := by
  simp only [crossOutPay,interleaveCrossQuad,extract4_interleave4_r240,
    ite_eq_right (show (3 : Fin 4)≠0 by decide),ite_eq_right (show (3 : Fin 4)≠1 by decide),
      ite_eq_right (show (3 : Fin 4)≠2 by decide)]

noncomputable def allowedActualSamplePrefix {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l k : ℕ) (x : ℕ → B) : B :=
  ⨆ u : {u : Word // u.length=4*actualSampleCut j k},
    closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u.val ⊓ cylinderValue x u.val

noncomputable def fixedActualSampleTree {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (x : ℕ → B) : B :=
  ⨅ k : ℕ, ⨅ _ : l≤k, ⨅ _ : k%2≠colorParity side, allowedActualSamplePrefix T j l k x

theorem fixedActualSampleTree_intro_r271 {G : bSet B} {ks : ℕ → ℕ} {p q : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (x : ℕ → B)
    (hx : q≤namedBranchCrossDomain G x) (hc : q≤ClosedMember (T.cover j) l x) :
    q≤fixedActualSampleTree T j l side x := by
  unfold fixedActualSampleTree
  apply le_iInf
  intro k
  apply le_iInf
  intro hl
  apply le_iInf
  intro hPar
  unfold allowedActualSamplePrefix
  apply le_of_dense_named_refinements_r219
  intro s hs hSQ
  obtain ⟨u,hu,t,ht,hts,hU⟩ :=
    exists_decided_initialWord_r136 x (4*actualSampleCut j k) s hs
  have htq := hts.trans hSQ
  have hOcc : t≤closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u :=
    le_iSup_of_le x (le_inf (htq.trans hx) (le_inf (htq.trans hc) hU))
  exact ⟨t,ht,hts,le_iSup_of_le ⟨u,hu⟩ (le_inf hOcc hU)⟩

theorem fixedActualSampleTree_apply_r271 {G : bSet B} {ks : ℕ → ℕ} {p q : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) (x : ℕ → B)
    (h : q≤fixedActualSampleTree T j l side x) (k : ℕ) (hl : l≤k) (hs : k%2≠colorParity side) :
    q≤allowedActualSamplePrefix T j l k x := by
  unfold fixedActualSampleTree at h
  exact h.trans ((iInf_le _ k).trans ((iInf_le _ hl).trans (iInf_le _ hs)))

theorem fixedActualSampleTree_mask_r271 {G : bSet B} {ks : ℕ → ℕ} {p q : B}
    (T : ActualBranchCrossingData G ks p) (j l : ℕ) (side : Bool) {x y : ℕ → B}
    (h : q≤realEqValue x y) :
    q⊓fixedActualSampleTree T j l side x=q⊓fixedActualSampleTree T j l side y := by
  unfold fixedActualSampleTree allowedActualSamplePrefix
  apply mask_iInf_congr_r126
  intro k
  by_cases hl : l ≤ k <;> by_cases hs : k % 2 ≠ colorParity side <;> simp [hl,hs]
  exact mask_iSup_congr_r126 (fun u => mask_inf_congr_r126 rfl (mask_cylinder_congr_r127 h u.val))

end SetLanguage
end JSP000933
