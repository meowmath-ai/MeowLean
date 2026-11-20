import JSP000933ActualNestedFaceCompletion

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualLarge_uniformize_countable_r329 {p : B} (F : CoherentSelectedIso B p)
    (hF : NameMapExt F.toName) (c : ℕ → B) (hL : p≤actualLongBlockLarge c)
    (k : ℕ) (hk : k≠0) (f : ℕ → (ℕ → B) → ℕ → B)
    (hC : ∀ n, NamedContinuousOn p (f n))
    (hCov : ∀ x : ℕ → B, p≤⨆ n, eventuallySmallError true (64*k) (f n x) (F.toName (bitsMeet c x))) :
    p≤existsLargeUniformCapValue F.toName c k := by
  classical
  let V := existsLargeUniformCapValue F.toName c k
  let q := p⊓Vᶜ
  suffices hqBot : q≤⊥ by
    exact (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hqBot)).trans_eq (compl_compl V)
  by_contra hn
  have hqN : q≠⊥ := fun h => hn h.le
  have hqp : q≤p := inf_le_left
  have hNo : q≤Vᶜ := inf_le_right
  let State := {P : (ℕ → B) × (ℕ → B) //
    q≤bitsBelowValue P.1 c ∧ q≤actualLongBlockLarge P.1}
  have hStep (n : ℕ) (P : State) :
      ∃ Q : State, q≤faceRefinementValue P.val.1 P.val.2 Q.val.1 Q.val.2 ∧
        q≤namedFaceBadValue (f n) F.toName c (64*k) Q.val.1 Q.val.2 := by
    obtain ⟨a,z,hAZ⟩ := noUniform_has_actualBadChild_r326 F hF (f n) (hC n) c P.val.1 P.val.2
      k hk hqp hNo P.property.1 P.property.2
    have hRef : q≤faceRefinementValue P.val.1 P.val.2 a z := hAZ.trans inf_le_left
    have hAc : q≤bitsBelowValue a c := bitsBelowValue_trans_r324
      (hRef.trans inf_le_left) P.property.1
    exact ⟨⟨(a,z),hAc,hAZ.trans (inf_le_right.trans inf_le_left)⟩,
      hRef,hAZ.trans (inf_le_right.trans inf_le_right)⟩
  let start : State := ⟨(c,fun _ => ⊥),bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl),hqp.trans hL⟩
  let next (n : ℕ) (P : State) := Classical.choose (hStep n P)
  let S : ℕ → State := Nat.rec start next
  let a (n : ℕ) := (S n).val.1
  let z (n : ℕ) := (S n).val.2
  have hSig (n : ℕ) : q≤faceRefinementValue (a n) (z n) (a (n+1)) (z (n+1)) ∧
      q≤namedFaceBadValue (f n) F.toName c (64*k) (a (n+1)) (z (n+1)) :=
    Classical.choose_spec (hStep n (S n))
  let x := actualFaceLimit a z
  have hX (n : ℕ) : q≤faceMembershipValue (a n) (z n) x :=
    actualFaceLimit_in_all_r328 a z (fun n => (hSig n).1) n
  let E (n : ℕ) := eventuallySmallError true (64*k) (f n x) (F.toName (bitsMeet c x))
  have hBad (n : ℕ) : q≤(E n)ᶜ := by
    let y := namedFacePoint (a (n+1)) (z (n+1)) x
    have he : q≤realEqValue y x := hX (n+1)
    have h0 : q≤(eventuallySmallError true (64*k) (f n y) (F.toName (bitsMeet c y)))ᶜ :=
      (hSig n).2.trans (iInf_le _ x)
    have hEq := eventuallySmallError_mask_r313 true (64*k) ((hC n).realEq_mask_r323 hqp he)
      (hF q _ _ (realEqValue_bitsMeet_mask_r251 (le_top.trans_eq (realEqValue_refl_r127 c).symm) he))
    exact ((le_inf le_rfl h0).trans_eq (mask_compl_congr_r126 hEq)).trans inf_le_right
  have hGood : q≤⨆ n, E n := hqp.trans (hCov x)
  have hNot : q≤(⨆ n, E n)ᶜ := by
    rw [compl_iSup]
    exact le_iInf hBad
  exact hqN (le_bot_iff.mp ((le_inf hGood hNot).trans_eq inf_compl_eq_bot'))

end SetLanguage
end JSP000933
