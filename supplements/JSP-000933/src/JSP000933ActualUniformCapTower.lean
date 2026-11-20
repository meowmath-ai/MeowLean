import JSP000933ActualOneScaleUniformization

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem maskedSubcap_absorb_r330 {p : B} {d c : ℕ → B} (h : p≤bitsBelowValue d c) (x : ℕ → B) :
    p≤realEqValue (bitsMeet c (bitsMeet d x)) (bitsMeet d x) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  change p⊓(c m⊓(d m⊓x m))=p⊓(d m⊓x m)
  calc
    p⊓(c m⊓(d m⊓x m))=((p⊓d m)⊓c m)⊓x m := by ac_rfl
    _=(p⊓d m)⊓x m := by rw [inf_eq_left.mpr (bitsBelowValue_apply_r256 h m)]
    _=p⊓(d m⊓x m) := inf_assoc _ _ _

theorem meetInput_prefix_r330 (d : ℕ → B) : NamedPrefixMap (bitsMeet d) := by
  intro p N x y h m hm
  exact mask_inf_congr_r126 rfl (h m hm)

abbrev ApproxPairIndex := (ℕ × ℕ) × (ℕ × ℕ)

theorem actualCountableApprox_uniform_subcap_r330 {p : B} (F : CoherentSelectedIso B p)
    (hF : NameMapExt F.toName) (c d : ℕ → B) (k : ℕ → ℕ)
    (A : ActualCountableContinuousApprox p F c (fun j => 64*k j))
    (hD : p≤bitsBelowValue d c) (hL : p≤actualLongBlockLarge d) (j : ℕ) (hk : k j≠0) :
    p≤existsLargeUniformCapValue F.toName d (k j) := by
  let dec (i : ℕ) : ApproxPairIndex := (Encodable.decode (α := ApproxPairIndex) i).getD ((0,0),(0,0))
  let g (i : ℕ) (x : ℕ → B) := A.approx j (dec i) (bitsMeet d x)
  apply actualLarge_uniformize_countable_r329 F hF d hL (k j) hk g
    (fun i => (A.continuous j (dec i)).comp_prefix_r305 (meetInput_prefix_r330 d))
  intro x
  let y := bitsMeet d x
  have hY := A.error j y
  have hEq := hF p _ _ (maskedSubcap_absorb_r330 hD x)
  apply (le_inf le_rfl hY).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le (Encodable.encode i)
  unfold g dec
  rw [Encodable.encodek]
  exact (eventuallySmallError_mask_r313 true (64*k j)
    (le_top.trans_eq (realEqValue_refl_r127 (A.approx j i y)).symm) hEq).le.trans inf_le_right

theorem exists_actualUniformCapTower_r330 {p : B} (F : CoherentSelectedIso B p)
    (hF : NameMapExt F.toName) (c : ℕ → B) (k : ℕ → ℕ) (hk : ∀ j, k j≠0)
    (A : ActualCountableContinuousApprox p F c (fun j => 64*k j))
    (hL : p≤actualLongBlockLarge c) :
    ∃ d : ℕ → ℕ → B, d 0=c ∧ (∀ n, p≤actualLongBlockLarge (d n)) ∧
      (∀ n, p≤bitsBelowValue (d (n+1)) (d n)) ∧
      (∀ n, p≤existsNamedUniformValue F.toName (d (n+1)) (k n)) := by
  classical
  let S := {d : ℕ → B // p≤bitsBelowValue d c ∧ p≤actualLongBlockLarge d}
  have hStep (j : ℕ) (d : S) :
      ∃ e : S, p≤bitsBelowValue e.val d.val ∧ p≤existsNamedUniformValue F.toName e.val (k j) := by
    have h := actualCountableApprox_uniform_subcap_r330 F hF c d.val k A d.property.1 d.property.2 j (hk j)
    obtain ⟨e,he⟩ := exists_realName_maximum_r138 (largeUniformCapValue F.toName d.val (k j))
      (largeUniformCapValue_ext_r314 F.toName hF d.val (k j)) p h
    have hBelow : p≤bitsBelowValue e d.val := he.trans inf_le_left
    exact ⟨⟨e,bitsBelowValue_trans_r324 hBelow d.property.1,he.trans (inf_le_right.trans inf_le_left)⟩,
      hBelow,he.trans (inf_le_right.trans inf_le_right)⟩
  let start : S := ⟨c,bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl),hL⟩
  let step (j : ℕ) (d : S) := Classical.choose (hStep j d)
  let d : ℕ → S := Nat.rec start step
  exact ⟨fun n => (d n).val,rfl,fun n => (d n).property.2,
    fun n => (Classical.choose_spec (hStep n (d n))).1,
    fun n => (Classical.choose_spec (hStep n (d n))).2⟩

end SetLanguage
end JSP000933
