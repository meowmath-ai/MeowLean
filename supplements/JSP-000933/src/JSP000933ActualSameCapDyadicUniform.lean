import JSP000933ActualFiniteTailNullity

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem actualAlmostCut_localEq_r334 {p : B} (a d x : ℕ → B)
    (hA : p≤⨆ N : ℕ, afterCutDisjointValue a (bitsComplement d) N) :
    LocalEq false p (bitsMeet d (bitsMeet a x)) (bitsMeet a x) := by
  let U := bitsMeet d (bitsMeet a x)
  let V := bitsMeet a x
  suffices H : p≤liveLE false U V⊓liveLE false V U by
    exact ⟨H.trans inf_le_left,H.trans inf_le_right⟩
  apply le_of_dense_named_refinements_r219
  intro r hr hrp
  obtain ⟨N,q,hq,hqr,hQ⟩ := exists_nonzero_below_choice_r135 r hr
    (fun N => afterCutDisjointValue a (bitsComplement d) N) (hrp.trans hA)
  have hBits (m : ℕ) (hm : N≤ m) : q⊓U m=q⊓V m := by
    have hb := afterCutDisjointValue_apply_r268 hQ m hm
    have ha : q⊓a m≤d m :=
      (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr (by
        change (q⊓a m)⊓(d m)ᶜ≤⊥
        rw [inf_assoc]
        exact hb))).trans_eq (compl_compl _)
    change q⊓(d m⊓(a m⊓x m))=q⊓(a m⊓x m)
    calc
      q⊓(d m⊓(a m⊓x m))=((q⊓a m)⊓d m)⊓x m := by ac_rfl
      _=(q⊓a m)⊓x m := by rw [inf_eq_left.mpr ha]
      _=q⊓(a m⊓x m) := inf_assoc _ _ _
  have hEq := ordinaryLocalEq_late_agreement_r333 U V N hBits
  exact ⟨q,hq,hqr,le_inf hEq.1 hEq.2⟩

theorem namedUniform_almostRestrict_r334 {p : B} (F : CoherentSelectedIso B p) (a d : ℕ → B)
    (k : ℕ) (hk : k≠0) (hA : p≤⨆ N : ℕ, afterCutDisjointValue a (bitsComplement d) N)
    (hU : p≤existsNamedUniformValue F.toName d (2*k)) :
    p≤existsNamedUniformValue F.toName a k := by
  obtain ⟨f,hC,hE⟩ := existsNamedUniformValue_elim_r313 F.toName d (2*k) hU
  let g (x : ℕ → B) := f (bitsMeet a x)
  have hG : NamedContinuousOn p g := hC.comp_prefix_r305 (meetInput_prefix_r330 a)
  apply existsNamedUniformValue_intro_r313 F.toName a k hG
  unfold uniformTailErrorValue
  apply le_iInf
  intro x
  let U := bitsMeet d (bitsMeet a x)
  let V := bitsMeet a x
  have hEq := (F.restrict_r246 (show p≤p from le_rfl)).mapLocalEq_r239
    (actualAlmostCut_localEq_r334 a d x hA)
  have hNull : p≤eventuallySmallError true (2*k) (F.toName U) (F.toName V) :=
    hEq.eventuallySmallError_r290 (2*k) (Nat.mul_ne_zero (by decide) hk)
  have hF : p≤eventuallySmallError true (2*k) (g x) (F.toName U) := hE.trans (iInf_le _ (bitsMeet a x))
  exact (le_inf hF hNull).trans (eventuallySmallError_triangle_r290 true k (g x) (F.toName U) (F.toName V))

theorem exists_sameCap_namedUniformAll_r334 {p : B} (F : CoherentSelectedIso B p)
    (hF : NameMapExt F.toName) (c : ℕ → B) (k : ℕ → ℕ) (hk : ∀ j, k j≠0)
    (A : ActualCountableContinuousApprox p F c (fun j => 64*(2*k j))) (hL : p≤actualLongBlockLarge c) :
    ∃ a : ℕ → B, p≤bitsBelowValue a c ∧ p≤actualLongBlockLarge a ∧
      ∀ j, p≤existsNamedUniformValue F.toName a (k j) := by
  obtain ⟨d,hd0,hdLarge,hdD,hdApprox⟩ :=
    exists_actualUniformCapTower_r330 F hF c (fun j => 2*k j) (fun j => Nat.mul_ne_zero (by decide) (hk j)) A hL
  let a := actualBlockChoiceUnion p d
  refine ⟨a,?_,actualBlockChoiceUnion_large_r331 p d hdLarge,fun j => ?_⟩
  · have h := actualBlockChoiceUnion_belowFirst_r332 p d hdD
    exact h.trans_eq (congrArg (bitsBelowValue a) hd0)
  · exact namedUniform_almostRestrict_r334 F a (d (j+1)) (k j) (hk j)
      (actualBlockChoiceUnion_boundedDifference_r332 p d hdLarge hdD (j+1)) (hdApprox j)

end SetLanguage
end JSP000933
