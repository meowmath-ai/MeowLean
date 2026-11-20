import JSP000933ActualJointResidualLocalization

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem localizedApproxSide_tail_r300 {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G (fun j => 8*(8*k j)) p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (P : ℕ → B) (j : ℕ) (hk : k j≠0) (b : Bool) (x : ℕ → B) :
    p≤⨆ i : ℕ × ℕ, eventuallySmallError true (4*k j) (localizedApproxSide T F P j i b x)
      (F.toName (bitsMeet (actualCoordinateFace T.freshCap P b) x)) := by
  let a := actualCoordinateFace T.freshCap P b
  let z := actualSectionPoint P b x
  let y := bitsMeet T.freshCap z
  let H := bitsMeet (F.toName a) (F.toName y)
  let Y := F.toName (bitsMeet a x)
  have hEq : LocalEq true p Y H := by
    have he := (F.restrict_r246 (show p≤p from le_rfl)).mapMeet_r237 a y
    change LocalEq true p (F.toName (bitsMeet a y)) H at he
    have hPayload : bitsMeet a y = bitsMeet a x := actualFace_section_payload_r298 T.freshCap P x b
    rw [hPayload] at he
    exact he
  have hk8 : 8*k j≠0 := Nat.mul_ne_zero (by decide) hk
  have hNull := hEq.symm_r236.eventuallySmallError_r290 (8*k j) hk8
  have hApp := actualJoined_countableTailApprox_r291 (k := fun j => 8*k j) T F hF j hk8 z
  apply (le_inf hApp hNull).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have hMask := eventuallySmallError_mask_r298 true (8*k j) (actualJoinedApprox T F j i z)
    (F.toName y) (F.toName a)
  have ht := eventuallySmallError_triangle_r290 true (4*k j) (localizedApproxSide T F P j i b x) H Y
  rw [show 2*(4*k j)=8*k j by omega] at ht
  exact (inf_le_inf_right _ hMask).trans ht

theorem localizedApproxPair_tail_r300 {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G (fun j => 8*(8*k j)) p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (P : ℕ → B) (j : ℕ) (hk : k j≠0) (x : ℕ → B) :
    p≤⨆ i : (ℕ × ℕ) × (ℕ × ℕ), eventuallySmallError true (k j) (localizedApproxPair T F P j i x)
      (F.toName (bitsMeet T.freshCap x)) := by
  let u := bitsMeet (actualCoordinateFace T.freshCap P false) x
  let v := bitsMeet (actualCoordinateFace T.freshCap P true) x
  let W := bitsSymmDiff (F.toName u) (F.toName v)
  let Y := F.toName (bitsMeet T.freshCap x)
  have hEq : LocalEq true p Y W := by
    have h := (F.restrict_r246 (show p≤p from le_rfl)).mapSymmDiff_r239 u v
    change LocalEq true p (F.toName (bitsSymmDiff u v)) W at h
    have hPayload : bitsSymmDiff u v = bitsMeet T.freshCap x := actualFaces_payload_xor_r298 T.freshCap P x
    rw [hPayload] at h
    exact h
  have hNull := hEq.symm_r236.eventuallySmallError_r290 (2*k j) (Nat.mul_ne_zero (by decide) hk)
  have h0 := localizedApproxSide_tail_r300 T F hF P j hk false x
  have h1 := localizedApproxSide_tail_r300 T F hF P j hk true x
  apply (le_inf (le_inf h0 h1) hNull).trans
  rw [iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have hX := eventuallySmallError_xorPairs_r290 true (2*k j)
    (localizedApproxSide T F P j i.1 false x) (F.toName u)
    (localizedApproxSide T F P j i.2 true x) (F.toName v)
  rw [show 2*(2*k j)=4*k j by omega] at hX
  exact (inf_le_inf_right _ hX).trans
    (eventuallySmallError_triangle_r290 true (k j) (localizedApproxPair T F P j i x) W Y)

structure ActualCountableContinuousApprox (p : B) (F : CoherentSelectedIso B p)
    (c : ℕ → B) (k : ℕ → ℕ) where
  approx : ℕ → ((ℕ × ℕ) × (ℕ × ℕ)) → (ℕ → B) → ℕ → B
  continuous : ∀ j i, NamedContinuousOn p (approx j i)
  error : ∀ j x, p≤⨆ i, eventuallySmallError true (k j) (approx j i x) (F.toName (bitsMeet c x))

theorem exists_sameBranch_actualContinuousApprox_r300 (G : bSet B) (k : ℕ → ℕ) (hk : ∀ j, k j≠0)
    {p : B} (F : CoherentSelectedIso B p)
    (hOCA : p≤namedCantorOCAValue B) (hG : p≤actualPreserveReflectValue G)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x)) :
    ∃ c : ℕ → B, (⊤ : B)≤actualLongBlockLarge c ∧ Nonempty (ActualCountableContinuousApprox p F c k) := by
  have hk64 (j : ℕ) : 8*(8*k j)≠0 := Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (by decide) (hk j))
  obtain ⟨T⟩ := exists_actualBranchCrossingData_r266 G (fun j => 8*(8*k j)) hk64 F hOCA hG hF
  obtain ⟨P,hP⟩ := exists_actual_lexRegular_sections_r299 T F
  exact ⟨T.freshCap,T.freshLarge_r266,
    ⟨⟨localizedApproxPair T F P,localizedApproxPair_continuous_r299 T F P hP,
      fun j x => localizedApproxPair_tail_r300 T F hF P j (hk j) x⟩⟩⟩

end SetLanguage
end JSP000933
