import JSP000933ActualEventualError

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bitsMeet_absorb_r291 (a x : ℕ → B) : bitsMeet a (bitsMeet a x)=bitsMeet a x := by
  funext m
  simp only [bitsMeet,← inf_assoc,inf_idem]

theorem actualParityCap_payload_xor_r291 (c x : ℕ → B) (j : ℕ) :
    bitsSymmDiff (bitsMeet (actualParityCap c j false) x) (bitsMeet (actualParityCap c j true) x)=bitsMeet c x := by
  funext m
  have h := Nat.mod_lt (actualBand j m) (show 0<2 by decide)
  by_cases h0 : actualBand j m%2=0
  · have h1 : actualBand j m%2≠1 := by omega
    simp [bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement,actualParityCap,colorParity,h0,h1]
  · have h1 : actualBand j m%2=1 := by omega
    simp [bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement,actualParityCap,colorParity,h0,h1]

noncomputable def actualJoinedApprox {G : bSet B} {ks : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G ks p) (F : CoherentSelectedIso B p)
    (j : ℕ) (i : ℕ × ℕ) (x : ℕ → B) : ℕ → B :=
  bitsSymmDiff (actualSideApprox T F j i.1 false x) (actualSideApprox T F j i.2 true x)

theorem actualSide_countableTailApprox_r291 {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G (fun j => 8*k j) p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (j : ℕ) (hk : k j≠0) (b : Bool) (x : ℕ → B) :
    p≤⨆ l : ℕ, eventuallySmallError true (4*k j) (actualSideApprox T F j l b x)
      (F.toName (bitsMeet (actualParityCap T.freshCap j b) x)) := by
  let a := actualParityCap T.freshCap j b
  let y := bitsMeet a x
  let H := bitsMeet (F.toName a) (F.toName y)
  have hEq : LocalEq true p (F.toName y) H := by
    have h := (F.restrict_r246 (show p≤p from le_rfl)).mapMeet_r237 a y
    change LocalEq true p (F.toName (bitsMeet a y)) H at h
    exact (show bitsMeet a y=y from bitsMeet_absorb_r291 a x) ▸ h
  have hk8 : 8*k j≠0 := Nat.mul_ne_zero (by decide) hk
  have hErr : p≤eventuallySmallError true (8*k j) H (F.toName y) :=
    hEq.symm_r236.eventuallySmallError_r290 (8*k j) hk8
  have hApp := actualSide_countableApprox_r288 T F hF j b x
  change p≤⨆ l : ℕ, smallAllPrefixes true (8*k j) (bitsSymmDiff (actualSideApprox T F j l b x) H) at hApp
  apply (le_inf hApp hErr).trans
  rw [iSup_inf_eq]
  apply iSup_le
  intro l
  apply le_iSup_of_le l
  have hTri := eventuallySmallError_triangle_r290 true (4*k j) (actualSideApprox T F j l b x) H (F.toName y)
  rw [show 2*(4*k j)=8*k j by omega] at hTri
  exact (inf_le_inf_right _ (smallAllPrefixes_le_eventuallySmallError_r290 true (8*k j)
    (actualSideApprox T F j l b x) H)).trans hTri

theorem actualJoined_countableTailApprox_r291 {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G (fun j => 8*k j) p) (F : CoherentSelectedIso B p)
    (hF : ∀ x, p≤graphPairBits G false x (F.toName x))
    (j : ℕ) (hk : k j≠0) (x : ℕ → B) :
    p≤⨆ i : ℕ × ℕ, eventuallySmallError true (k j) (actualJoinedApprox T F j i x)
      (F.toName (bitsMeet T.freshCap x)) := by
  let u := bitsMeet (actualParityCap T.freshCap j false) x
  let v := bitsMeet (actualParityCap T.freshCap j true) x
  let W := bitsSymmDiff (F.toName u) (F.toName v)
  let Y := F.toName (bitsMeet T.freshCap x)
  have hEq : LocalEq true p Y W := by
    have h := (F.restrict_r246 (show p≤p from le_rfl)).mapSymmDiff_r239 u v
    change LocalEq true p (F.toName (bitsSymmDiff u v)) W at h
    have he : bitsSymmDiff u v = bitsMeet T.freshCap x := actualParityCap_payload_xor_r291 _ _ _
    rw [he] at h
    exact h
  have hNull := hEq.symm_r236.eventuallySmallError_r290 (2*k j) (Nat.mul_ne_zero (by decide) hk)
  have h0 := actualSide_countableTailApprox_r291 T F hF j hk false x
  have h1 := actualSide_countableTailApprox_r291 T F hF j hk true x
  apply (le_inf (le_inf h0 h1) hNull).trans
  rw [iSup_inf_iSup,iSup_inf_eq]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  have hX := eventuallySmallError_xorPairs_r290 true (2*k j)
    (actualSideApprox T F j i.1 false x) (F.toName u)
    (actualSideApprox T F j i.2 true x) (F.toName v)
  rw [show 2*(2*k j)=4*k j by omega] at hX
  have hTri := eventuallySmallError_triangle_r290 true (k j) (actualJoinedApprox T F j i x) W Y
  exact (inf_le_inf_right _ hX).trans hTri

end SetLanguage
end JSP000933
