import JSP000933ActualGoodTailsRegularApprox

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def CoherentSelectedIso.restrictCoherent_r321 {p q : B} (F : CoherentSelectedIso B p) (hq : q≤p) :
    CoherentSelectedIso B q where
  toName := F.toName
  invName := F.invName
  orderMask x y := mask_under_r302 hq (F.orderMask x y)
  inv_ord x := (F.inv_ord x).of_stronger_r246 hq
  inv_har y := (F.inv_har y).of_stronger_r246 hq

theorem actualRegularUniform_to_continuous_r321 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (k : ℕ) (hk : k≠0) (f : (ℕ → B) → ℕ → B) (hR : NamedRegularOn p f)
    (hApp : ∀ x, p≤eventuallySmallError true (8*k) (f x) (F.toName (bitsMeet c x))) :
    p≤existsNamedUniformValue F.toName c k := by
  obtain ⟨P,hP⟩ := exists_actualComplementarySections_r296 hR.code p hR.dense
  let bFace (b : Bool) := actualCoordinateFace c P b
  let g (b : Bool) (x : ℕ → B) :=
    bitsMeet (F.toName (bFace b)) (f (actualSectionPoint P b x))
  have hG (b : Bool) : NamedContinuousOn p (g b) :=
    (hR.onSection_continuous_r320 P b (fun x => le_iInf (fun n => hP n b x))).meet_fixed_r297 (F.toName (bFace b))
  let L (x : ℕ → B) := bitsSymmDiff (g false x) (g true x)
  apply existsNamedUniformValue_intro_r313 F.toName c k ((hG false).xor_r297 (hG true))
  unfold uniformTailErrorValue
  apply le_iInf
  intro x
  have hSides (b : Bool) : p≤eventuallySmallError true (4*k) (g b x) (F.toName (bitsMeet (bFace b) x)) := by
    let a := bFace b
    let z := actualSectionPoint P b x
    let y := bitsMeet c z
    let H := bitsMeet (F.toName a) (F.toName y)
    let Y := F.toName (bitsMeet a x)
    have hEq : LocalEq true p Y H := by
      have he := (F.restrict_r246 (show p≤p from le_rfl)).mapMeet_r237 a y
      change LocalEq true p (F.toName (bitsMeet a y)) H at he
      have hPayload : bitsMeet a y = bitsMeet a x := actualFace_section_payload_r298 c P x b
      rw [hPayload] at he
      exact he
    have hk8 : 8*k≠0 := Nat.mul_ne_zero (by decide) hk
    have hN := hEq.symm_r236.eventuallySmallError_r290 (8*k) hk8
    have hz := (hApp z).trans (eventuallySmallError_mask_r298 true (8*k) (f z) (F.toName y) (F.toName a))
    have hTri := eventuallySmallError_triangle_r290 true (4*k) (g b x) H Y
    rw [show 2*(4*k)=8*k by omega] at hTri
    exact (le_inf hz hN).trans hTri
  let u := bitsMeet (bFace false) x
  let v := bitsMeet (bFace true) x
  let W := bitsSymmDiff (F.toName u) (F.toName v)
  let Y := F.toName (bitsMeet c x)
  have hEq : LocalEq true p Y W := by
    have h := (F.restrict_r246 (show p≤p from le_rfl)).mapSymmDiff_r239 u v
    change LocalEq true p (F.toName (bitsSymmDiff u v)) W at h
    have hPayload : bitsSymmDiff u v = bitsMeet c x := actualFaces_payload_xor_r298 c P x
    rw [hPayload] at h
    exact h
  have hNull := hEq.symm_r236.eventuallySmallError_r290 (2*k) (Nat.mul_ne_zero (by decide) hk)
  have hX := eventuallySmallError_xorPairs_r290 true (2*k) (g false x) (F.toName u) (g true x) (F.toName v)
  rw [show 2*(2*k)=4*k by omega] at hX
  exact (le_inf ((le_inf (hSides false) (hSides true)).trans hX) hNull).trans
    (eventuallySmallError_triangle_r290 true k (L x) W Y)

end SetLanguage
end JSP000933
