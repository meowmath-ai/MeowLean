import JSP000933SelectedIsoComplement

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem LocalEq.refl_r239 (h : Bool) (p : B) (x : ℕ → B) : LocalEq h p x x :=
  ⟨LocalLE.refl_r236 h p x,LocalLE.refl_r236 h p x⟩

theorem LocalEq.meet_congr_r239 {h : Bool} {p : B} {a b c d : ℕ → B}
    (ha : LocalEq h p a b) (hc : LocalEq h p c d) :
    LocalEq h p (bitsMeet a c) (bitsMeet b d) := by
  have hAC := LocalLE.meet_bounds_r237 h p a c
  have hBD := LocalLE.meet_bounds_r237 h p b d
  exact ⟨LocalLE.meet_right_r236.mpr ⟨hAC.1.trans_r236 ha.1,hAC.2.trans_r236 hc.1⟩,
    LocalLE.meet_right_r236.mpr ⟨hBD.1.trans_r236 ha.2,hBD.2.trans_r236 hc.2⟩⟩

theorem LocalEq.join_congr_r239 {h : Bool} {p : B} {a b c d : ℕ → B}
    (ha : LocalEq h p a b) (hc : LocalEq h p c d) :
    LocalEq h p (bitsJoin a c) (bitsJoin b d) := by
  have hAC := LocalLE.join_bounds_r237 h p a c
  have hBD := LocalLE.join_bounds_r237 h p b d
  exact ⟨LocalLE.join_left_r236.mpr ⟨ha.1.trans_r236 hBD.1,hc.1.trans_r236 hBD.2⟩,
    LocalLE.join_left_r236.mpr ⟨ha.2.trans_r236 hAC.1,hc.2.trans_r236 hAC.2⟩⟩

theorem LocalEq.compl_congr_r239 {h : Bool} {p : B} {a b : ℕ → B} (hEq : LocalEq h p a b) :
    LocalEq h p (bitsComplement a) (bitsComplement b) := by
  unfold LocalEq LocalLE at hEq ⊢
  rw [liveLE_compl_reverse_r235,liveLE_compl_reverse_r235]
  exact hEq.symm

def bitsSymmDiff (x y : ℕ → B) : ℕ → B :=
  bitsJoin (bitsMeet x (bitsComplement y)) (bitsMeet (bitsComplement x) y)

theorem SelectedQuotientIso.mapLocalEq_r239 {p : B} (F : SelectedQuotientIso B p)
    {x y : ℕ → B} (h : LocalEq false p x y) : LocalEq true p (F.toName x) (F.toName y) :=
  ⟨(F.order x y).mp h.1,(F.order y x).mp h.2⟩

theorem SelectedQuotientIso.mapSymmDiff_r239 {p : B} (F : SelectedQuotientIso B p) (x y : ℕ → B) :
    LocalEq true p (F.toName (bitsSymmDiff x y)) (bitsSymmDiff (F.toName x) (F.toName y)) := by
  unfold bitsSymmDiff
  have hL := (F.mapMeet_r237 x (bitsComplement y)).trans_r236
    (LocalEq.meet_congr_r239 (LocalEq.refl_r239 true p (F.toName x)) (F.mapCompl_r238 y))
  have hR := (F.mapMeet_r237 (bitsComplement x) y).trans_r236
    (LocalEq.meet_congr_r239 (F.mapCompl_r238 x) (LocalEq.refl_r239 true p (F.toName y)))
  exact (F.mapJoin_r237 _ _).trans_r236 (LocalEq.join_congr_r239 hL hR)

end SetLanguage
end JSP000933
