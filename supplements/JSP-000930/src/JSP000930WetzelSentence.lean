import JSP000933SetSentence

open Fol

namespace JSP000930
namespace SetLanguage

open JSP000933.SetLanguage

structure AnalyticPredicates where
  complex : ∀ {n : ℕ}, STerm n → SForm n
  entire : ∀ {n : ℕ}, STerm n → SForm n
  evaluates : ∀ {n : ℕ}, STerm n → STerm n → STerm n → SForm n

def ordinal_f {n : ℕ} (a : STerm n) : SForm n :=
  sEx fun x =>
    bd_and (bd_equal (up a) x) (Ord_f.cast (by omega))

def injects_f {n : ℕ} (a b : STerm n) : SForm n :=
  sEx fun x =>
    sEx fun y =>
      bd_and (bd_equal (up2 a) (up x))
        (bd_and (bd_equal (up2 b) y) (injects_into_f.cast (by omega)))

def sameCard_f {n : ℕ} (a b : STerm n) : SForm n :=
  bd_and (injects_f a b) (injects_f b a)

def strictCard_f {n : ℕ} (a b : STerm n) : SForm n :=
  bd_and (injects_f a b) (bd_not (injects_f b a))

def nextInitialCard_f {n : ℕ} (a b : STerm n) : SForm n :=
  bd_and (ordinal_f b)
    (bd_and (strictCard_f a b) (allIn b fun c => injects_f c (up a)))

def continuumAlephTwo_f : sentence L_ZFC :=
  sEx fun aOne =>
    sEx fun aTwo =>
      bd_and (nextInitialCard_f omega (up aOne))
        (bd_and (nextInitialCard_f (up aOne) aTwo)
          (sameCard_f aTwo omegaSubsets))

def continuumAlephOne_f : sentence L_ZFC :=
  sEx fun aOne =>
    bd_and (nextInitialCard_f omega aOne) (sameCard_f aOne omegaSubsets)

def familyEntire_f {n : ℕ} (A : AnalyticPredicates) (F : STerm n) : SForm n :=
  allIn F fun a => A.entire a

def evalImage_f {n : ℕ} (A : AnalyticPredicates) (F z W : STerm n) : SForm n :=
  sAll fun y =>
    bd_biimp (mem' y (up W))
      (bd_and (A.complex y) (exIn (up F) fun a => A.evaluates a (up2 z) (up y)))

def pointwiseBound_f {n : ℕ} (A : AnalyticPredicates) (F m : STerm n) : SForm n :=
  sAll fun z =>
    bd_imp (A.complex z)
      (sEx fun W =>
        bd_and (evalImage_f A (up2 F) (up z) W) (injects_f W (up2 m)))

def familyBoundAt_f {n : ℕ} (A : AnalyticPredicates) (m : STerm n) : SForm n :=
  sAll fun F =>
    bd_imp (bd_and (familyEntire_f A F) (pointwiseBound_f A F (up m)))
      (injects_f F (up m))

def wetzelBound_f (A : AnalyticPredicates) : sentence L_ZFC :=
  sAll fun m =>
    bd_imp (bd_and (ordinal_f m)
      (bd_and (strictCard_f omega m) (strictCard_f m omegaSubsets)))
      (familyBoundAt_f A m)

def wetzelCounterexample_f (A : AnalyticPredicates) : sentence L_ZFC :=
  bd_not (wetzelBound_f A)

def wetzelAtAlephTwoPos_f (A : AnalyticPredicates) : sentence L_ZFC :=
  bd_and continuumAlephTwo_f (wetzelBound_f A)

def wetzelAtAlephTwoNeg_f (A : AnalyticPredicates) : sentence L_ZFC :=
  bd_and continuumAlephTwo_f (wetzelCounterexample_f A)

end SetLanguage
end JSP000930
