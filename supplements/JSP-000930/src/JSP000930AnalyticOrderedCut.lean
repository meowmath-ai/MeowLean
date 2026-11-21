import JSP000930AnalyticArithmeticSyntax

open Fol JSP000933.SetLanguage

namespace JSP000930.AnalyticSyntax

def rationalCode_f {n : ℕ} (q : STerm n) : SForm n :=
  exIn omega fun a =>
    exIn omega fun b =>
      exIn omega fun d =>
        bd_and (bd_not (bd_equal d zero))
          (bd_equal (up3 q) (pair' (up2 a) (pair' (up b) d)))

def rationalNat_f {n : ℕ} (x q : STerm n) : SForm n :=
  bd_and (mem' x omega) (exIn omega fun one =>
    bd_and (successor_f zero one) (bd_equal (up q) (pair' (up x) (pair' zero one))))

def rationalNeg_f {n : ℕ} (q r : STerm n) : SForm n :=
  unpackRational_f q (fun _ : Fin 1 => r) (fun p a b d =>
    bd_equal (p 0) (pair' b (pair' a d)))

def rationalLE_f {n : ℕ} (q r : STerm n) : SForm n :=
  unpackRational_f q (fun _ : Fin 1 => r) (fun rs a b d =>
    unpackRational_f (rs 0) (fun i => ![a,b,d] i) (fun ps e f g =>
      crossOrder_f (ps 0) (ps 1) (ps 2) e f g))

def rationalLT_f {n : ℕ} (q r : STerm n) : SForm n :=
  bd_and (rationalLE_f q r) (bd_not (rationalLE_f r q))

def rationalAdd_f {n : ℕ} (a b c : STerm n) : SForm n :=
  rationalTernary_f a b c crossAdd_f

def rationalMul_f {n : ℕ} (a b c : STerm n) : SForm n :=
  rationalTernary_f a b c crossMul_f

def rationalEx_f {n : ℕ} (body : STerm (n+1) → SForm (n+1)) : SForm n :=
  sEx fun q => bd_and (rationalCode_f q) (body q)

def rationalAll_f {n : ℕ} (body : STerm (n+1) → SForm (n+1)) : SForm n :=
  sAll fun q => bd_imp (rationalCode_f q) (body q)

def validLowerParts_f {n : ℕ} (X : STerm n) : SForm n :=
  allIn X fun r => rationalAll_f fun q =>
    bd_imp (rationalLE_f q (up r)) (mem' q (up2 X))

def roundedParts_f {n : ℕ} (X : STerm n) : SForm n :=
  allIn X fun q => exIn (up X) fun r => rationalLT_f (up q) r

def realCut_f {n : ℕ} (X : STerm n) : SForm n :=
  bd_and (exIn X fun q => rationalCode_f q)
    (bd_and (allIn X fun q => rationalCode_f q)
      (bd_and (rationalEx_f fun r => bd_not (mem' r (up X)))
        (bd_and (validLowerParts_f X) (roundedParts_f X))))

def realLE_f {n : ℕ} (X Y : STerm n) : SForm n :=
  allIn X (fun q => mem' q (lift_bounded_term Y 1))

def realLT_f {n : ℕ} (X Y : STerm n) : SForm n :=
  bd_and (realLE_f X Y) (bd_not (bd_equal X Y))

def realNat_f {n : ℕ} (n0 X : STerm n) : SForm n :=
  rationalEx_f fun r => bd_and (rationalNat_f (up n0) r)
    (rationalAll_f fun q => bd_biimp (mem' q (up2 X)) (rationalLT_f q (up r)))

def realNegApprox_f {n : ℕ} (X q : STerm n) : SForm n :=
  rationalEx_f fun r => rationalEx_f fun mr =>
    bd_and (rationalNeg_f (up r) mr)
      (bd_and (bd_not (mem' (up r) (up2 X))) (rationalLT_f (up2 q) mr))

def realNeg_f {n : ℕ} (X Y : STerm n) : SForm n :=
  rationalAll_f fun q =>
    bd_biimp (mem' q (up Y)) (realNegApprox_f (up X) q)

def realAddApprox_f {n : ℕ} (X Y q : STerm n) : SForm n :=
  exIn X fun a => exIn (up Y) fun b => rationalEx_f fun c =>
    bd_and (rationalAdd_f (up2 a) (up b) c) (rationalLT_f (up3 q) c)

def realAdd_f {n : ℕ} (X Y Z : STerm n) : SForm n :=
  rationalAll_f fun q =>
    bd_biimp (mem' q (up Z)) (realAddApprox_f (up X) (up Y) q)

def rationalIntervalContainsReal_f {n : ℕ} (l X u : STerm n) : SForm n :=
  bd_and (mem' l X) (rationalEx_f fun b =>
    bd_and (rationalLT_f b (up u)) (bd_not (mem' b (up X))))

def belowProduct_f {n : ℕ} (q a b : STerm n) : SForm n :=
  rationalEx_f fun c =>
    bd_and (rationalMul_f (up a) (up b) c) (rationalLT_f (up q) c)

def realMulApprox_f {n : ℕ} (X Y q : STerm n) : SForm n :=
  rationalEx_f fun a => rationalEx_f fun b => rationalEx_f fun c => rationalEx_f fun d =>
    bd_and (rationalIntervalContainsReal_f (up3 a) (up2 (up2 X)) (up2 b))
      (bd_and (rationalIntervalContainsReal_f (up c) (up2 (up2 Y)) d)
        (bd_and (belowProduct_f (up2 (up2 q)) (up3 a) (up c))
          (bd_and (belowProduct_f (up2 (up2 q)) (up3 a) d)
            (bd_and (belowProduct_f (up2 (up2 q)) (up2 b) (up c))
              (belowProduct_f (up2 (up2 q)) (up2 b) d)))))

def realMul_f {n : ℕ} (X Y Z : STerm n) : SForm n :=
  rationalAll_f fun q =>
    bd_biimp (mem' q (up Z)) (realMulApprox_f (up X) (up Y) q)

end JSP000930.AnalyticSyntax
