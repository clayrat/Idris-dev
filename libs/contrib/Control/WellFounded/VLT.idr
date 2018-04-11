
||| Vector LT: Proofs that `xs` is lexicographically less than `ys`
||| @ xs the smaller small ordinal
||| @ ys the larger small ordinal
data VLT  : (xs, ys : Vect n Nat) -> Type where
  ||| If degrees are equal, but leading coefficients aren't, those determine order.
  VLTHead   : (headlt:LT x y) -> VLT (x::_) (y::_)
  ||| If both degree and head agree, tails recursively define order.
  VLTTail   : (taillt:VLT xs ys) -> VLT (h::xs) (h::ys)

||| Nil is not smaller than itself
Uninhabited (VLT _ []) where
  uninhabited lt impossible

--- Move this to Prelude.Nat eventually
Uninhabited (LTE (S n) n) where
  uninhabited (LTESucc lte) = uninhabited lte

--- Move this to Prelude.Nat eventually
||| `LTE` is antisymmetric
lteAntiSym : LTE n m -> LTE m n -> n = m
lteAntiSym LTEZero LTEZero = Refl
lteAntiSym (LTESucc x) (LTESucc y) = cong $ lteAntiSym x y

||| A decision procedure for `VLT`
isVLT : (xs, ys : Vect n Nat) -> Dec (xs `VLT` ys)
isVLT [] [] = No uninhabited
isVLT (x :: xs) (y :: ys) with (isLTE (S x) y)
  isVLT (x :: xs) (y :: ys) | (Yes lt) = Yes (VLTHead lt)
  isVLT (x :: xs) (y :: ys) | (No nlt) with (decEq x y)
    isVLT (y :: xs) (y :: ys) | (No nlt) | (Yes Refl) with (isVLT xs ys)
      isVLT (y :: xs) (y :: ys) | (No nlt) | (Yes Refl) | (Yes vlt) = Yes (VLTTail vlt)
      isVLT (y :: xs) (y :: ys) | (No nlt) | (Yes Refl) | (No nvlt) = No (\vlt=>
                 case vlt of
                      (VLTHead headlt) => nlt headlt
                      (VLTTail taillt) => nvlt taillt)
    isVLT (x :: xs) (y :: ys) | (No nlt) | (No neq) = No (\vlt=>
               case vlt of
                    (VLTHead headlt) => nlt headlt
                    (VLTTail taillt) => neq Refl)
    

||| `VLT` is transitive
vltTransitive : {x,y,z:Vect n Nat} -> (zLTy:z `VLT` y) -> (yLTx:y `VLT` x) -> z `VLT` x
vltTransitive {n=(S n')} {x=(xh::_)} {y=(yh::_)} {z=(zh::_)} (VLTHead zhLTyh) (VLTHead yhLTxh) 
    = VLTHead $ lteTransitive zhLTyh $ lteSuccLeft yhLTxh
vltTransitive {n=(S n')} {x=(h::_)} {y=(h::_)} {z=(zh::_)} (VLTHead zhLTh) (VLTTail taillt) = VLTHead zhLTh
vltTransitive {n=(S n')} {x=(xh::_)} {y=(h::_)} {z=(h::_)} (VLTTail taillt) (VLTHead hLTxh) = VLTHead hLTxh
vltTransitive {n=(S n')} {x=(h::x')} {y=(h::y')} {z=(h::z')} (VLTTail z'LTy') (VLTTail y'LTx') 
    = VLTTail $ vltTransitive z'LTy' y'LTx'

-- Eventually move this to Prelude.Nat
lteNeqIsLt : (neq:Not (n = m)) -> (nLEm:n `LTE` m) -> n `LT` m
lteNeqIsLt {n = Z} {m = Z} neq LTEZero = void $ neq Refl
lteNeqIsLt {n = Z} {m = (S k)} neq LTEZero = LTESucc LTEZero
lteNeqIsLt {n = (S n')} {m = (S m')} neq (LTESucc n'LTEm') = LTESucc $ lteNeqIsLt (neq . cong) n'LTEm'

addPrefixLt : (shared:Vect k Nat) -> (x:Vect n Nat) -> (z:Vect n Nat) -> 
             z `VLT` x -> shared++z `VLT` shared++x
addPrefixLt [] x z zLTx = zLTx
addPrefixLt (h :: shared') x z zLTx = VLTTail $ addPrefixLt shared' x z zLTx

remPrefixLt : (shared:Vect k Nat) -> (x:Vect n Nat) -> (z:Vect n Nat) -> 
             shared++z `VLT` shared++x -> z `VLT` x
remPrefixLt [] x z zLTx = zLTx
remPrefixLt (h :: shared') x z (VLTHead headlt) = absurd headlt
remPrefixLt (h :: shared') x z (VLTTail taillt) = remPrefixLt shared' x z taillt

accrec : {x:a} -> Accessible rel x -> (y:a) -> rel y x -> Accessible rel y
accrec (Access rec) = rec

consZPreservesAccess : (accx:Accessible VLT t) -> Accessible VLT (0::t)
consZPreservesAccess (Access rec) = Access $ \(yh::yt),(VLTTail ytLTx)=> consZPreservesAccess $ rec yt ytLTx

succPreservesAccess : {xt:Vect n Nat} -> (acch:Accessible VLT (xh::xt)) -> 
                      (ihyp: (it:Vect n Nat) -> Accessible VLT it) -> Accessible VLT (S xh::xt)
succPreservesAccess {xh = Z} (Access rech) ihyp = Access $ 
  \(yh::yt),yLTx=>case yLTx of
        (VLTHead (LTESucc yhLEZ)) => case yh of
                                      Z => consZPreservesAccess $ ihyp yt
                                      (S yh') => absurd yhLEZ
        (VLTTail taillt) => succPreservesAccess (rech (0::yt) (VLTTail taillt)) ihyp
succPreservesAccess {xh = (S xh')} (Access rech) ihyp = Access $ 
  \(yh::yt),yLTx => case yLTx of
        (VLTHead (LTESucc yhLExh)) => case decEq yh (S xh') of
                       (Yes eq) => rewrite eq in 
                                    succPreservesAccess (rech (xh'::yt) (VLTHead $ LTESucc lteRefl)) ihyp
                       (No neq) => rech (yh::yt) (VLTHead $ lteNeqIsLt neq yhLExh)
        (VLTTail taillt) => succPreservesAccess (rech (S xh'::yt) (VLTTail taillt)) ihyp

consPreservesAccess : {xt:Vect n Nat} -> (acct:Accessible VLT xt) -> 
                      (ihyp: (it:Vect n Nat) -> Accessible VLT it) -> Accessible VLT (xh::xt)
consPreservesAccess {n} {xh} {xt} acct ihyp = Access $ acc xh where
  acc : (h:Nat) -> (y:Vect (S n) Nat) -> (yLTx:y `VLT` (h::xt)) -> Accessible VLT y
  acc h (Z :: yt) yLTx = consZPreservesAccess (ihyp yt)
  acc Z _ (VLTHead (LTESucc _)) impossible
  acc (S xh') ((S yh') :: yt) (VLTHead (LTESucc x)) 
    = succPreservesAccess (accrec (consPreservesAccess {xh=xh'} acct ihyp) (yh'::yt) (VLTHead x)) ihyp
  acc (S yh') ((S yh') :: yt) (VLTTail taillt) 
    = succPreservesAccess (accrec (consPreservesAccess {xh=yh'} acct ihyp) (yh'::yt) (VLTTail taillt)) ihyp

inductVLTWellFounded : (n:Nat) -> (x:Vect n Nat) -> Accessible VLT x
inductVLTWellFounded Z [] = Access $  \y,yLTNil=>absurd yLTNil
inductVLTWellFounded (S k) (x :: xs) = consPreservesAccess (inductVLTWellFounded k xs) (inductVLTWellFounded k)

WellFounded VLT where
  wellFounded {n} x = inductVLTWellFounded n x

interface NSized (n:Nat) t where
  nsize : t -> Vect n Nat

VLTSmaller : NSized n t => t -> t -> Type
VLTSmaller {n} a b = nsize {n} a `VLT` nsize {n} b

NSizeAccessible : NSized n t => t -> Type
NSizeAccessible {n} = Accessible (VLTSmaller {n})

nsizeAccessible : NSized n t => (x:t) -> NSizeAccessible {n} x
nsizeAccessible {n} x with (wellFounded {rel=VLT} (nsize {n} x)) 
  | (Access recX) = Access $ \y,yLTx=> nsizeAccessible {n} y | (recX (nsize {n} y) yLTx)

vltHeadSuccRight : (xLTy:y `VLT` (xh::xt)) -> (y `VLT` (S xh::xt))
vltHeadSuccRight (VLTHead headlt) = VLTHead (lteSuccRight headlt)
vltHeadSuccRight (VLTTail taillt) = VLTHead lteRefl

