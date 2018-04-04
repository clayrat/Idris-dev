||| Datatypes for representing well-orders larger than Nat. 
|||
||| Used in combination with WellFounded to show termination of 
||| functions where the decreasing argument can't be mapped monotonically
||| into Nat, or where no single argument is strictly decreasing, but some
||| combination of arguments is.
module Control.Ordinals

import Data.Vect

%default total
%access public export

||| Proofs that `v` doesn't have a leading zero.
data NoLeadZ : (v:Vect n Nat) -> Type where
  NoLeadZNil  : NoLeadZ Nil
  NoLeadZCons : IsSucc m -> NoLeadZ (m :: _)

||| The ordinal numbers less than omega^omega, that is, those expressible 
||| as a sum of powers of omega with natural coefficients.
||| They are well-ordered, and so well-founded, with degree-lexicographical order.
record SmallOrdinal where
  constructor MkSmallOrd
  degree : Nat
  coefs : Vect degree Nat
  {proper : NoLeadZ coefs}

||| Wraps a properly formed `Vect _ Nat` of coefficients of powers of omega as a small ordinal.
smallOrdinal : (coefs:Vect _ Nat) -> {auto proper : NoLeadZ coefs} -> SmallOrdinal
smallOrdinal coefs {proper} = MkSmallOrd _ coefs {proper}

||| Casts a Vect _ Nat to a small ordinal, stripping any leading zeroes.
toSmallOrdinal : (coefs:Vect deg Nat) -> SmallOrdinal
toSmallOrdinal [] = smallOrdinal []
toSmallOrdinal (Z :: ns) = toSmallOrdinal ns
toSmallOrdinal ((S n) :: ns) = smallOrdinal ((S n) :: ns)

||| Shows that the degree of a small ordinal is the length of its vector of coefficients.
degreeIsLength : {deg:Nat} -> {v:Vect deg Nat} -> (oo:SmallOrdinal) -> 
                 (v = coefs oo) -> (deg = degree oo)
degreeIsLength {deg=(degree oo)} {v=(coefs oo)} oo Refl = Refl


Eq SmallOrdinal where
  (==) x y with (decEq (degree x) (degree y)) 
    (==) x (MkSmallOrd (degree x) v) | Yes Refl = coefs x == v
    | No _ = False

Ord SmallOrdinal where
  compare x y with (decEq (degree x) (degree y)) 
    compare x (MkSmallOrd (degree x) v) | Yes Refl = compare (coefs x) v
    | No _ = compare (degree x) (degree y) 

||| Vector LT: Proofs that `xs` is lexicographically less than `ys`
||| @ xs the smaller small ordinal
||| @ ys the larger small ordinal
data VLT  : (xs, ys : Vect n Nat) -> Type where
  ||| If degrees are equal, but leading coefficients aren't, those determine order.
  VLTHead   : (headlt:LT x y) -> VLT (x::_) (y::_)
  ||| If both degree and head agree, tails recursively define order.
  VLTTail   : (taillt:VLT xs ys) -> VLT (h::xs) (h::ys)

||| Small Ordinal LT: Proofs that `a` is less than `b`
||| @ a the smaller small ordinal
||| @ b the larger small ordinal
data SOrdLT  : (a, b : SmallOrdinal) -> Type where
  ||| If the `degree xs` is smaller than `degree ys`, `xs` is smaller than `ys`
  SOrdLTDegree : (deglt: LT n m) -> SOrdLT (MkSmallOrd n _) (MkSmallOrd m _) 
  ||| If degrees are equal, the coefficients determine order.
  SOrdLTCoefs  : (coefslt:VLT xs ys) -> SOrdLT (MkSmallOrd n xs) (MkSmallOrd n ys)

||| Nil is not smaller than itself
Uninhabited (VLT _ []) where
  uninhabited lt impossible

Uninhabited (SOrdLT _ (MkSmallOrd _ [])) where
  uninhabited (SOrdLTDegree deglt) = uninhabited deglt
  uninhabited (SOrdLTCoefs coefslt) = uninhabited coefslt

||| Nothing is smaller than zero
noSOrdLTzero : Not (SOrdLT any (MkSmallOrd _ [] {proper=NoLeadZNil}) )
noSOrdLTzero = uninhabited

||| Strict greater than
total SOrdGT : SmallOrdinal -> SmallOrdinal -> Type
SOrdGT left right = SOrdLT right left

||| Less than or equal to
total SOrdLTE : SmallOrdinal -> SmallOrdinal -> Type
SOrdLTE left right = Either (SOrdLT left right) (left = right)

||| Greater than or equal to
total SOrdGTE : SmallOrdinal -> SmallOrdinal -> Type
SOrdGTE left right = SOrdLTE right left

||| Nothing is ever smaller than ordinal zero
consNotSOrdLTzero : Not ((MkSmallOrd _ _)`SOrdLT` (MkSmallOrd _ []))
consNotSOrdLTzero lt = uninhabited lt

||| A constructor is never less than or equal to zero.
consNotSOrdLTEzero : Not ((MkSmallOrd _ (_::_) )`SOrdLTE` (MkSmallOrd _ []))
consNotSOrdLTEzero (Left lt) = uninhabited lt
consNotSOrdLTEzero (Right Refl) impossible

||| Get the order of degrees from the order of ordinals
|||
||| Note that this yields an LTE, not an LT, due to not being able to exclude
||| the SOrdCoefs constructor
elimSOrdLTDegree : (MkSmallOrd n xs `SOrdLT` MkSmallOrd m ys) -> (n `LTE` m)
elimSOrdLTDegree (SOrdLTDegree (LTESucc x)) = lteSuccRight x
elimSOrdLTDegree {n = n} {m = n} (SOrdLTCoefs _) = lteRefl

--- Move this to Prelude.Nat eventually
Uninhabited (LTE (S n) n) where
  uninhabited (LTESucc lte) = uninhabited lte

--- Move this to Prelude.Nat eventually
||| `LTE` is antisymmetric
lteAntiSym : LTE n m -> LTE m n -> n = m
lteAntiSym LTEZero LTEZero = Refl
lteAntiSym (LTESucc x) (LTESucc y) = cong $ lteAntiSym x y

||| Get the lex order of the underlying vector from the order of ordinal
elimSOrdLTCoefs : (MkSmallOrd n xs `SOrdLT` MkSmallOrd n ys) -> (xs `VLT` ys)
elimSOrdLTCoefs (SOrdLTCoefs vlt) = vlt
elimSOrdLTCoefs (SOrdLTDegree lt) = void $ uninhabited lt

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
    


||| A decision procedure for `SOrdLT`
isSOrdLT : (a, b : SmallOrdinal) -> Dec (a `SOrdLT` b)
isSOrdLT (MkSmallOrd n xs) (MkSmallOrd m ys) with (isLTE (S n) m)
  isSOrdLT (MkSmallOrd n xs) (MkSmallOrd m ys) | (Yes lt) = Yes $ SOrdLTDegree lt
  isSOrdLT (MkSmallOrd n xs) (MkSmallOrd m ys) | (No nlt) with (decEq n m)
    isSOrdLT (MkSmallOrd m xs) (MkSmallOrd m ys) | (No nlt) | (Yes Refl) with (isVLT xs ys)
      isSOrdLT (MkSmallOrd m xs) (MkSmallOrd m ys) | (No nlt) | _ | (Yes vlt) = Yes (SOrdLTCoefs vlt)
      isSOrdLT (MkSmallOrd m xs) (MkSmallOrd m ys) | (No nlt) | _ | (No nvlt) = No (\solt=>
                                                     case solt of
                                                          (SOrdLTDegree deglt) => nlt deglt
                                                          (SOrdLTCoefs coefslt) => nvlt coefslt)
    isSOrdLT (MkSmallOrd n xs) (MkSmallOrd m ys) | (No nlt) | (No neq) = No (\solt=>
                                                   case solt of
                                                        (SOrdLTDegree deglt) => nlt deglt
                                                        (SOrdLTCoefs coefslt) => neq Refl)


||| `SOrdLTE` is reflexive.
sOrdLteRefl : SOrdLTE a a
sOrdLteRefl = Right Refl

||| `VLT` is transitive
vltTransitive : {x,y,z:Vect n Nat} -> (zLTy:z `VLT` y) -> (yLTx:y `VLT` x) -> z `VLT` x
vltTransitive {n=(S n')} {x=(xh::_)} {y=(yh::_)} {z=(zh::_)} (VLTHead zhLTyh) (VLTHead yhLTxh) 
    = VLTHead $ lteTransitive zhLTyh $ lteSuccLeft yhLTxh
vltTransitive {n=(S n')} {x=(h::_)} {y=(h::_)} {z=(zh::_)} (VLTHead zhLTh) (VLTTail taillt) = VLTHead zhLTh
vltTransitive {n=(S n')} {x=(xh::_)} {y=(h::_)} {z=(h::_)} (VLTTail taillt) (VLTHead hLTxh) = VLTHead hLTxh
vltTransitive {n=(S n')} {x=(h::x')} {y=(h::y')} {z=(h::z')} (VLTTail z'LTy') (VLTTail y'LTx') 
    = VLTTail $ vltTransitive z'LTy' y'LTx'

||| Interface of types with multiple ordered sizes, with later sizes being
||| allowed to grow if earlier sizes shrink at the same time.
||| The ordsize is used for proofs of termination via accessibility.
|||
||| @ t the type whose elements can be mapped to SmallOrdinal
interface MultiSized t where
  multisize : t -> SmallOrdinal

MultiSized SmallOrdinal where
  multisize = id

SOrdSmaller : MultiSized t => t -> t -> Type
SOrdSmaller a b = multisize a `SOrdLT` multisize b

MultiSizeAccessible : MultiSized t => t -> Type
MultiSizeAccessible = Accessible SOrdSmaller

-- Eventually move this to Prelude.Nat
lteNeqIsLt : (neq:Not (n = m)) -> (nLTEm:n `LTE` m) -> n `LT` m
lteNeqIsLt {n = Z} {m = Z} neq LTEZero = void $ neq Refl
lteNeqIsLt {n = Z} {m = (S k)} neq LTEZero = LTESucc LTEZero
lteNeqIsLt {n = (S n')} {m = (S m')} neq (LTESucc n'LTEm') = LTESucc $ lteNeqIsLt (neq . cong) n'LTEm'



wellOrderVectN : (x : Vect len Nat) -> Accessible VLT x
wellOrderVectN {len = Z} [] = Access (\y,yLTx => void $ uninhabited yLTx)
wellOrderVectN {len = (S _n)} (_xh :: _xt) = Access (acc _n _xh _xt) where
  acc : (n:Nat) -> (xh:Nat) -> (xt:Vect n Nat) -> 
        (y:Vect (S n) Nat) -> (yLTx:y `VLT` (xh::xt)) -> Accessible VLT y
  acc n (S xh') xt (yh :: yt) (VLTHead (LTESucc yhLTxh)) with (decEq xh' yh)
    acc n (S h') xt (h' :: yt) (VLTHead (LTESucc yhLTxh)) | Yes Refl = Access $ \z,zLTy=>acc n h' yt z zLTy
    acc n (S xh') xt (yh :: yt) (VLTHead (LTESucc yhLTxh)) | No neq 
      = Access $ \z,zLTy=>acc n xh' yt z $ vltTransitive zLTy $ VLTHead $ lteNeqIsLt (neq . sym) yhLTxh
  acc Z _ _ (_::_) (VLTTail _) impossible
  acc (S n') h (xh::xt) (h::yh::ytt) (VLTTail (VLTHead yhLTxh)) = Access $ 
            \(zh::zt),zLTy=> case zLTy of
                           (VLTHead zhLTh) => ?ho_1
                           (VLTTail ztLTyt) => ?ho_2
  acc (S n') h (h'::ys) (h::h'::xs) (VLTTail (VLTTail taillt)) = Access $ \z,zLTy=> ?hole
             
  {-
  acc n (S Z) xt (Z :: yt) (VLTHead (LTESucc xh'LTyh')) = Access $ \z,zLTy=>acc n Z yt z zLTy
  acc n (S (S xh'')) xt (Z :: yt) (VLTHead (LTESucc LTEZero)) 
    = Access $ \z,zLTy=>case z of
                   (Z :: z')     => acc n (S xh'') xt (Z :: z') (VLTHead (LTESucc LTEZero))
                   ((S j) :: xs) => case zLTy of (VLTHead headlt) => void $ uninhabited headlt
  acc n (S (S right)) xt ((S left) :: yt) (VLTHead (LTESucc (LTESucc x))) = Access $ \z,zLTy=>acc n (S right) xt z ?hole_4
  -}

 {- 
    = Access (\(zh::z'),zLTy=>case zLTy of 
                            (VLTHead headlt) => acc n xh' xt (zh::z') 
                                  (VLTHead $ lteTransitive headlt yhLTxh')
                            (VLTTail taillt) => acc n xh' xt (yh::z') (vltTransitive zLTy ?hole) )
                            -}
                            
||| Proof of well-foundedness of `SOrdSmaller`.
||| Constructs accessibility for any given element of `t`, provided `MultiSized t`.
multiSizeAccessible : MultiSized t => (x : t) -> MultiSizeAccessible x
multiSizeAccessible {t} x with (multisize x) proof msAsizeX 
  | (MkSmallOrd Z [] {proper = NoLeadZNil}) = Access (\y,yLTx=> -- Induction base: x=0 => y<x empty
                               void $ noSOrdLTzero (rewrite msAsizeX in yLTx))
  | (MkSmallOrd (S msAdxt) (msAxh :: msAxt) {proper = msAproper}) 
    = Access (rewrite sym msAsizeX in acc msAdxt msAxh msAxt msAproper) where
      -- We need unpacked arguments for acc because size change under a function doesn't count
      mutual
        acc : (dxt:Nat) -> (xh:Nat) -> (xt:Vect dxt Nat) -> (propX:NoLeadZ (xh::xt)) -> 
              (y : t) -> (solt:multisize y `SOrdLT` MkSmallOrd (S dxt) (xh::xt) {proper=propX}) -> MultiSizeAccessible y
        acc dxt xh xt propX y solt with (multisize y) proof sizeY
          acc _ _ _ _ _ _ | (MkSmallOrd Z [] {proper=NoLeadZNil}) =  
            Access (\z,zLTy=>void $ noSOrdLTzero (rewrite sizeY in zLTy)) -- y=0 => Accessible y
          acc Z _ _ _ _ (SOrdLTDegree (LTESucc LTEZero)) | (MkSmallOrd (S _) _) impossible -- x=1 => y=0
          acc (S dxt') xh (xth :: xtt) propX y (SOrdLTDegree (LTESucc (LTESucc mLTEk))) 
            | (MkSmallOrd (S dyt') (yh::yt)) = Access (\z, zLTy => acc dxt' (S yh) xtt _ z ?hole_1)
          acc dt (S xh') xt propX y (SOrdLTCoefs (VLTHead (LTESucc lts))) 
            | (MkSmallOrd (S dt) (yh::yt)) = Access (\z, zLTy => acc dt xh' xt _ z ?hole3)
          acc dt h xt prop2 y (SOrdLTCoefs (VLTTail taillt)) 
            | (MkSmallOrd (S dt) (h::yt)) = Access (\z, zLTy => tailacc y sizeY taillt zLTy)
        tailacc : (y : t) -> (sizeY : MkSmallOrd (S dt') (yh :: yt) = multisize y) -> 
                  (taillt : VLT yt xt) -> (zLTy : SOrdSmaller z y) -> Accessible SOrdSmaller z
        tailacc y sY {yt = (yth :: yt')} {xt = ((S xth') :: xt')} ((VLTHead (LTESucc lt))) {z} zLTy = Access (\q, qLTz => ?tailacc_rhs_4)
        tailacc y sY {yt = (th :: yt')} {xt = (th :: xt')} ((VLTTail taillt)) {z} zLTy = 
          Access (\q, qLTz => ?tailacc_rhs_2)

  {-
  acc sizeX y solt with (multisize y) proof sizeY
    acc (MkSmallOrd _ _) _ _ | (MkSmallOrd Z [] {proper=NoLeadZNil}) = 
      Access (\z,zLTy=>void $ noSOrdLTzero (rewrite sizeY in zLTy))
    acc (MkSmallOrd (S Z) _) _ (SOrdLTDegree (LTESucc LTEZero)) | (MkSmallOrd (S _) _) impossible
    acc (MkSmallOrd (S (S k))  (h :: th :: xs)) y (SOrdLTDegree (LTESucc (LTESucc lts))) 
            | (MkSmallOrd (S len) (yh :: ys)) = 
              Access (?temphole) --(\z,zLTy=>acc ?ordhole z ?relhole) --(MkSmallOrd ( k) (xs)) z ?acchole)
    acc (MkSmallOrd n ys) y (SOrdLTCoefs coefslt) | (MkSmallOrd n xs) 
        = Access (?hole_2)
        -}

{-
multiSizeAccessible x = Access (acc $ size x)
  where
    acc : (sizeX : Nat) -> (y : a) -> (size y `LT` sizeX) -> SizeAccessible y
    acc (S x') y (LTESucc yLEx')
        = Access (\z, zLTy => acc x' z (lteTransitive zLTy yLEx'))
        -}

{-
||| a < b implies a < b + 1
lteSuccRight : LTE n m -> LTE n (S m)
lteSuccRight LTEZero     = LTEZero
lteSuccRight (LTESucc x) = LTESucc (lteSuccRight x)


||| n + 1 < m implies n < m
lteSuccLeft : LTE (S n) m -> LTE n m
lteSuccLeft (LTESucc x) = lteSuccRight x

||| `LTE` is transitive
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)

lteAddRight : (n : Nat) -> LTE n (plus n m)
lteAddRight Z = LTEZero
lteAddRight (S k) = LTESucc (lteAddRight k)

||| If a number is not less than another, it is greater than or equal to it
notLTImpliesGTE : Not (LT a b) -> GTE a b
notLTImpliesGTE {b = Z} _ = LTEZero
notLTImpliesGTE {a = Z} {b = S k} notLt = absurd (notLt (LTESucc LTEZero))
notLTImpliesGTE {a = S k} {b = S j} notLt = LTESucc (notLTImpliesGTE (notLt . LTESucc))-}  
