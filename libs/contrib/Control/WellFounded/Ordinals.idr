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

||| Small Ordinal LT: Proofs that `a` is less than `b`
||| @ a the smaller small ordinal
||| @ b the larger small ordinal
data SOrdLT  : (a, b : SmallOrdinal) -> Type where
  ||| If the `degree xs` is smaller than `degree ys`, `xs` is smaller than `ys`
  SOrdLTDegree : (deglt: LT n m) -> SOrdLT (MkSmallOrd n _) (MkSmallOrd m _) 
  ||| If degrees are equal, the coefficients determine order.
  SOrdLTCoefs  : (coefslt:VLT xs ys) -> SOrdLT (MkSmallOrd n xs) (MkSmallOrd n ys)

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

||| Get the lex order of the underlying vector from the order of ordinal
elimSOrdLTCoefs : (MkSmallOrd n xs `SOrdLT` MkSmallOrd n ys) -> (xs `VLT` ys)
elimSOrdLTCoefs (SOrdLTCoefs vlt) = vlt
elimSOrdLTCoefs (SOrdLTDegree lt) = void $ uninhabited lt


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

sOrdLtTransitive : (zLTy:z `SOrdLT` y) -> (yLTx:y `SOrdLT` x) -> z `SOrdLT` x
sOrdLtTransitive (SOrdLTDegree zdLTyd) (SOrdLTDegree ydLTxd) = SOrdLTDegree $ lteTransitive zdLTyd $ lteSuccLeft ydLTxd
sOrdLtTransitive (SOrdLTDegree deglt) (SOrdLTCoefs coefslt) = SOrdLTDegree deglt
sOrdLtTransitive (SOrdLTCoefs coefslt) (SOrdLTDegree deglt) = SOrdLTDegree deglt
sOrdLtTransitive (SOrdLTCoefs zsLTys) (SOrdLTCoefs ysLTxs) = SOrdLTCoefs $ vltTransitive zsLTys ysLTxs

sOrdHeadSuccRight : (xLTy:y `SOrdLT` MkSmallOrd (S xd') (xh::xt)) -> 
                    (y `SOrdLT` MkSmallOrd (S xd') (S xh::xt) {proper=NoLeadZCons _})
sOrdHeadSuccRight (SOrdLTDegree deglt) = SOrdLTDegree deglt
sOrdHeadSuccRight (SOrdLTCoefs coefslt) = SOrdLTCoefs (vltHeadSuccRight coefslt)

sOrdWellFounded : (x:SmallOrdinal) -> Accessible SOrdLT x
sOrdWellFounded (MkSmallOrd Z []) = Access $ \y,yLTx=> absurd yLTx
sOrdWellFounded (MkSmallOrd (S n') (xhc :: xtc) {proper}) = Access $ acc n' xhc xtc proper where
  acc : (xtd:Nat) -> (xh:Nat) -> (xt:Vect xtd Nat) -> (propX:NoLeadZ (xh::xt)) ->
        (y:SmallOrdinal) -> (yLTx:y `SOrdLT` (MkSmallOrd (S xtd) (xh :: xt) {proper=propX})) -> Accessible SOrdLT y
  acc xtd xh xt propX y yLTx with (wellFounded {rel=VLT} (xh::xt))
    acc _ _ _ _ (MkSmallOrd Z []) _ | _ = Access $ \z,zLTy=> absurd zLTy
    acc Z _ _ _ (MkSmallOrd (S _) _) (SOrdLTDegree (LTESucc LTEZero)) | _ impossible 
    acc (S xtd') xh (xth :: xt') propX (MkSmallOrd (S yd') (yh :: yt)) (SOrdLTDegree (LTESucc (LTESucc yd'LExtd'))) | _ with (decEq yd' xtd')
      acc (S xtd') xh (xth :: xt') propX (MkSmallOrd (S xtd') (yh :: yt)) (SOrdLTDegree (LTESucc (LTESucc yd'LExtd'))) | _
        | (Yes Refl) = Access $ \z,zLTy=>acc xtd' (S yh) yt (NoLeadZCons ItIsSucc) z (sOrdHeadSuccRight zLTy)
      acc (S xtd') xh (xth :: xt') propX (MkSmallOrd (S yd') (yh :: yt)) (SOrdLTDegree (LTESucc (LTESucc yd'LExtd')))  | _
        | (No neq) = Access $ \z,zLTy=>acc xtd' (S xh) xt' (NoLeadZCons ItIsSucc) z $
              sOrdLtTransitive zLTy $ SOrdLTDegree $ LTESucc $ lteNeqIsLt neq yd'LExtd'
    acc xtd xh xt propX (MkSmallOrd (S xtd) (yh :: yt) {proper=propY}) (SOrdLTCoefs coefslt) 
        | (Access recx) = Access $ \z,zLTy=>acc xtd yh yt propY z zLTy | recx (yh::yt) coefslt

WellFounded SOrdLT where
  wellFounded = sOrdWellFounded
                            
||| Interface of types with multiple ordered sizes, with later sizes being
||| allowed to grow if earlier sizes shrink at the same time.
||| The ordinal size is used for proofs of termination via accessibility.
|||
||| @ t the type whose elements can be mapped to SmallOrdinal
interface MultiSized t where
  multisize : t -> SmallOrdinal

SOrdSmaller : MultiSized t => t -> t -> Type
SOrdSmaller a b = multisize a `SOrdLT` multisize b

MultiSizeAccessible : MultiSized t => t -> Type
MultiSizeAccessible = Accessible SOrdSmaller

||| Proof of well-foundedness of `SOrdSmaller`.
||| Constructs accessibility for any given element of `t`, provided `MultiSized t`.
multisizeAccessible : MultiSized t => (x : t) -> MultiSizeAccessible x
multisizeAccessible x with (wellFounded {rel=SOrdLT} (multisize x)) 
  | (Access recX) = Access $ \y,yLTx=> multisizeAccessible y | (recX (multisize y) yLTx)

{- TODO: translate the rest of the LTE truths, where applicable
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
notLTImpliesGTE {a = S k} {b = S j} notLt = LTESucc (notLTImpliesGTE (notLt . LTESucc))
-}  
