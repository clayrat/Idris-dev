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

||| Nothing is smaller than zero
Uninhabited (SOrdLT _ (MkSmallOrd _ [])) where
  uninhabited (SOrdLTDegree deglt) = uninhabited deglt
  uninhabited (SOrdLTCoefs coefslt) = uninhabited coefslt

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

{-

  SOrdLTDegree : {auto deglt: LT n m} -> SOrdLT (MkSmallOrd n _) (MkSmallOrd m _) 
  ||| If degrees are equal, the coefficients determine order.
  SOrdLTCoefs  : {auto coefslt:VLT xs ys} -> SOrdLT (MkSmallOrd n xs) (MkSmallOrd n ys)
||| If two numbers are ordered, their predecessors are too
fromLteSucc (LTESucc x) = x

||| A decision procedure for `LTE`
isLTE : (m, n : Nat) -> Dec (m `LTE` n)
isLTE Z n = Yes LTEZero
isLTE (S k) Z = No succNotLTEzero
isLTE (S k) (S j) with (isLTE k j)
  isLTE (S k) (S j) | (Yes prf) = Yes (LTESucc prf)
  isLTE (S k) (S j) | (No contra) = No (contra . fromLteSucc)

||| `LTE` is reflexive.
lteRefl : LTE n n
lteRefl {n = Z}   = LTEZero
lteRefl {n = S k} = LTESucc lteRefl

||| n < m implies n < m + 1
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
