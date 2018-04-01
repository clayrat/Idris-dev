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
  constructor MkSmallOrdinal
  degree : Nat
  coefs : Vect degree Nat
  {proper : NoLeadZ coefs}

||| Wraps a properly formed `Vect _ Nat` of coefficients of powers of omega as a small ordinal.
smallOrdinal : (coefs:Vect _ Nat) -> {auto proper : NoLeadZ coefs} -> SmallOrdinal
smallOrdinal coefs {proper} = MkSmallOrdinal _ coefs {proper}

||| Casts a Vect _ Nat to a small ordinal, stripping any leading zeroes.
toSmallOrdinal : (coefs:Vect deg Nat) -> SmallOrdinal
toSmallOrdinal [] = smallOrdinal []
toSmallOrdinal (Z :: ns) = toSmallOrdinal ns
toSmallOrdinal ((S n) :: ns) = smallOrdinal ((S n) :: ns)

||| Lemma: Equal Vectors have equal tails. Doesn't assume equal length.
||| Should be moved to Data.Vect at some point.
vectTailInjective : {xs:Vect n a} -> {ys:Vect m a} -> {x,y:a} -> (x::xs)=(y::ys) -> xs=ys
vectTailInjective {xs=xs} {ys=xs} {x=x} {y=x} Refl = Refl

||| Lemma: Equal vectors have equal length.
||| Should be moved to Data.Vect at some point.
vectLengthInjective : {v:Vect n a} -> {w:Vect m a} -> v=w -> n=m
vectLengthInjective {v=w} {w=w} Refl = Refl

||| Shows that the degree of a small ordinal is the length of its vector of coefficients.
degreeIsLength : {deg:Nat} -> {v:Vect deg Nat} -> (oo:SmallOrdinal) -> 
                 (v = coefs oo) -> (deg = degree oo)
degreeIsLength {deg=(degree oo)} {v=(coefs oo)} oo Refl = Refl


Eq SmallOrdinal where
  (==) x y with (decEq (degree x) (degree y)) 
    (==) x (MkSmallOrdinal (degree x) v) | Yes Refl = coefs x == v
    | No _ = False

Ord SmallOrdinal where
  compare x y with (decEq (degree x) (degree y)) 
    compare x (MkSmallOrdinal (degree x) v) | Yes Refl = compare (coefs x) v
    | No _ = compare (degree x) (degree y) 

