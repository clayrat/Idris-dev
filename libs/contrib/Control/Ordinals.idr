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


{-
Eq SmallOrdinal where
  OrdZ            == OrdZ            = True
  (OrdS Z     xs) == OrdZ            = xs == OrdZ
  (OrdS (S k) xs) == OrdZ            = False
  OrdZ            == (OrdS Z     ys) = OrdZ == ys
  OrdZ            == (OrdS (S k) ys) = False
  (OrdS x     xs) == (OrdS y     ys) = x == y && xs == ys

namespace SmallOrdinal
  length : SmallOrdinal -> Nat
  length OrdZ = Z
  length (OrdS _ xs) = length xs

Ord SmallOrdinal where
  compare OrdZ            OrdZ            = EQ
  compare (OrdS Z     xs) OrdZ            = compare xs OrdZ
  compare (OrdS (S k) xs) OrdZ            = GT
  compare OrdZ            (OrdS Z     ys) = compare OrdZ ys
  compare OrdZ            (OrdS (S k) ys) = LT
  compare (OrdS x     xs) (OrdS y     ys) = (compare (length xs) (length ys) `thenCompare`
                                            (compare x y `thenCompare` compare xs ys))
                                            -}

-- The ordinals with a finite arithmetic representation.
-- In a way, these can be thought of as the "finite-dimensional" ordinals, where 
-- dimensions 0, 1, 2 correspond to (), Nat, and SmallOrdinal, respectively
data ArithOrdinal : (dim:Nat) -> Type where
  AOrdZ : ArithOrdinal dim
  AOrdS : ArithOrdinal dim -> ArithOrdinal (S dim) -> ArithOrdinal (S dim)

-- TODO: Add type-level ordering for ArithOrdinal. 
--       Possibly optimize ArithOrdinal for speed by adding knowledge and
--       reordering recursion direction.
{-
Eq (ArithOrdinal dim) where
  AOrdZ == AOrdZ = True
  (AOrdS x xs) == AOrdZ = x == AOrdZ && xs == AOrdZ
  AOrdZ == (AOrdS y ys) = AOrdZ == y && AOrdZ == ys
  (AOrdS x xs) == (AOrdS y ys) = x == y && xs == ys

mutual 
  Ordinal (ArithOrdinal dim) where
    degree AOrdZ = Z
    degree (AOrdS x y) = S (degree y)

  Ord (ArithOrdinal dim) where
    compare x AOrdZ = if (x == AOrdZ) then EQ else GT
    compare AOrdZ y = if (AOrdZ == y) then EQ else LT
    compare (AOrdS x xs) (AOrdS y ys) 
        = (compare (degree xs) (degree ys) `thenCompare`(compare x y `thenCompare` compare xs ys))
-}
