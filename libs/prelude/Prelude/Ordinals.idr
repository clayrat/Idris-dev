||| Datatypes for representing well-orders larger than Nat. 
|||
||| Used in combination with WellFounded to show termination of 
||| functions where the decreasing argument can't be mapped monotonically
||| into Nat, or where no single argument is strictly decreasing, but some
||| combination of arguments is.
module Prelude.Ordinals

import Prelude.Nat
import Prelude.Algebra
import Prelude.Basics
import Prelude.Bool
import Prelude.Cast
import Prelude.Interfaces
import Prelude.Uninhabited
import Prelude.List

%default total
%access public export

interface Ord a => Ordinal (a:Type) where
  degree : a -> Nat

-- The ordinal numbers less than omega^omega, that is, those expressible 
-- as a sum of powers of omega with natural coefficients.
-- They are well-ordered, and so well-founded, with degree-lexicographical order.
data SmallOrdinal : Type where
  OrdZ  : SmallOrdinal
  OrdS  : Nat -> SmallOrdinal -> SmallOrdinal

-- The ordinals with a finite arithmetic representation.
-- In a way, these can be thought of as the finite-dimensional ordinals, where 
-- dimensions 0, 1, 2 correspond to (), Nat, and SmallOrdinal, respectively
data ArithOrdinal : (dim:Nat) -> Type where
  AOrdZ : ArithOrdinal dim
  AOrdS : ArithOrdinal dim -> ArithOrdinal (S dim) -> ArithOrdinal (S dim)

-- TODO: Add type-level ordering for ArithOrdinal
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

