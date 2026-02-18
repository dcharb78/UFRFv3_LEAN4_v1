import Mathlib

/-!
# Octonion "Fano Plane" Unit Multiplication: Nonassociativity Witness

Math folklore (and the Quanta article we reviewed) emphasizes the key qualitative jump:

* quaternions: associative but noncommutative,
* octonions: **nonassociative** (parentheses matter).

Mathlib does not (currently) ship a full octonion algebra development.
Instead, this file adds a *minimal, exact* Lean-certified witness that an
octonion-style multiplication table (the standard Fano-plane rule on the 7 imaginary units)
is not associative.

We restrict to the 16 signed basis units `{±1, ±e1, …, ±e7}`. Their product is always another
signed basis unit, so the table is closed.

No placeholders.
-/

namespace OctonionFano

/-!
## Basis and signed units
-/

inductive Base : Type
  | one | e1 | e2 | e3 | e4 | e5 | e6 | e7
  deriving DecidableEq, Repr

structure Unit : Type where
  neg : Bool
  base : Base
  deriving DecidableEq, Repr

def pos (b : Base) : Unit := ⟨false, b⟩
def neg (b : Base) : Unit := ⟨true, b⟩

def one : Unit := pos Base.one
def e1 : Unit := pos Base.e1
def e2 : Unit := pos Base.e2
def e3 : Unit := pos Base.e3
def e4 : Unit := pos Base.e4
def e5 : Unit := pos Base.e5
def e6 : Unit := pos Base.e6
def e7 : Unit := pos Base.e7

def neg_e6 : Unit := neg Base.e6

/-!
## Fano-plane orientation (positive products)

We encode the standard seven oriented triples (each yields three positive products):

* (1,2,3), (1,4,5), (1,6,7),
* (2,4,6), (2,5,7),
* (3,4,7), (3,5,6).
-/

def mulPos : Base → Base → Option Base
  | .e1, .e2 => some .e3
  | .e2, .e3 => some .e1
  | .e3, .e1 => some .e2
  | .e1, .e4 => some .e5
  | .e4, .e5 => some .e1
  | .e5, .e1 => some .e4
  | .e1, .e6 => some .e7
  | .e6, .e7 => some .e1
  | .e7, .e1 => some .e6
  | .e2, .e4 => some .e6
  | .e4, .e6 => some .e2
  | .e6, .e2 => some .e4
  | .e2, .e5 => some .e7
  | .e5, .e7 => some .e2
  | .e7, .e2 => some .e5
  | .e3, .e4 => some .e7
  | .e4, .e7 => some .e3
  | .e7, .e3 => some .e4
  | .e3, .e5 => some .e6
  | .e5, .e6 => some .e3
  | .e6, .e3 => some .e5
  | _, _ => none

/-!
## Basis multiplication with sign extraction

`mulBase i j = (b, k)` means `i*j = (-1)^b * k` on the basis.
-/

def mulBase : Base → Base → Bool × Base
  | .one, b => (false, b)
  | b, .one => (false, b)
  | i, j =>
      if _ : i = j then
        (true, .one) -- `eᵢ*eᵢ = -1`
      else
        match mulPos i j with
        | some k => (false, k)
        | none =>
            match mulPos j i with
            | some k => (true, k) -- reverse order flips sign
            | none => (false, .one) -- unreachable if `mulPos` is complete

def mul (x y : Unit) : Unit :=
  let (n, b) := mulBase x.base y.base
  ⟨Bool.xor x.neg (Bool.xor y.neg n), b⟩

instance : Mul Unit := ⟨mul⟩

/-!
## Concrete anchor identities + nonassociativity witness
-/

abbrev nonassoc_witness_statement : Prop :=
  (e1 * e2) * e5 ≠ e1 * (e2 * e5)

theorem e1_mul_e2 : e1 * e2 = e3 := by
  native_decide

theorem e2_mul_e5 : e2 * e5 = e7 := by
  native_decide

theorem e1_mul_e7 : e1 * e7 = neg_e6 := by
  native_decide

theorem nonassoc_witness : nonassoc_witness_statement := by
  native_decide

end OctonionFano
