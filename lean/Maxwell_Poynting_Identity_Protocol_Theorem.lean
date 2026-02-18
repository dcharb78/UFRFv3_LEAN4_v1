import Mathlib

/-!
# Maxwell Poynting / Invariants Identity Protocol (Finite Anchors + Exact Algebra)

Lean companion to:
- `maxwell_poynting_identity_protocol.py` -> `maxwell_poynting_identity_results.json`

In natural units (`c=1`), define the standard electromagnetic invariants (vector form):
- `I1 := ‖E‖² - ‖B‖²`
- `I2 := E ⋅ B`
and the Poynting proxy direction/flux `S := E × B`.

Core algebraic identity (Lagrange):

`‖E×B‖² = ‖E‖² ‖B‖² - (E⋅B)²`

This file provides:
1) an exact (general) proof of the identity over any commutative ring, and
2) a small finite anchor example of a null field (`I1=0` and `I2=0`) on integer vectors.

No placeholders.
-/

namespace MaxwellPoyntingIdentityProtocol

-- A tiny explicit `ℝ³`-style vector carrier (we keep it ring-generic).
structure Vec3 (α : Type) where
  x : α
  y : α
  z : α

namespace Vec3

variable {α : Type}

def dot [Ring α] (u v : Vec3 α) : α :=
  u.x * v.x + u.y * v.y + u.z * v.z

def cross [Ring α] (u v : Vec3 α) : Vec3 α :=
  { x := u.y * v.z - u.z * v.y
    y := u.z * v.x - u.x * v.z
    z := u.x * v.y - u.y * v.x }

def norm2 [Ring α] (u : Vec3 α) : α :=
  dot u u

end Vec3

open Vec3

theorem lagrange_identity {α : Type} [CommRing α] (E B : Vec3 α) :
    norm2 (cross E B) = norm2 E * norm2 B - (dot E B) * (dot E B) := by
  cases E with
  | mk Ex Ey Ez =>
    cases B with
    | mk Bx By Bz =>
      simp [Vec3.dot, Vec3.cross, Vec3.norm2]
      ring

-- A fixed null-field anchor example (natural units): E ⟂ B and ‖E‖=‖B‖.
def E0 : Vec3 ℤ := { x := 1, y := 0, z := 0 }
def B0 : Vec3 ℤ := { x := 0, y := 1, z := 0 }

abbrev I1 (E B : Vec3 ℤ) : ℤ := Vec3.norm2 E - Vec3.norm2 B
abbrev I2 (E B : Vec3 ℤ) : ℤ := Vec3.dot E B

theorem null_plane_wave_anchor :
    I1 E0 B0 = 0 ∧ I2 E0 B0 = 0 ∧ Vec3.norm2 (Vec3.cross E0 B0) = 1 := by
  native_decide

end MaxwellPoyntingIdentityProtocol

