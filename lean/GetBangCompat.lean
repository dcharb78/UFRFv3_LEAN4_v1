import Mathlib

/-!
# List.get! Compatibility

Lean `v4.26.0-rc2` does not expose `List.get!` as a core field.
Provide a local compatibility alias used by protocol bridge files.
-/

namespace List

/-- Total list indexing with a default fallback from `Inhabited`. -/
def get! {α : Type _} [Inhabited α] (xs : List α) (i : Nat) : α :=
  xs.getD i default

/-- Compatibility alias for `List.bind` field-style usage. -/
def bind {α β : Type _} (xs : List α) (f : α → List β) : List β :=
  match xs with
  | [] => []
  | x :: xt => f x ++ bind xt f

end List
