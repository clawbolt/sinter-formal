/-!
# 基础定义

整个核心演算共用的小工具：用函数表示的有限映射，以及它的更新操作。
-/

namespace Core

abbrev Var := Nat
abbrev Loc := Nat

/-- 把映射 `f` 在 `k` 处改成 `v`。 -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun i => if i = k then v else f i

@[simp] theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) :
    upd f k v k = v := by
  simp [upd]

@[simp] theorem upd_other {α : Type} (f : Nat → α) {k i : Nat} (v : α) (h : i ≠ k) :
    upd f k v i = f i := by
  simp [upd, h]

end Core
