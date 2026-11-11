import Core.Generics.Check

/-!
# `()` 作类型实参

**问题**：`write_file` 要返回 `Result<(), Str>`，于是 `()` 要能作类型实参：`Ok(())` 的载荷、
`Vec<()>` 的元素、泛型函数里 `T = ()`。以前一律拒绝，因为 C 后端把 `()` 写成 `void`，没法放进字段和数组。

**模型**：`()` 只有一个值，不占资源：没有堆格子（`Datatypes.Recursive`、`Datatypes.Vec`），不用析构，复制它什么也不做。
所以它的类别是 `copy`，和 `I64`、`Bool` 一样。后端给它一个真实的表示（一个字节的结构体），只是为了能放进字段；
这个字节从来不读，不影响所有权。

**结论**：
- `unit_respects`：把任意一个类型参数换成 `()`（`copy`），约束仍然满足——不管它写没写 `T: linear`；
- `unit_instance_safe`：所以定义处检查通过的泛型函数，把某个参数换成 `()` 的实例照样安全、不泄漏，
  直接是 `Generics.Check` 的 `instance_safe`。不需要新的检查规则。
-/

namespace Core.Generics.UnitArg
open Core.Generics.Check

/-- `()` 的类别。 -/
def unitK : Kind := .copy

/-- 把第 `i` 个类型参数换成 `()`。 -/
def setUnit (θ : Nat → Kind) (i : Nat) : Nat → Kind := fun j => if j = i then unitK else θ j

theorem unit_respects {bnd : Nat → Bool} {θ : Nat → Kind} (hθ : Respects bnd θ) (i : Nat) :
    Respects bnd (setUnit θ i) := by
  intro j hj
  unfold setUnit unitK
  by_cases h : j = i
  · simp [h]
  · simp [h]; exact hθ j hj

/-- 所有类型参数都换成 `()` 也满足约束。 -/
theorem all_unit_respects (bnd : Nat → Bool) : Respects bnd (fun _ => unitK) := by
  intro j _
  simp [unitK]

/-- **结论**：定义处检查通过的泛型函数，把第 `i` 个类型参数换成 `()` 的实例安全、不泄漏。 -/
theorem unit_instance_safe (N : Nat) (Γ : Var → Ty) (bnd : Nat → Bool) (θ : Nat → Kind) (i : Nat) (g : G)
    (hg : genericOk N Γ bnd g = true) (hθ : Respects bnd θ) (fuel : Nat) (cs : List Bool) :
    let p := tr (fun x => instK (setUnit θ i) (Γ x)) g
    Core.Unified.Base.exec fuel p Core.Unified.Base.St.empty cs ≠ .err ∧
    ∀ st cs', Core.Unified.Base.exec fuel p Core.Unified.Base.St.empty cs = .ok st cs' →
      (∃ b, Core.Ownership.Branch.dropAll st.o.b N = some b ∧ ∀ l, b.live l = false) ∧
      (∀ l, st.l.live l = false) :=
  instance_safe N Γ bnd (setUnit θ i) g hg (unit_respects hθ i) fuel cs

end Core.Generics.UnitArg
