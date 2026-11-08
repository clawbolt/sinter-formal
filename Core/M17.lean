import Core.M12

/-!
# M17：字符串 `Str`

**模型**：一个 `Str` 拥有一块堆内存（字节），在 M12 的堆里就是一个没有子格子的格子。

- 字面量 `"…"`、`str_concat(a, b)`、`str_clone(s)`、`str_from_i64(n)` 都分配一个新的格子（`alloc`，子格子为空），
  实参按借用读，不改拥有关系；
- `str_push(inout s, t)` 在原地追加，可能换地址（`realloc`），拥有关系不变，所以堆不变；
- `Str` 不是可复制的值：`let t = s` 是移动（M1）；作用域结束时析构（`drop`）；
- `Vec<Str>` 的 `push` / `pop` 就是 M12 的 `attach` / `detach`；
- `Str` 需要析构，所以不能放进区域（D4，M5c）；它不是 `linear`，忘了处理时由编译器自动析构。

**结论** `str_scope_end`：从空堆出发，任意夹杂着新建字符串的操作序列之后，作用域结束时析构所有根一定成功并且不泄漏。
这直接是 M12 的 `scope_end`；这里只证明“新建字符串”是 `Reach` 的一步。
-/

namespace Core.M17
open Core.M11 (Cell Heap keys dropList)

/-- 新建一个字符串：分配一个没有子格子的格子，成为新的根。 -/
theorem new_str {h : Heap} {roots : List Cell} {l : Cell} (hr : Core.M12.Reach h roots) (hl : l ∉ keys h) :
    Core.M12.Reach ((l, []) :: h) (l :: roots) := by
  have hr' : Core.M12.Reach h ([] ++ roots) := by rw [List.nil_append]; exact hr
  exact Core.M12.Reach.alloc hr' hl

/-- **结论**：作用域结束时析构所有根成功，之后堆是空的。 -/
theorem str_scope_end {h : Heap} {roots : List Cell} (hr : Core.M12.Reach h roots) :
    dropList (keys h).length h roots = some [] :=
  Core.M12.scope_end hr

/-! ## 例子

`let a = "ab"`（格子 1）、`let b = "c"`（格子 2）、`let c = str_concat(a, b)`（格子 3），作用域结束时三个都析构。 -/

example : Core.M12.Reach [(3, []), (2, []), (1, [])] [3, 2, 1] :=
  new_str (new_str (new_str Core.M12.Reach.empty (by decide)) (by decide)) (by decide)

example : dropList 3 [(3, []), (2, []), (1, [])] [3, 2, 1] = some [] := rfl

/-- `Vec<Str>`：把字符串（格子 2）放进数组（格子 5），只析构数组就释放了字符串。 -/
example : dropList 2 (Core.M12.setKids [(2, []), (5, [])] 5 [2]) [5] = some [] := rfl

/-- 忘了析构（`a` 还是根却没有析构）：堆里留下格子，就是泄漏。编译器在作用域结束时自动析构所有根。 -/
example : dropList 1 [(1, []), (2, [])] [2] = some [(1, [])] := rfl

end Core.M17
