import Core.Datatypes.Vec

/-!
# `vec_swap`——交换 Vec 的两个元素

`vec_swap(inout v, i, j)` 交换第 i、j 个元素（下标越界时 panic，不读内存）。`std.map` 用它在插入、删除时把元素挪到位。

**模型**：数组的格子 `k` 拥有元素的格子 `ks`（`Datatypes.Vec`）。交换只调换 `ks` 的顺序：换成 `ks` 的一个排列 `ns`。
拥有关系一个都没变（谁拥有谁不变，只是顺序），所以 `Datatypes.Vec` 的不变式保持（`permute_inv`），
作用域结束时照样全部析构、不泄漏（`inv_scope_end`）。`swap_perm`：交换两个位置确实是一个排列。
-/

namespace Core.Datatypes.VecSwap
open Core.Datatypes.Recursive (Cell Heap keys kids look dropList)
open Core.Datatypes.Vec (Inv setKids look_mem keys_set kids_set mem_set drop_total drop_inv no_leak)

/-- 把格子 `k` 的子格子换成它们的一个排列，不变式保持。 -/
theorem permute_inv {h : Heap} {roots : List Cell} {k : Cell} {ks ns : List Cell}
    (hI : Inv h roots) (hks : look h k = some ks) (hp : ks.Perm ns) : Inv (setKids h k ns) roots := by
  obtain ⟨r, hr⟩ := hI.rank
  have hkm := look_mem h k ks hks
  have p2 := kids_set h k ks ns hks
  refine ⟨by rw [keys_set]; exact hI.nd, ?_, ?_⟩
  · rw [keys_set]
    refine List.perm_iff_count.2 (fun a => ?_)
    have e1 := List.perm_iff_count.1 hI.own a
    have e2 := List.perm_iff_count.1 p2 a
    have e3 := List.perm_iff_count.1 hp a
    simp only [List.count_append] at e1 e2 ⊢
    omega
  · refine ⟨r, fun p ds he c hc => ?_⟩
    rcases mem_set h k ns (p, ds) he with he | he
    · exact hr p ds he c hc
    · simp only [Prod.mk.injEq] at he
      obtain ⟨e1, e2⟩ := he
      rw [e2] at hc
      rw [e1]
      exact hr k ks hkm c (hp.symm.subset hc)

/-- 满足不变式的状态，作用域结束时析构所有根成功，之后堆是空的（和 `Datatypes.Vec` 的 `scope_end` 一样，只是从不变式出发）。 -/
theorem inv_scope_end {h : Heap} {roots : List Cell} (hI : Inv h roots) :
    dropList (keys h).length h roots = some [] := by
  have hI' : Inv h (roots ++ []) := by rw [List.append_nil]; exact hI
  obtain ⟨h', e⟩ := drop_total _ h roots [] hI' (Nat.le_refl _)
  have := no_leak h' (drop_inv _ h roots [] h' hI' e)
  rw [e, this]

/-- 交换两个位置（`i < j`：前面 `pre`，中间 `mid`，后面 `post`）是一个排列。 -/
theorem swap_perm {α : Type} [DecidableEq α] (pre mid post : List α) (a b : α) :
    (pre ++ a :: mid ++ b :: post).Perm (pre ++ b :: mid ++ a :: post) := by
  refine List.perm_iff_count.2 (fun x => ?_)
  simp only [List.count_append, List.count_cons]
  omega

/-- **结论**：交换数组格子里的两个元素之后，不变式保持，作用域结束时全部析构、不泄漏。 -/
theorem swap_scope_end {h : Heap} {roots : List Cell} {k a b : Cell} {pre mid post : List Cell}
    (hI : Inv h roots) (hks : look h k = some (pre ++ a :: mid ++ b :: post)) :
    let h' := setKids h k (pre ++ b :: mid ++ a :: post)
    Inv h' roots ∧ dropList (keys h').length h' roots = some [] := by
  have hI' := permute_inv hI hks (swap_perm pre mid post a b)
  exact ⟨hI', inv_scope_end hI'⟩

end Core.Datatypes.VecSwap
