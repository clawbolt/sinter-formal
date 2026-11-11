/-!
# 文件与参数 IO 的规格

**内建函数**：
- `args() -> Vec<Str>`：命令行参数（不含程序名），每个都是新分配的字符串；
- `read_file(path: Str) -> Result<Str, Str>`：整个文件的字节；打不开或读不了时 `Err(说明)`；
- `write_file(path: Str, s: Str) -> Result<(), Str>`：把文件换成 `s`；失败时 `Err(说明)`。

**模型**：文件系统是“路径 → 内容”的部分函数，路径和内容都是字节列表。
所有权上它们和 `read_line` 一样：参数按借用读，返回的字符串是新的格子（`Datatypes.Str` 的 `new_str`），不需要新的安全证明。
这里证明的是行为：

- `read_write`：写成功之后读同一个路径，得到写进去的内容；
- `read_other`：写一个路径不改变别的路径；
- `write_atomic`：`write_file` 要么整个换成新内容，要么失败并且文件系统完全不变——**不会留下写了一半的文件**。
  这条规格决定了实现：先写到同目录的临时文件，再用 `rename` 换上去（POSIX 保证 `rename` 是原子的）；
  直接 `fopen(path, "w")` 再写，中途失败时原文件已经被清空，不满足这条。
- `read_missing`：读不存在的路径是 `Err`。
-/

namespace Core.Library.FileIO

abbrev Bytes := List Nat

/-- 文件系统：路径 → 内容（不存在时是 `none`）。 -/
def FS := Bytes → Option Bytes

inductive Res (α : Type)
  | ok (a : α)
  | err (msg : Bytes)

/-- `read_file`。 -/
def readF (fs : FS) (p : Bytes) : Res Bytes :=
  match fs p with
  | some s => .ok s
  | none => .err []

/-- 写成功后的文件系统。 -/
def put (fs : FS) (p s : Bytes) : FS := fun q => if q = p then some s else fs q

/-- `write_file`：`fail` 表示环境让它失败（磁盘满、没有权限……），由外界决定。
    实现（临时文件 + rename）保证的就是这个形状：失败时什么也没改。 -/
def writeF (fs : FS) (p s : Bytes) (fail : Option Bytes) : Res Unit × FS :=
  match fail with
  | some msg => (.err msg, fs)
  | none => (.ok (), put fs p s)

theorem read_write (fs : FS) (p s : Bytes) : readF (writeF fs p s none).2 p = .ok s := by
  simp [writeF, readF, put]

theorem read_other (fs : FS) (p q s : Bytes) (h : q ≠ p) (fail : Option Bytes) :
    readF (writeF fs p s fail).2 q = readF fs q := by
  cases fail with
  | some msg => rfl
  | none => simp [writeF, readF, put, h]

/-- **原子性**：结果是 `Err` 时文件系统不变；是 `Ok` 时恰好是把 `p` 换成 `s`。 -/
theorem write_atomic (fs : FS) (p s : Bytes) (fail : Option Bytes) :
    (∃ msg, writeF fs p s fail = (.err msg, fs)) ∨ writeF fs p s fail = (.ok (), put fs p s) := by
  cases fail with
  | some msg => exact Or.inl ⟨msg, rfl⟩
  | none => exact Or.inr rfl

theorem read_missing (fs : FS) (p : Bytes) (h : fs p = none) : ∃ msg, readF fs p = .err msg := by
  exact ⟨[], by simp [readF, h]⟩

/-- 写两次同一个路径，后一次为准。 -/
theorem write_write (fs : FS) (p s t : Bytes) :
    (writeF (writeF fs p s none).2 p t none).2 = (writeF fs p t none).2 := by
  funext q
  simp only [writeF, put]
  by_cases h : q = p <;> simp [h]

end Core.Library.FileIO
