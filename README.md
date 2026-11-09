# 核心演算的 Lean 4 证明

只依赖 Lean 核心库，不需要 Mathlib。

## 运行

```
cd lean
lake build
```

`lean-toolchain` 写的是 `leanprover/lean4:stable`。如果要固定版本，改成本机已安装的版本号即可，例如 `leanprover/lean4:v4.xx.0`。

## 状态

| 里程碑 | 文件 | 状态 |
|---|---|---|
| M1 所有权与移动（直线代码） | `Core/M1.lean` | 已通过机器检查（Lean v4.35.0） |
| M2a 作用域结束时自动释放、没有泄漏 | `Core/M2.lean` | 已通过机器检查（Lean v4.35.0） |
| M2b（上）一层分支与 drop flag | `Core/M2b.lean` | 已通过机器检查（Lean v4.35.0） |
| M2b（下·一）任意嵌套的分支 | `Core/M2n.lean` | 已通过机器检查（Lean v4.35.0） |
| M2b（下·二）循环 | `Core/M2L.lean` | 已通过机器检查（Lean v4.35.0） |
| M3（一）两参数调用与排他性 | `Core/M3.lean` | 已通过机器检查（Lean v4.35.0） |
| M3（二）n 个参数与求值顺序 | `Core/M3n.lean` | 已通过机器检查（Lean v4.35.0） |
| M4（一）投影与源对象锁定 | `Core/M4.lean` | 已通过机器检查（Lean v4.35.0） |
| M4（二）活跃性 | `Core/M4L.lean` | 已通过机器检查（Lean v4.35.0） |
| M4（三·上）投影与分支、循环 | `Core/M4C.lean` | 已通过机器检查（Lean v4.35.0） |
| M4（三·下）投影作为调用参数 | `Core/M4D.lean` | 已通过机器检查（Lean v4.35.0）；后来加入按 drop flag 析构 `dropIf`（静态变成“没有”，要求没被锁定；动态是 M2b 的 `dropOne`），`step2` 和 M7b 的 `bounded_check2` 补了这个情况 |
| M4（四）分支、循环上的活跃性分析 | `Core/M4E.lean` | 已通过机器检查（Lean v4.35.0） |
| M5（一）区域的基本模型 | `Core/M5.lean` | 已通过机器检查（Lean v4.35.0） |
| M5（二）协变与 `Mut` | `Core/M5b.lean` | 已通过机器检查（Lean v4.35.0） |
| M5（三）D4：区域里不放带 `Drop` 的值 | `Core/M5c.lean` | 已通过机器检查（Lean v4.35.0） |
| M5（四）D3：函数区域参数之间没有顺序 | `Core/M5d.lean` | 已通过机器检查（Lean v4.35.0） |
| M6（一）`linear` 值 | `Core/M6.lean` | 已通过机器检查（Lean v4.35.0） |
| M6（二）`errdefer` 与出错退出 | `Core/M6e.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（一）合并成一个演算：所有权、投影、`linear` | `Core/M7.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（二）合并演算加入调用 | `Core/M7b.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（三）合并演算加入 `errdefer` 与出错退出 | `Core/M7c.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（四·上）合并演算加入区域 | `Core/M7d.lean`（定义）、`Core/M7e.lean`（证明） | 已通过机器检查（Lean v4.35.0） |
| M7（四·下）合并演算里的 D4 | `Core/M7f.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（五·上）CFG 数据流检查（所有权 + 线性值） | `Core/M7g.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（五·下）CFG 加入区域与 errdefer | `Core/M7h.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（六）结构化 → CFG 翻译与对照测试 | `Core/M7i.lean` | 已通过（Lean v4.35.0）：第一组 14400 个程序，加上 errdefer 登记规则后两边结论完全相同（都接受 1729、都拒绝 12671；不加时只有 CFG 接受 463）；第二组 8000 个复杂循环体程序，两边结论完全相同（都接受 444、都拒绝 7556）；动态结果不一致 0 次 |
| M7（七·上）降级正确：模拟关系 | `Core/M7j.lean` | 已通过机器检查（Lean v4.35.0） |
| M7（七·下）降级正确：`lower` 满足嵌入关系 | `Core/M7k.lean` | 已通过机器检查（Lean v4.35.0） |
| C5 翻译验证：复核编译器导出的 CFG | `Core/C5.lean`（`compiler/validate.sh` 生成 `Validate/*.lean`） | 已通过：17 个可编译程序全部接受（含字符串的 c29_str、for 循环的 c30_for、break 的 c31_break、读取输入的 c32_input）（含部分移动的 c14_partial、分支里移走后放回的 c15_refill、多层部分移动的 c18_nested），12 个跳过编译器检查的反例全部被独立拒绝 |
| C5 后半：22400 个程序的三方对照 | `Core/C5b.lean`（打印成 Sinter 源码），`compiler/diff.sh` | 已通过：Lean 接受的 2173 个 sinterc 全部接受；sinterc 另外接受 985 个（自动析构，允许）；sinterc 接受的 3158 个各按 15 组选择运行，泄漏 0 次 |
| M8（一）枚举：构造、按移动的 `match`、按标签析构 | `Core/M8.lean` | 已通过机器检查（Lean v4.35.0） |
| M8（二）按借用的 `match` 与源对象锁定 | `Core/M8b.lean` | 已通过机器检查（Lean v4.35.0） |
| M9（一）泛型：定义处按抽象类型检查 | `Core/M9.lean` | 已通过机器检查（Lean v4.35.0）：定义处通过 ⇒ 每个满足约束的实例都通过，实例的安全与无泄漏由 M7（一）得到 |
| M10（一）trait 约束与静态派发 | `Core/M10.lean` | 已通过机器检查（Lean v4.35.0）：定义处通过、实例对每个约束都有参数约定一致的 `impl` ⇒ 实例通过；例子说明缺 `impl`、`impl` 把 `let` 改成 `sink` 都会被拒绝 |
| M11（一）递归类型：经过 `Box` 的链与树 | `Core/M11.lean` | 已通过机器检查（Lean v4.35.0）：从空堆出发经过分配、按移动拆开、析构，作用域结束时析构所有根一定成功（没有重复释放、一定结束），之后堆是空的（没有泄漏）；例子说明共享会重复释放、没有拥有者的环会泄漏 |
| M12（一）一般的拥有关系与动态数组 `Vec<T>` | `Core/M12.lean` | 已通过机器检查（Lean v4.35.0）：无环条件改成“存在秩”，加入 `attach`（`push`、往堆里的位置整体赋值）和 `detach`（`pop`）；从空堆出发经过任意这些操作，作用域结束时析构所有根成功且堆变空。补上了 M11（一）的 `Ordered` 不覆盖 `inout` 整体赋值的缺口 |
| M13（一）部分移动 | `Core/M13.lean` | 已通过机器检查（Lean v4.35.0）：按字段记状态，部分移动后其他字段照常可用，整体操作要求每个字段都在；每个结构体操作展开成 M2b 的语句，证明按字段检查接受 ⇒ 展开后 M2b 接受，于是按字段 drop flag 的释放不出错、结束时堆为空 |
| M14（一）区域参数与泛型实例化 | `Core/M14.lean` | 已通过机器检查（Lean v4.35.0）：函数体在定义处把区域参数当作抽象深度检查；调用处的实际区域保持声明的 outlives 顺序（`Mono`）且都活着（`Below`）时，按区域换名（参数区域换成实际区域、本地区域平移）得到的实例在调用处检查通过（`instance_accepted`），并由 M5 的 `sound` 得到执行不出错（`instance_safe`、`entry_safe`）；例子说明反向实例化被拒绝 |
| M15（一）含引用的数据类型 | `Core/M15.lean` | 已通过机器检查（Lean v4.35.0）：变量的值里有一组指针，静态信息记下值的类型里的区域（类型实参里的区域都算上）；`pack`、`empty`（`.None` 不含指针但类型带区域）、`read`；`safety_and_no_leak`：接受的程序执行不出错、结束时没有区域活着；反例说明漏掉类型实参的检查器会接受读取悬空指针的程序（`eraseP bad1`）；泛型函数换名对一组区域的情形没有重新证明 |
| M16（一）含引用的数据类型的协变 | `Core/M16.lean` | 已通过机器检查（Lean v4.35.0）：变量的类型固定，每个引用的位置一个区域；值的每个槽为空或指向一个不比类型里对应区域短命的区域；`copy` 逐个位置协变；`safety_and_no_leak`：接受的程序执行不出错、结束时没有区域活着；反方向复制被拒绝且不经检查执行出错；协变只对只读的值成立 |
| M17 字符串 `Str` | `Core/M17.lean` | 已通过机器检查（Lean v4.35.0）：`Str` 是没有子格子的格子；字面量、拼接、复制都是 `alloc`，追加只换地址；`str_scope_end` 由 M12 的 `scope_end` 得到 |
| M18 `for x in inout v` | `Core/M18.lean` | 已通过机器检查：循环体不提到 `v` 时下标都在界内、长度不变（`for_inout_ok`），反例 `bad_pop`；元素整体赋值由 M12 的操作组成（`replace_reach`），旧值析构后不泄漏（`replace_scope_end`） |
| M19 `panic` | `Core/M19.lean` | 已通过机器检查：CFG 加 `halt` 节点，编码成指向自己的空节点；`sim`：走到 `halt` 之前两种语义相同；`panic_safe`：编码后被 `cfgOk` 接受则执行不出错、正常或出错离开时干净 |
| S1 标准库 `std.math` 的规格 | `Core/S1.lean` | 已通过机器检查（Lean v4.35.0）：`Ord` 的四条定律；I64、Str（按字节字典序）的 `cmp` 满足；`min_of`、`max_of` 只依赖定律；`clamp`、`pow`、`sign` 的规格 |
| S2 标准库 `std.str`、`std.vec` 的规格 | `Core/S2.lean` | 已通过机器检查：`starts_with`、`find`（第一次出现 / 确实没有）、`trim`（只去头尾空白）、`join(split(s, sep), sep) == s`、`reverse` |
| S3 文件与参数 IO 的规格 | `Core/S3.lean` | 已通过机器检查：写后读、写一个路径不影响别的、读不存在的是 `Err`、两次写以后一次为准；`write_atomic`：失败时文件系统不变 |
| M9u `()` 作类型实参 | `Core/M9u.lean` | 已通过机器检查：`()` 是 `copy`；换进任何类型参数都满足约束（`unit_respects`）；实例安全、不泄漏（`unit_instance_safe`，由 M9 的 `instance_safe` 得到） |
| M20 `vec_swap` | `Core/M20.lean` | 已通过机器检查：把数组格子的子格子换成一个排列，M12 的不变式保持（`permute_inv`）；交换两个位置是排列（`swap_perm`）；交换后作用域结束时全部析构、不泄漏（`swap_scope_end`） |
| S4 标准库 `std.map` 的规格 | `Core/S4.lean` | 已通过机器检查：键严格递增的键值对列表；只依赖 `Ord` 的定律，插入、删除后仍有序（`ins_sorted`、`del_sorted`），插入后查得到（`lookup_ins`），删除后查不到（`lookup_del`），别的键不受影响（`lookup_ins_other`、`lookup_del_other`） |

M1 第一次编译时有 4 处 `omega` 失败（`omega` 不认 `abbrev Loc := Nat` 这个别名），改用 `Nat.lt_irrefl` 等引理后全部通过。后续里程碑避免在别名类型上用 `omega`。

## M1 证明了什么

- `safety`：检查器接受的程序，从空状态执行不会出错，也就是没有释放后使用、没有重复释放、没有通过已移走的变量访问已释放的内存。
- 不变式 `Inv` 的三条：拥有值的变量指向活着的位置；拥有者唯一；指针都指向已分配过的位置。
- 动态语义里 `move` 只拷贝指针、不清空旧变量，和真实机器一样。所以 `safety` 不是因为语义本身太保守才成立，而是检查器确实挡住了危险程序。文件末尾的最后一个例子演示了不经检查直接执行会出错。

## M1 还没覆盖的

- 泄漏：覆盖一个仍然拥有值的变量会泄漏，检查器拒绝这种情况，但还没有证明“程序结束时没有泄漏”。放到 M2，和作用域结束时的自动释放一起证明。
- 控制流、参数约定、投影、区域、`linear`：见报告附录 E 的里程碑表。
