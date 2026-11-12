# 核心演算的 Lean 4 证明

编译器在单独的仓库 [sinterc](https://github.com/clawbolt/sinterc)；把两个仓库克隆到同一个目录下（`compiler`、`lean`），
编译器的 `validate.sh`、`diff.sh` 会用到这里的证明。

只依赖 Lean 核心库，不需要 Mathlib。

## 运行

```
cd lean
lake build
```

`lean-toolchain` 写的是 `leanprover/lean4:stable`。如果要固定版本，改成本机已安装的版本号即可，例如 `leanprover/lean4:v4.xx.0`。

## 内容

下面的文件都已通过机器检查（Lean v4.35.0）。模块名和路径一一对应：`Core.Ownership.Move` 就是 `Core/Ownership/Move.lean`。
各文件和以前的里程碑编号（M1、S4、C5 等）的对照见编译器的 CHANGELOG。

### 所有权 `Core/Ownership/`

| 文件 | 内容 |
|---|---|
| `Move.lean` | 所有权与移动（直线代码）：检查器接受的程序执行不出错（`safety`），见文末 |
| `Drop.lean` | 作用域结束时自动释放，没有泄漏 |
| `Branch.lean` | 一层分支与 drop flag |
| `Nested.lean` | 任意嵌套的分支 |
| `Loop.lean` | 循环 |
| `Partial.lean` | 部分移动：按字段记状态，部分移动后其他字段照常可用，整体操作要求每个字段都在；每个结构体操作展开成 `Ownership.Branch` 的语句，证明按字段检查接受 ⇒ 展开后 `Ownership.Branch` 接受，于是按字段 drop flag 的释放不出错、结束时堆为空 |

### 调用 `Core/Calls/`

| 文件 | 内容 |
|---|---|
| `Modes.lean` | 参数约定（`let` / `inout` / `sink`）与排他性，两参数调用 |
| `NArgs.lean` | n 个参数的调用与求值顺序 |

### 投影 `Core/Projection/`

| 文件 | 内容 |
|---|---|
| `Lock.lean` | 投影与源对象锁定 |
| `Liveness.lean` | 活跃性：投影的锁定只持续到最后一次使用 |
| `Branches.lean` | 投影与分支、循环 |
| `CallArg.lean` | 投影作为调用参数；按 drop flag 析构 `dropIf`（静态变成“没有”，要求没被锁定；动态是 `Ownership.Branch` 的 `dropOne`），`step2` 和 `Unified.Call` 的 `bounded_check2` 覆盖这个情况 |
| `Return.lean` | 返回借用的调用（`fn get(v: Vec<T>, i: I64) -> &T in v`）：调用之后返回的借用锁住以 `read` 传入的参数，和投影一样（`callOwn` 就是调用接着投影）；也可以借用传入的投影（`callBor`，锁住同一个源对象，比传入的投影活得长）；反例：不检查时借用还在就释放源对象，读到已释放的内存 |
| `Dataflow.lean` | 分支、循环上的活跃性分析 |

### 区域 `Core/Regions/`

| 文件 | 内容 |
|---|---|
| `Model.lean` | 区域的基本模型 |
| `Variance.lean` | 协变（D2）与 `Mut` |
| `NoDrop.lean` | D4：区域里不放带 `Drop` / `linear` 的值 |
| `Params.lean` | D3：函数的区域参数之间没有顺序 |
| `Generic.lean` | 区域参数与泛型实例化：函数体在定义处把区域参数当作抽象深度检查；调用处的实际区域保持声明的 outlives 顺序（`Mono`）且都活着（`Below`）时，按区域换名得到的实例在调用处检查通过（`instance_accepted`），并由 `Regions.Model` 的 `sound` 得到执行不出错（`instance_safe`、`entry_safe`）；反向实例化被拒绝 |
| `Data.lean` | 含引用的数据类型：静态信息记下值的类型里的区域（类型实参里的区域都算上）；`pack`、`empty`（`.None` 不含指针但类型带区域）、`read`；`safety_and_no_leak`；反例：漏掉类型实参的检查器会接受读取悬空指针的程序（`eraseP bad1`）。泛型函数换名对一组区域的情形没有重新证明 |
| `DataVariance.lean` | 含引用的数据类型的协变：值的每个槽为空或指向一个不比类型里对应区域短命的区域；`copy` 逐个位置协变；`safety_and_no_leak`；反方向复制被拒绝且不经检查执行出错；协变只对只读的值成立 |

### 线性值 `Core/Linearity/`

| 文件 | 内容 |
|---|---|
| `Linear.lean` | `linear` 值 |
| `Errdefer.lean` | `errdefer` 与出错退出 |

### 合并的演算 `Core/Unified/`

| 文件 | 内容 |
|---|---|
| `Base.lean` | 合并成一个演算：所有权、投影、`linear` |
| `Call.lean` | 加入调用 |
| `Errdefer.lean` | 加入 `errdefer` 与出错退出 |
| `RegionDefs.lean`、`RegionProofs.lean` | 加入区域（定义、证明） |
| `NoDrop.lean` | 合并演算里的 D4 |

### 控制流图 `Core/FlowGraph/`

| 文件 | 内容 |
|---|---|
| `Check.lean` | CFG 上的数据流检查（所有权 + 线性值） |
| `Region.lean` | CFG 加入区域与 errdefer |
| `Lower.lean` | 结构化程序 → CFG 的翻译与对照测试：第一组 14400 个程序，加上 errdefer 登记规则后两边结论完全相同（都接受 1729、都拒绝 12671；不加时只有 CFG 接受 463）；第二组 8000 个复杂循环体程序，两边结论完全相同（都接受 444、都拒绝 7556）；动态结果不一致 0 次 |
| `Simulation.lean` | 降级正确：模拟关系 |
| `Embed.lean` | 降级正确：`lower` 满足嵌入关系 |
| `Panic.lean` | `panic`：CFG 加 `halt` 节点，编码成指向自己的空节点；`sim`：走到 `halt` 之前两种语义相同；`panic_safe`：编码后被 `cfgOk` 接受则执行不出错、正常或出错离开时干净 |

### 编译器输出的检查 `Core/Checking/`

| 文件 | 内容 |
|---|---|
| `Validate.lean` | 翻译验证：复核编译器导出的 CFG（`compiler/validate.sh` 生成 `Validate/*.lean`）。`compiler/examples/ok/` 的程序全部接受，`examples/bad/` 里跳过编译器检查的反例全部被独立拒绝 |
| `Print.lean`、`Suite.lean` | 42000 个程序的三方对照（`compiler/diff.sh`）：`Print.lean` 把 `FlowGraph.Lower` 的程序和 `Suite.lean` 的第三组（整体移动、调用约定、闭包、泛型）打印成 Sinter 源码。第三组 19600 个程序在 Lean 里结构化和 CFG 结论相同（都接受 4301）；Lean 接受的 6474 个 sinterc 全部接受；sinterc 另外接受 2224 个（自动析构，允许）；sinterc 接受的 8698 个各按 15 组选择运行，泄漏 0 次。闭包按 `Closures.Param` 的模型当作一次调用（只读捕获按 read、被写按 inout） |

### 数据类型 `Core/Datatypes/`

| 文件 | 内容 |
|---|---|
| `Enum.lean` | 枚举：构造、按移动的 `match`、按标签析构 |
| `Recursive.lean` | 递归类型：经过 `Box` 的链与树。从空堆出发经过分配、按移动拆开、析构，作用域结束时析构所有根一定成功（没有重复释放、一定结束），之后堆是空的；共享会重复释放、没有拥有者的环会泄漏 |
| `Vec.lean` | 一般的拥有关系与动态数组 `Vec<T>`：无环条件改成“存在秩”，加入 `attach`（`push`、往堆里的位置整体赋值）和 `detach`（`pop`）；作用域结束时析构所有根成功且堆变空。补上了 `Recursive.lean` 的 `Ordered` 不覆盖 `inout` 整体赋值的缺口 |
| `Str.lean` | 字符串 `Str`：没有子格子的格子；字面量、拼接、复制都是 `alloc`，追加只换地址；`str_scope_end` 由 `Vec.lean` 的 `scope_end` 得到 |
| `VecInout.lean` | `for x in inout v`：循环体不提到 `v` 时下标都在界内、长度不变（`for_inout_ok`），反例 `bad_pop`；元素整体赋值由 `Vec.lean` 的操作组成（`replace_reach`），旧值析构后不泄漏（`replace_scope_end`） |
| `VecSwap.lean` | `vec_swap`：把数组格子的子格子换成一个排列，不变式保持（`permute_inv`）；交换两个位置是排列（`swap_perm`）；交换后全部析构、不泄漏（`swap_scope_end`） |

### 模式匹配 `Core/Matching/`

| 文件 | 内容 |
|---|---|
| `Borrow.lean` | 按借用的 `match` 与源对象锁定 |
| `Wildcard.lean` | 通配分支 `_`：覆盖检查 `covers` 通过时，把 `_` 展开成每个变体一个分支（带载荷时先析构载荷）一定成功（`expand_some`、`expand_length`）；展开后每个分支的检查结果就是编译器检查的结果（`wild_arm`、`expand_arm`），所以 `Datatypes.Enum` 的 `safety_and_no_leak` 照样成立（`wild_safe`）。字面量分支只是 if 链 |
| `Nested.lean` | 嵌套模式的展开：编译器把每个分支展开成只读的测试 `test` 和拆开取值的 `extract`；`test p v` 为真当且仅当 `pmatch p v` 成功（`test_eq`），成功时 `extract` 取出的绑定就是匹配给出的绑定（`extract_of_pmatch`）；按顺序测试、只拆开第一个通过的分支，结果和逐个分支匹配完全一样（`run_correct`） |
| `Coverage.lean` | 嵌套模式的覆盖检查：按类型枚举有限个代表值（写出的字面量各一个、再加一个“其他”），每个值都被某个代表值概括（`abs_match`、`abs_mem`）；代表值都有分支匹配时每个值都有分支匹配（`exhaustive_sound`）；报告的“永远匹配不到”是对的（`useful_complete`） |

### 泛型 `Core/Generics/`

| 文件 | 内容 |
|---|---|
| `Check.lean` | 定义处按抽象类型检查：定义处通过 ⇒ 每个满足约束的实例都通过，实例的安全与无泄漏由 `Unified.Base` 得到 |
| `UnitArg.lean` | `()` 作类型实参：`()` 是 `copy`；换进任何类型参数都满足约束（`unit_respects`）；实例安全、不泄漏（`unit_instance_safe`） |

### trait `Core/Traits/`

| 文件 | 内容 |
|---|---|
| `Static.lean` | trait 约束与静态派发：定义处通过、实例对每个约束都有参数约定一致的 `impl` ⇒ 实例通过；缺 `impl`、`impl` 把 `let` 改成 `sink` 都会被拒绝 |
| `ImplSearch.lean` | 泛型 impl 的查找：`WF`、`Coherent` 下查找成功当且仅当有推导（`solve_sound`、`solve_complete`，查找会停），适用的 impl 至多一个（`impl_unique`），定义处查得到的约束在实例里也查得到（`instance_resolves`）——单态化不会因为找不到 impl 而失败。默认方法是约束 `Self: trait` 的泛型函数，直接用 `Static.lean` |
| `Inherent.lean` | 类型自己的方法（`impl 类型 { }`）：按接收者类型查找，先查方法、再查约束里的 trait、否则报错，不落到全局函数。`CoherentM` 下能匹配的方法一定被查到、和书写顺序无关（`resolve_complete`）；落到 trait 时实例里 impl 查得到（`resolve_tra_instance`）；查到方法时换掉类型参数仍是同一个函数（`resolve_stable`）。反例：头部重叠时按顺序查到不同的函数；落到 trait 的调用在实例里重新查会变，所以只在定义处查一次 |

### 闭包 `Core/Closures/`

| 文件 | 内容 |
|---|---|
| `Param.lean` | 当实参传的闭包。排他性：捕获当作调用处的额外实参按 `Calls.NArgs` 的规则检查；`inner_ok`、`two_levels`；`for_each(v, \|x\| v.push(x))` 被拒绝。不会悬空：每个帧里的闭包只引用更靠下的帧（`good_reach`）；调用闭包时它的帧还在（`clo_live`）；帧返回后没有引用它的闭包（`pop_clean`）；反例：允许返回闭包时不成立 |
| `CapRef.lean` | 闭包捕获引用：捕获的区域在提升出的函数里是区域参数，调用时按 `Regions.Generic` 实例化；`capture_below`、`capture_mono`、`capture_safe`；反例：已结束的区域不满足 `Below` |
| `Stored.lean` | 可以存起来的闭包 `Fn(T) -> U` 和 trait 对象 `dyn Tr`。不会悬空：`pack` 的值环境按值拥有，不变式照旧（`good_reach`、`clo_live`、`pop_clean`、`pack_clean`）；排他性：闭包体从实参访问的位置和环境里的位置不重叠（`env_disjoint`），`fs[0](fs)` 被拒绝；动态派发：对象安全的方法签名和里面的类型无关（`sig_indep`），查得到 impl（`vtable_found`），经过方法表的调用等于直接调用（`dispatch_eq`） |

### 字符串 `Core/Strings/`

| 文件 | 内容 |
|---|---|
| `Slice.lean` | 字符串切片和静态字面量。子切片 `sub` 结果仍在缓冲区里、内容是原切片的 `[a, b)`（`sub_ok`、`sub_content`），按下标读字节不越界（`byte_ok`）；arena 只在后面追加：已有切片仍然有效、内容不变（`grow_valid`、`grow_read`），新缓冲区上有覆盖整块的切片（`fresh_valid`）；静态字面量：分配计数总等于拥有的堆字符串个数（`reach_inv`），析构时计数够减（`drop_exact`），全部析构后为 0（`no_leak`），内容和全部在堆上的表示一样（`observe_step`） |
| `ChunkLines.lean` | 逐块读行：不管输入怎么切成块，逐块得到的行和整个读进来再切的行相同（`stream_eq`）；关键的不变式是留下的不完整部分里没有换行（`carry_noNl`）；反例：每块各自切行时，跨块的行被切成两行 |

### 标准库 `Core/Library/`

| 文件 | 内容 |
|---|---|
| `Math.lean` | `std.math`：`Ord` 的四条定律；I64、Str（按字节字典序）的 `cmp` 满足；`min_of`、`max_of` 只依赖定律；`clamp`、`pow`、`sign` 的规格 |
| `StrVec.lean` | `std.str`、`std.vec`：`starts_with`、`find`（第一次出现 / 确实没有）、`trim`（只去头尾空白）、`join(split(s, sep), sep) == s`、`reverse` |
| `FileIO.lean` | 文件与参数 IO：写后读、写一个路径不影响别的、读不存在的是 `Err`、两次写以后一次为准；`write_atomic` 失败时文件系统不变 |
| `Map.lean` | `std.map`：键严格递增的键值对列表；插入、删除后仍有序（`ins_sorted`、`del_sorted`），插入后查得到（`lookup_ins`），删除后查不到（`lookup_del`），别的键不受影响 |
| `MapSearch.lean` | `std.map` 的二分查找和原来的线性查找结果相同（`bs_eq_lin`），所以 `Map.lean` 的定律对新实现照样成立 |
| `TreeMap.lean` | `std.treemap` 的 AVL 树：旋转、`bal`、去掉最小键、`join` 都不改变中序遍历；查找、插入、删除的中序遍历分别等于 `Map.lean` 的 `lookup`、`ins`、`del`（`lookupT_eq`、`insT_eq`、`delT_eq`） |
| `TreeMapAvl.lean` | AVL 平衡：插入、取出最小键、合并、删除都保持平衡（`insT_bal`、`popT_bal`、`join_bal`、`delT_bal`）；`2 ^ (高度 / 2) ≤ 节点数 + 1`（`height_log`），所以是对数时间 |
| `Utf8.lean` | UTF-8：合法字符编码后 `decode1` 正好解出它（`dec_encode`）；按字符遍历得到原来的字符（`chars_encodeAll`）；不合法的字节解成 U+FFFD（`decode1_valid`）。和 sinterc 的 `sn_utf8_put`、`sn_utf8_get` 逐条对应 |
| `Utf8Check.lean` | `str_from_utf8` 的检查：通过当且仅当字节串是某串合法字符的编码（`valid_sound`、`valid_complete`、`utf8_iff`），通过时按字符遍历再编码回去不变（`chars_of_utf8`） |
| `HeapSort.lean` | 堆排序：和 `std/vec.sn` 的 `sift`、`sort_by` 逐条对应；结果排好序（`heapSort_sorted`），是原来元素的一个排列（`heapSort_swaps`） |
| `HashMap.lean` | 开放寻址的哈希表：查找结果和表的内容一致（`lookup_iff`）；插入保持不变式（`ins_spec`）；删除后移回填保持不变式（`erase_spec`）。紧凑数组那一侧由编译器的 `test/std_hashmap.t` 和 `std.map` 随机对照 |
| `BigInt.lean` | 大整数：各位从低到高、基数 10^9；加、减、乘、比较、除以小数、去掉高位的 0 算出的数都对（`val_addL`、`val_subL`、`val_mulL`、`cmpL_spec`、`val_divS`、`val_trim`）；带符号的一层 `toInt_addZ` 等。和 `std/bigint.sn` 一一对应，I64 的范围由 `test/std_bigint.t` 随机对照 |

`Ownership/Move.lean` 第一次编译时有 4 处 `omega` 失败（`omega` 不认 `abbrev Loc := Nat` 这个别名），改用 `Nat.lt_irrefl` 等引理后全部通过。之后的文件都避免在别名类型上用 `omega`。

## `Ownership/Move.lean` 证明了什么

- `safety`：检查器接受的程序，从空状态执行不会出错，也就是没有释放后使用、没有重复释放、没有通过已移走的变量访问已释放的内存。
- 不变式 `Inv` 的三条：拥有值的变量指向活着的位置；拥有者唯一；指针都指向已分配过的位置。
- 动态语义里 `move` 只拷贝指针、不清空旧变量，和真实机器一样。所以 `safety` 不是因为语义本身太保守才成立，而是检查器确实挡住了危险程序。文件末尾的最后一个例子演示了不经检查直接执行会出错。
- 泄漏在 `Ownership/Drop.lean` 里和作用域结束时的自动释放一起证明。

## 许可证 / License

MIT 或 Apache-2.0，任选其一（[LICENSE-MIT](LICENSE-MIT)、[LICENSE-APACHE](LICENSE-APACHE)）。
除非另有说明，你提交的贡献按同样的双许可发布。

Licensed under either of MIT or Apache-2.0 at your option. Unless you state otherwise, any contribution you
submit is dual licensed in the same way.
