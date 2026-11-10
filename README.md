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
| C5 后半：42000 个程序的三方对照 | `Core/C5b.lean`（打印成 Sinter 源码），`Core/C5c.lean`（第三组：整体移动、调用约定、闭包、泛型），`compiler/diff.sh` | 已通过：第三组 19600 个程序在 Lean 里结构化和 CFG 结论相同（都接受 4301）；Lean 接受的 6474 个（2173 + 4301）sinterc 全部接受；sinterc 另外接受 2224 个（自动析构，允许）；sinterc 接受的 8698 个各按 15 组选择运行，泄漏 0 次。闭包按 M21 的模型当作一次调用（只读捕获按 read、被写按 inout） |
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
| M21 闭包 | `Core/M21.lean` | 已通过机器检查：闭包只能当实参传。（一）排他性：捕获当作调用处的额外实参按 M3n 的规则检查；`inner_ok`：被调函数用自己的实参调用闭包或往下传时仍满足同一条规则（`two_levels`：两层）；例子说明 `for_each(v, |x| v.push(x))` 被拒绝。（二）不会悬空：每个帧里的闭包只引用更靠下的帧（`good_reach`）；调用闭包时它的帧还在（`clo_live`）；帧返回后没有引用它的闭包（`pop_clean`）；反例：允许返回闭包时不成立 |
| M22 闭包捕获引用 | `Core/M22.lean` | 已通过机器检查：捕获的区域在提升出的函数里是区域参数，调用时按 M14 实例化；`capture_below`：被捕获的变量在调用者的作用域里，由 M5 的不变式 `Good` 得到它指向的区域还活着；`capture_mono`：按嵌套顺序编号，实例化保持顺序；`capture_safe`：由 M14 的 `entry_safe` 得到执行不出错；反例：已结束的区域不满足 `Below` |
| S4 标准库 `std.map` 的规格 | `Core/S4.lean` | 已通过机器检查：键严格递增的键值对列表；只依赖 `Ord` 的定律，插入、删除后仍有序（`ins_sorted`、`del_sorted`），插入后查得到（`lookup_ins`），删除后查不到（`lookup_del`），别的键不受影响（`lookup_ins_other`、`lookup_del_other`） |
| M23 `match` 的通配分支 `_` | `Core/M23.lean` | 已通过机器检查：覆盖检查 `covers`（`_` 最多一个、在最后、还有没写到的变体；没有 `_` 时写全）通过时，把 `_` 展开成每个变体一个分支（带载荷时先析构载荷）一定成功（`expand_some`、`expand_length`）；展开后每个分支的检查结果就是编译器检查的结果（`wild_arm`、`expand_arm`），所以 M8 的 `safety_and_no_leak` 照样成立（`wild_safe`）。字面量分支只是 if 链，不需要新的推理 |
| S5 `std.map` 的二分查找 | `Core/S5.lean` | 已通过机器检查：键严格递增时，二分查找（`bs`，循环不变式：`lo` 之前都小于 `k`，`hi` 开始都不小于 `k`）和原来的线性查找（`lin`）都满足 `IsLower`（`bs_lower`、`lin_lower`），满足它的下标唯一（`lower_unique`），所以两者结果相同（`bs_eq_lin`），S4 的定律对新实现照样成立 |
| S6 `std.treemap` 的 AVL 树 | `Core/S6.lean` | 已通过机器检查：旋转、`bal`、去掉最小键、`join` 都不改变中序遍历（`toList_bal` 等）；键有序时，查找、插入、删除的中序遍历分别等于 S4 的 `lookup`、`ins`、`del`（`lookupT_eq`、`insT_eq`、`delT_eq`），所以仍有序、查得到刚插入的、查不到刚删除的。平衡（树高是对数）没有证明，只由 C43 的测试检查 |
| S7 UTF-8 | `Core/S7.lean` | 已通过机器检查：合法字符编码后 `decode1` 正好解出它（`dec_encode`）；一串合法字符编码再按字符遍历得到原来的字符（`chars_encodeAll`），`str_push_char` 之后正好多出这个字符（`push_chars`）；解码得到的总是合法字符，不合法的字节解成 U+FFFD（`decode1_valid`）。sinterc 的 `sn_utf8_put`、`sn_utf8_get` 与 `encode`、`decode1` 逐条对应 |
| S8 堆排序 | `Core/S8.lean` | 已通过机器检查：`siftDown`、`heapify`、`extract` 与 `std/vec.sn` 的 `sift`、`sort_by` 逐条对应；结果排好序（`heapSort_sorted`），并且由若干次 `[0, n)` 里的交换得到、是原来元素的一个排列（`heapSort_swaps`）。不变式：下沉时除了当前位置都满足堆性质；取出时前面是堆、后面已排好、前面的都不大于后面的 |
| S9 哈希表 | `Core/S9.lean` | 已通过机器检查：槽位表看成位置到键的函数，不变式是每个键在起始位置之后、中间没有空位、键不重复。查找结果和表的内容一致（`lookup_iff`）；插入保持不变式、别的键位置不变（`ins_spec`）；删除后移回填保持不变式、表里的键恰好少了被删的那个（`erase_spec`，回填过程的不变式 `SInv`：只有当前空位可能挡在后面键的探测路上）。紧凑数组那一侧由 `test/c51.t` 与 `std.map` 的随机对照检查 |
| M24 嵌套模式的展开 | `Core/M24.lean` | 已通过机器检查：值（字面量、变体、二元组）和模式（`_`、变量、字面量、变体、元组）的匹配 `pmatch`。编译器把每个分支展开成一个只读的测试 `test` 和一个拆开取值的 `extract`：`test p v` 为真当且仅当 `pmatch p v` 成功（`test_eq`），成功时 `extract` 取出的绑定就是匹配给出的绑定（`extract_of_pmatch`）；所以按顺序测试、只拆开第一个通过的分支，结果和逐个分支匹配完全一样（`run_correct`）。展开后只用到已有的 `match let`、`==`、`&&` 和移动的 `match`，原有的所有权证明不受影响 |
| M24b 嵌套模式的覆盖检查 | `Core/M24b.lean` | 已通过机器检查：按类型（整数、k 个变体的枚举、二元组）枚举有限个代表值，“写出的字面量各一个、再加一个‘其他’”，深度取模式的最大深度。每个值都被某个代表值概括（`abs_match`、`abs_mem`）：代表值都有分支匹配时，这个类型的每个值都有分支匹配（`exhaustive_sound`）；某个分支对所有代表值都不是第一个匹配的分支时，它对任何值都不是（`useful_complete`），所以报告的“永远匹配不到”是对的 |
| S10 大整数 | `Core/S10.lean` | 已通过机器检查：各位从低到高、基数 10^9。逐位加法（`val_addL`）、带借位的减法（被减数不小于减数时，`val_subL`）、乘一位和从高位开始的乘法（`val_mul1`、`val_mulL`）、从高位往低位的比较（`cmpL_spec`）、除以不超过基数的数（`val_divS`）、去掉高位的 0（`val_trim`）算出的数都对，结果每一位仍小于基数（`digits_*`）。带符号的一层：`toInt (addZ x y) = toInt x + toInt y`，减法、乘法、取负同样（`toInt_subZ`、`toInt_mulZ`、`toInt_negZ`），0 只有一种写法（`norm`）。和 `std/bigint.sn` 一一对应，I64 的范围由 `test/c54.t` 的随机对照检查 |

M1 第一次编译时有 4 处 `omega` 失败（`omega` 不认 `abbrev Loc := Nat` 这个别名），改用 `Nat.lt_irrefl` 等引理后全部通过。后续里程碑避免在别名类型上用 `omega`。

## M1 证明了什么

- `safety`：检查器接受的程序，从空状态执行不会出错，也就是没有释放后使用、没有重复释放、没有通过已移走的变量访问已释放的内存。
- 不变式 `Inv` 的三条：拥有值的变量指向活着的位置；拥有者唯一；指针都指向已分配过的位置。
- 动态语义里 `move` 只拷贝指针、不清空旧变量，和真实机器一样。所以 `safety` 不是因为语义本身太保守才成立，而是检查器确实挡住了危险程序。文件末尾的最后一个例子演示了不经检查直接执行会出错。

## M1 还没覆盖的

- 泄漏：覆盖一个仍然拥有值的变量会泄漏，检查器拒绝这种情况，但还没有证明“程序结束时没有泄漏”。放到 M2，和作用域结束时的自动释放一起证明。
- 控制流、参数约定、投影、区域、`linear`：见报告附录 E 的里程碑表。


## 许可证 / License

MIT 或 Apache-2.0，任选其一（[LICENSE-MIT](LICENSE-MIT)、[LICENSE-APACHE](LICENSE-APACHE)）。
除非另有说明，你提交的贡献按同样的双许可发布。

Licensed under either of MIT or Apache-2.0 at your option. Unless you state otherwise, any contribution you
submit is dual licensed in the same way.
