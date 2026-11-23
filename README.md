# chrono-harness-judge-cost

比较变更前后的声明成本。

运行 `./check.sh` 验证独立组件。证明使用 Verus 0.2026.04.24.f8e1704，通过环境变量 `VERUS` 指定可执行文件。

[固定来源](https://github.com/ChronoAIProject/chrono-harness/tree/5f6892dfa2f73675a84e4ebdc3b06eb83b824d6e/crates/judge-cost)

成本判官使用 FILEMAP 已校验的公开输出，并保留输入与所绑定 DELTA 的一致性检查、已退役测试以及有未知成本时的报告行为。运行时在宿主 PATH 中安装本仓 mise 清单固定的 chrono-judge-filemap 与 chrono-judge-registration。判官按已登记的超时、输出上限和环境调用 `impact-summary`。它把同一份封存请求交给 registration 的 `filemap-views`，读取变更前后各节点的声明成本，并将绑定 Git 读取产生的观察记录放入判官响应。

专属测试直接使用本仓的成本报告库。报告按输入中的变更文件路径选择成本条目。默认构建启用 `judge`，由判官入口核对封存请求、完整 DELTA 与 FILEMAP 原始输出，再调用同一套报告计算。`check.sh` 分别构建命令、运行专属测试和 Verus 证明。
