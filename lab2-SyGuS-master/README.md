# 软件分析2024 课程项目2

## 课程项目任务

请实现一个语法制导的程序合成（SyGuS）算法，按照给定的语法和语义规约合成程序。

请编写一个 `run.sh` 脚本作为算法入口，如果通过 `./run.sh three.sl` 命令调用你的算法，其中 three.sl 是按照 [SyGuS-IF](https://sygus-org.github.io/language/) 语法描述的程序规约：

```
(set-logic LIA)

(synth-fun f ((x Int)) Int
    ((Start Int (
                 x
                 3
                 7
                 10
                 (* Start Start)
                 (mod Start Start)))))

(declare-var x Int)

(constraint (= (f x) (f (+ x 10))))
(constraint (= (f 1) 3))
(constraint (= (f 2) 6))
(constraint (= (f 3) 9))
(constraint (= (f 4) 2))
(constraint (= (f 5) 5))
(constraint (= (f 6) 8))
(constraint (= (f 7) 1))
(constraint (= (f 8) 4))
(constraint (= (f 9) 7))
(constraint (= (f 0) 0))

(check-synth)
```

则你需要按照 `synth-fun` 的指令生成符合语法规约的程序 `f`，且这个程序满足所有 `constraint`。将程序输出到 `result.txt`：

```
(define-fun f ((x Int)) Int (mod (* x 3) 10))
```

我们会在公开测试用例和隐藏测试用例上评测你的算法，按解出数量打分。公开测试用例在 `judge/global/tests` 目录，包含以下三个类别：

- basic：共 4 个测试用例，比较简单，全部解出即可获得 60 分
- lia：共 12 个测试用例，所有运算都是线性整数运算（LIA），语义约束是严格的逻辑约束
- bv：共 13 个测试用例，涉及位向量（BV）运算，语义约束是一些输入输出样例，但是有 10% 的约束会在输入给你的程序之前被随机删除掉，因此合成出的程序需要有较好的可泛化性

隐藏测试用例包括 10 个 LIA 测试用例、20 个 BV 测试用例和每个队提交的测试用例。最终测试时可能会对公开测试用例进行等价的小修改来避免打表。

时间限制是每个测试用例 3 分钟，资源限制是 4 核、8GB 内存、512 进程。

与 Lab1 相同，请写一份**不超过两页的报告**，描述算法的主要设计思想和小组内分工。也可以提交一个**测试用例**，用来凸显本组算法的亮点。测试用例只能使用 LIA 逻辑，不能使用公开测试用例未涉及的操作符或 SyGuS-IF 语法特性。

## 提供的内容

**trivial_impl 目录：**是一个用 Python 语言实现的程序合成算法，实现得**非常非常烂**，例如：

- 搜索过程十分低效（进行简单修改即可让它解出 basic 类别的全部测试用例）
- 使用的数据结构十分低效，时间长了还可能超出内存限制（评测机显示 `Killed`）
- 验证反例的过程十分低效，每次都调用 Z3，不会将已有的反例存储下来
- 是单核战士，无法充分利用 CPU 的 4 个核心

你可以在这个程序的基础上进行修改，也可以使用喜欢的编程语言重写。SyGuS 官方 [为 C++ 语言提供了解析输入格式的库](https://github.com/sygus-tools/synthlib2parser)，对于其他语言，你可能需要找一个解析 S-expression 的库。

评测环境安装了 Z3 和主流编程语言的运行环境，包括 Python、PyPy、OpenJDK 和 NodeJS，Python 额外安装了 numba 库。如果你使用 C++ / Rust 等语言，请在本地编译后提交编译产物。

**judge 目录：**是评测机源码，可用于在本地测试自己的作业。运行 `init.sh` 来初始化，把作业放到 `user/submission/submission.zip` 后运行 `run.sh` 来运行评测。评测结果会保存到 `user/submission` 目录。

请注意 `Dockerfile` 里注释掉了安装 PyPy、OpenJDK 和 NodeJS 的步骤，以节省时间和空间，如果需要可以取消注释。实际的评测环境安装了这些软件包。

## 要提交的内容

- **可执行的程序合成工具（打包成 .zip）：**用自己小组的密码登录网站 https://162.105.88.145，点击【提交作业】，并在线评测。提交时只测公开用例（和下发的 judge 目录是一样的），可能会花费最多三个小时，因此建议先在本地调试，不要反复提交。
- **测试用例：**在提交完程序后，点击网站上的【贡献测试用例】，并在线评测。
- **代码和报告：**将代码和报告提交到教学网，标题为 “课程项目二代码-学号1-学号2-学号3”。