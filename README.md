# improved-CC
improved CC strategy for SAT

## usage
To build the solver, run `build.sh`. It will:
- Create a new `/binary` folder
- Compile the source code to generate the `CCAnr` binary
- Copy the binary into `/binary`

To run the solver:

```bash
./CCAnr instance_file random_seed
```

---



## 实验

### Benchmark 来源与类型

目前从 SAT Competition 网站下载的 random 3-SAT 例子，共 500+ 个，分为三类：

1. 不同 ratio 的 3-SAT  
2. ratio = 4.2 的不同规模例子  
3. ratio = 4.267 的不同规模例子

### 实验设置

1. 
    - 每个 instance 运行 10 次  
    - 每次运行设置 300 秒截断时间   

2. 
    - 每个 instance 运行 1 次  
    - 每次运行设置 3600 秒截断时间 

---
## todo

- [x] 300s 截断时间可能太短，尝试延长至 3600 秒  
- [x] 换用 SATLIB 中的 benchmark，经验上这些更简单  
- [x] CCAnr 原版为结构化问题设计，可能需仿照 swcca 修改以适配 random 问题  
- [x] 详细对照SWCC,SWCCA,查看代码的问题。


## 详细记录

<details>

<summary>4/28</summary>

### 做了啥
1. 修改完了所有的bug,在进行步数统计的实验。
2. 有1000s和5000s两个版本

### 计划
1. 先进行步数上的比较
2. 或许减少更新的频率


</details>

<details>

<summary>4/8</summary>

### 做了啥
1. 详细查阅了一下蔡老师的博士论文以及相关参考论文
2. 按照博士论文描述的，实现了专注于random例子的SWCC和SWCCA算法

### 计划
1. 仔细检查我写的代码是否与论文一致
2. 多加一点统计信息，看看时间花在哪里
3. 与SWCC,SWCCA对照，查看问题




</details>

<details>

<summary>3/28</summary>


### 实验效果

试了todo的前两项，效果不明显，准备详细检查一下代码先



</details>



<details>

<summary>3/27</summary>


### 实验效果

目前效果一般，原始版本和修改版本表现都不理想。

### 后续可能的改进方向

- 300s 截断时间可能太短，尝试延长至 1800 或 3600 秒  
- 换用 SATLIB 中的 benchmark，经验上这些更简单  
- CCAnr 原版为结构化问题设计，可能需仿照 swcca 修改以适配 random 问题  

---

**TLDR**：准备按上述猜想继续修改实验策略。

</details>