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
- [ ] CCAnr 原版为结构化问题设计，可能需仿照 swcca 修改以适配 random 问题  


## 详细记录


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