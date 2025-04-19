/************************************=== CCAnr ===***************************************
 ** CCAnr is a local search solver for the Boolean Satisfiability (SAT) problem,
 ** which is especially designed for non-random instances.
 ** CCAnr is designed and implemented by Shaowei Cai (email: shaoweicai.cs@gmail.com),
 *****************************************************************************************/

/*****************************=== Develpment history ===*************************************
** 2011.5
** SWCC (Smoothed Weighting and Configuration Checking) by Shaowei Cai
** New Idea: Configuration Checking (CC)
** A variable is configuration changed, if since its last flip, at least one of its
** neighboring var has been flipped.
** In the greedy mode, Swcc picks the best Configuration Changed Decreasing  var to flip.
** In the random mode, it updates weights, and flips the oldest var in a random unsat clause.

** 2011.9
** SWCCA (Smoothed Weighting and Configuration Checking with Aspiration) by Shaowei Cai
** New Idea: CC with Aspiration (CCA)
** Modification: in greedy mode, it first prefers to flip the best CCD var. If there is
** no CCD variable, then flip the best significant decreasing var, i.e., with a great
** positive score (in Swcca, bigger than averaged clause weight), if there exsit such vars.

** 2013.4
** CCAnr (CCA for non-random SAT)
** Modifications: Generalize the smoothig fomula as w(ci)=w(ci)*p+ave_w*q; pick the greediest
** variable in the diversification mode.
************************************************************************************************/

#ifndef _CCA_H_
#define _CCA_H_

#include "basis.h"
#include "pair_key.h"

// -----------------------------------------------------------------------new
#include <iostream>
#include <cstdint>
#include <unordered_map>
#include <map>
#include <deque>
#include <vector>
#include <utility>
#include <unordered_set>
#include <set>
using PairKey = uint64_t;

// 用vector来管理，代码更简洁易懂
#define stack_push(item, stack) stack[stack##_fill_pointer++] = item
#define stack_pop(stack) stack[--stack##_fill_pointer]

using namespace std;
// 全局数组，用于存储非关键子句的属性
extern int Q_C[MAX_CLAUSES];				 // 0或1, 表示该子句是否包含u-q-flippable对
extern int R_C[MAX_CLAUSES];				 // 0或1, 表示该子句是否包含reversible对
extern int S_C[MAX_CLAUSES];				 // 整数分数, 记录当前最高score
extern int T_C[MAX_CLAUSES];				 // 时间戳, 表示上次更新该子句的step
extern std::pair<int, int> P_C[MAX_CLAUSES]; // 记录当前子句所选最佳变量对

int computePairScore(int xi, int xj);

// LN 用来保存所有非关键且 N(C)==1 的子句编号
// LN[i] 存储所有满足条件的子句编号，其中 i 为变量编号（1 <= i <= num_vars）
// std::vector<vector<int>> LN;
std::vector<std::unordered_set<int>> LN;
extern std::set<int> noncritical_clauses;
// 定义自定义哈希函数，用于 std::pair<int,int>
struct pair_hash
{
	size_t operator()(const pair<int, int> &p) const
	{
		// 使用两个整数的哈希值组合
		size_t h1 = hash<int>()(p.first);
		size_t h2 = hash<int>()(p.second);
		return h1 ^ (h2 << 1);
	}
};

/* ------------------------------------------------------------------ */
/* 替换原来的 std::map<pair<int,int>,int> 容器                       */
/* ------------------------------------------------------------------ */
std::unordered_map<PairKey, int> LCQ; // qualified‑pair  → score
std::unordered_map<PairKey, int> LCR; // reversible‑pair → score

unordered_map<int, std::deque<int>> LNQ; // 记录 Q(C)=1 的子句，按score分组
unordered_map<int, std::deque<int>> LNR;

// criticalVars 为全局变量，存储所有 critical 变量的编号
extern std::vector<int> criticalVars;

bool U_array[MAX_VARS];
std::unordered_set<int> LU;

// 全局定义两个集合，类型使用 std::set 保证唯一性和有序性
extern std::set<std::pair<int, int>> qualified_pairs_in_critical;
std::set<std::pair<int, int>> valuable_pairs_for_critical;

struct Last2Flip
{
	int a = -1, b = -2;

	inline void push(int x)
	{
		b = a;
		a = x;
	}

	inline bool same() const
	{
		return a == b;
	}
};
std::vector<Last2Flip> var_change;

// 需要每次遍历flipvar及其邻居和二次邻居的var_change，用于判断受到影响的是否为unqualified_pairs
// 定义全局变量 neighbor_pairs 和 unqualified_pairs
// 定义存储所有相邻变量对的集合（每个对保证 (v, u) 中 v < u）
// set<pair<int, int>> neighbor_pairs;
set<pair<int, int>> unqualified_pairs;
// // 定义存储 critical pairs 的集合（即重复出现的对）
// set<pair <int, int>> critical_pairs;
// // 定义存储 noncritical pairs 的集合（即重复出现的对）
// map<pair <int, int>, int> noncritical_pairs;

void removeClauseFromLNQ(int c, int oldScore)
{
	// 在 LNQ 中查找 oldScore
	auto it = LNQ.find(oldScore);
	if (it == LNQ.end())
	{
		// 说明 LNQ 中没有分数=oldScore 的条目，无需删除
		return;
	}

	// 取到存放旧分数=oldScore 的子句队列
	std::deque<int> &dq = it->second;

	// 在 dq 里找到子句 c 并删除
	// 注意迭代器安全：一旦 erase 会使该迭代器失效，所以要先 break 再退出循环
	for (auto dit = dq.begin(); dit != dq.end(); ++dit)
	{
		if (*dit == c)
		{
			dq.erase(dit);
			break;
		}
	}

	// 如果 dq 变空了，说明没有子句在 oldScore 这个桶中
	if (dq.empty())
	{
		LNQ.erase(it);
	}
}

void removeClauseFromLNR(int c, int oldScore)
{
	// 在 LNQ 中查找 oldScore
	auto it = LNR.find(oldScore);
	if (it == LNR.end())
	{
		// 说明 LNQ 中没有分数=oldScore 的条目，无需删除
		return;
	}

	// 取到存放旧分数=oldScore 的子句队列
	std::deque<int> &dq = it->second;

	// 在 dq 里找到子句 c 并删除
	// 注意迭代器安全：一旦 erase 会使该迭代器失效，所以要先 break 再退出循环
	for (auto dit = dq.begin(); dit != dq.end(); ++dit)
	{
		if (*dit == c)
		{
			dq.erase(dit);
			break;
		}
	}

	// 如果 dq 变空了，说明没有子句在 oldScore 这个桶中
	if (dq.empty())
	{
		LNR.erase(it);
	}
}

// 将子句标记为不满足，并更新相关变量
inline void unsat(int clause)								 // 这里clause应该表示子句在整个公式F中的下标（从0开始）
{															 // unsat_stack_fill_pointer指当前新入stack的元素下标，也表示当前stack元素数量
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer; // 记录子句在不满足栈中的位置
	stack_push(clause, unsat_stack);						 // 入栈

	// update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	// p是一个lit结构体向量，每个lit包含 子句下标（0开始） 变量下标（1开始） 从句真值
	// clause_lit[i][j]表示第i个子句的第j个lit，
	// 这里p初始化指向为clause_lit的第clause个子句的第一个lit的指针，子句包含了很多lit结构体
	// v表示p所指向的lit结构体的变量数这一成员，子句末尾变量一般用0作为标记
	for (lit *p = clause_lit[clause]; (v = p->var_num) != 0; p++)
	{
		unsat_app_count[v]++;		 // 增加变量（下标为v）在不满足子句中的出现次数
		if (unsat_app_count[v] == 1) // 首次出现，则压入不满足变量栈，并记录位置
		{
			index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
			stack_push(v, unsatvar_stack); // 将变量压入不满足变量栈
		}
	}
}

// 将子句标记为满足，并更新相关变量
inline void sat(int clause)
{
	int index, last_unsat_clause;

	// since the clause is satisfied, its position can be reused to store the last_unsat_clause
	// 交换函数输入clause和unsat_stack最后一个子句位置，并将clause出栈
	last_unsat_clause = stack_pop(unsat_stack);		 // 从不满足栈中移除最新一条不满足的子句
	index = index_in_unsat_stack[clause];			 // 获得clause在不满足栈中的index
	unsat_stack[index] = last_unsat_clause;			 // 将last_unsat_clause插入到该index中
	index_in_unsat_stack[last_unsat_clause] = index; // 更新last_unsat_clause的index

	// update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v, last_unsat_var;
	for (lit *p = clause_lit[clause]; (v = p->var_num) != 0; p++)
	{
		unsat_app_count[v]--;		 // 减少变量（下标为v）在不满足子句中的出现次数
		if (unsat_app_count[v] == 0) // 如果次数减少为0，则将其出栈，同样是交换v和unsat_stack最后一个变量位置，并将v出栈
		{
			last_unsat_var = stack_pop(unsatvar_stack);
			index = index_in_unsatvar_stack[v];
			unsatvar_stack[index] = last_unsat_var;
			index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

void initializePairStructures(const std::set<std::pair<int, int>> &criticalPairs);
void updatePairStructures(int xi, int xj);

void init()
{
	int v, c;
	int i, j;
	int clause;
	LN.resize(num_vars + 1); // 给 LN 分配 num_vars+1 个 unordered_set

	// 初始化var_change，长度为 count，每个队列为空
	var_change = std::vector<Last2Flip>(num_vars + 1);

	// 初始化qualified_pair

	// Initialize edge weights 初始化子句权重为1
	for (c = 0; c < num_clauses; c++)
		clause_weight[c] = 1;

	// init unsat_stack
	//  初始化不满足子句栈和不满足变量栈
	unsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;

	// init solution
	for (v = 1; v <= num_vars; v++)
	{

		if (fix[v] == 0)
		{
			if (rand() % 2 == 1)
				cur_soln[v] = 1;
			else
				cur_soln[v] = 0;

			time_stamp[v] = 0;
			conf_change[v] = 1;
			unsat_app_count[v] = 0;

			// pscore[v] = 0;
		}
		// cout << "v " << v << ": " << cur_soln[v] << endl;
	}

	/* figure out sat_count, and init unsat_stack */
	for (c = 0; c < num_clauses; ++c)
	{
		if (clause_delete[c] == 1)
			continue;

		sat_count[c] = 0;

		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				sat_count[c]++;
				sat_var[c] = clause_lit[c][j].var_num;
			}
		}

		if (sat_count[c] == 0)
			unsat(c);
	}

	// figure out var score 可以作为一个函数
	int lit_count;
	for (v = 1; v <= num_vars; v++)
	{

		U_array[v] = false; // 初始化bool_U_array
		// 如果变量被固定，则将其得分设置为一个极小值
		if (fix[v] == 1)
		{
			score[v] = -100000;
			continue;
		}

		score[v] = 0;
		score[v] = 0;
		// 获取变量所在的所有文字数量
		lit_count = var_lit_count[v];
		// 遍历变量的所有文字，计算得分
		for (i = 0; i < lit_count; ++i)
		{ // 获取该文字所在子句的编号
			c = var_lit[v][i].clause_num;
			if (sat_count[c] == 1)
			{
				if (var_lit[v][i].sense == cur_soln[v])
				{
					score[v]--; // 子句仅由当前变量满足，则得分减1
					score[v]--; // 子句仅由当前变量满足，则得分减1
				}
				if (noncritical_clauses.find(c) != noncritical_clauses.end() && find(LN[v].begin(), LN[v].end(), c) == LN[v].end())
					LN[v].insert(c);
			}
			else if (sat_count[c] == 0)
			{
				score[v]++; // 子句不满足，则翻转该变量后子句满足，得分+1
				score[v]++; // 子句不满足，则翻转该变量后子句满足，得分+1
			}
		}
	}
	/*
	int flag;
	//compute pscore and record sat_var and sat_var2 for 2sat clauses
	for (c=0; c<num_clauses; ++c)
	{
		if(clause_delete[c]==1) continue;

		if (sat_count[c]==1)
		{
			for(j=0;j<clause_lit_count[c];++j)
			{
				v=clause_lit[c][j].var_num;
				if(v!=sat_var[c])pscore[v]++;
			}
		}
		else if(sat_count[c]==2)
		{
			flag=0;
			for(j=0;j<clause_lit_count[c];++j)
			{
				v=clause_lit[c][j].var_num;
				if(clause_lit[c][j].sense == cur_soln[v])
				{
					pscore[v]--;
					if(flag==0){sat_var[c] = v; flag=1;}
					else	{sat_var2[c] = v; break;}
				}
			}

		}
	}
	*/

	// init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++)
	{
		if (fix[v] == 1)
			continue;
		// 如果变量得分大于 0，则将其加入 goodvar_stack
		if (score[v] > 0) // && conf_change[v]==1)
		{
			already_in_goodvar_stack[v] = 1;
			stack_push(v, goodvar_stack);

		} // 否则标记为未在 goodvar_stack 中
		else
			already_in_goodvar_stack[v] = 0;
	}

	// setting for the virtual var 0 时戳初始化为0
	time_stamp[0] = 0;
	// pscore[0]=0;
	//  解、子句状态、得分初始化完毕后，初始化 LCQ,LCR
	initializePairStructures(criticalpairs);
}

void flip(int flipvar)
{
	// if (key_flip == 1)
	LU.insert(flipvar); // 记录翻转变量

	cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转 flipvar 的值
	// 选择翻转变量后应该更新flipvar及其邻居的var_change
	// var_change用于判断其和邻居是否为qualifie pair
	// below
	// 更新flipvar自己的var_change
	int i, j;
	// 如果历史记录已经有两事件，则移除最早的一个
	var_change[flipvar].push(flipvar);

	for (i = 0; var_neighbor[flipvar][i] != 0; i++)
	{
		j = var_neighbor[flipvar][i];
		var_change[j].push(flipvar);
	}

	int v, c;

	lit *clause_c;
	// 在分数没更新时，保存flipvar的原始得分
	int org_flipvar_score = score[flipvar];
	int orig_flipvar_score = score[flipvar];

	// update related clauses and neighbor vars 遍历flipvar所在的子句，q是flipvar的所有文字，c是文字对应的子句编号
	for (lit *q = var_lit[flipvar]; (c = q->clause_num) >= 0; q++)
	{
		clause_c = clause_lit[c]; // 获取当前子句的文字列表
		// 如果翻转后 flipvar 的当前值==子句中的文字真值
		// 如，q->sense=0时，变量1->0，则文字假变真；q->sense=1时，变量0->1，则文字假变真。else则子句满足数-1
		if (cur_soln[flipvar] == q->sense)
		{
			++sat_count[c];

			if (sat_count[c] == 2)
			{ // sat_count from 1 to 2
				// 增加满足子句的另一个变量的得分
				// ∵之前翻转另一变量,子句从满足变成不满足,因此子句对另一变量的分数贡献为-clause_weight[c]
				// 这儿要修改成不加权和加权的两种
				bool oldQ = (Q_C[c] == 1);
				bool oldR = (R_C[c] == 1);
				int oldScore = S_C[c];
				if (oldQ)
				{
					// c 在 LNQ[oldScore]
					removeClauseFromLNQ(c, oldScore);
				}
				if (oldR)
				{
					// c 在 LNR[oldScore]
					removeClauseFromLNR(c, oldScore);
				}
				score[sat_var[c]] += clause_weight[c];
				score[sat_var[c]] += 1; // 使用固定权重1
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					if (LN[v].find(c) != LN[v].end())
					{
						LN[v].erase(c);
						// cout << "erase c because sat_cout=2, variable and clause :(" << v << ", " << c << "): " << endl;
					}
				}
			}
			else if (sat_count[c] == 1) // sat_count from 0 to 1
			{
				sat_var[c] = flipvar; // record the only true lit's var
				// flipvar翻转后子句才满足
				// ∵子句其他变量翻转后sat_count由增加变不增加，∴得分减少
				// ∵flipvar再翻转后sat_count-1，，∴得分也减少
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					score[v] -= clause_weight[c];
					score[v] -= 1;	 // 固定权重1
					LN[v].insert(c); // 将子句编号加入到变量的 LN 中
				}
				// 将子句标记为满足，并更新相关变量
				sat(c);
			}
		}
		// 如果翻转后 flipvar 的当前值！=子句中的文字真值
		// 如，q->sense=0时，变量0->1，则文字真变假；q->sense=1时，变量1->0，则文字真变假。else则子句满足数-1
		else // cur_soln[flipvar] != cur_lit.sense
		{
			--sat_count[c];
			if (sat_count[c] == 1) // sat_count from 2 to 1
			{
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					// q->sense=0时,cur_soln[v]=0,则当前文字为真，翻转v，sat-1；
					// q->sense=1时,cur_soln[v]=1,则当前文字为真，翻转v，sat-1；
					if (p->sense == cur_soln[v])
					{

						score[v] -= clause_weight[c];
						score[v] -= 1;	// 固定权重1
						sat_var[c] = v; // 目前唯一满足子句c的变量是v
						break;
					}
					LN[v].insert(c); // 将子句编号加入到变量的 LN 中
				}
			}
			else if (sat_count[c] == 0) // sat_count from 1 to 0
			{
				// 此时子句c不满足，任意翻转c包含的变量均可使其满足，得分+
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					score[v] += clause_weight[c];
					score[v] += 1; // 固定权重1
					bool oldQ = (Q_C[c] == 1);
					bool oldR = (R_C[c] == 1);
					int oldScore = S_C[c];
					if (oldQ)
					{
						// c 在 LNQ[oldScore]
						removeClauseFromLNQ(c, oldScore);
					}
					if (oldR)
					{
						// c 在 LNR[oldScore]
						removeClauseFromLNR(c, oldScore);
					}
					if (LN[v].find(c) != LN[v].end())
					{
						LN[v].erase(c);
						// cout << "erase c because satcout==0 variable and clause :(" << v << ", " << c << "): " << endl;
					}
				}
				// 将子句标记为不满足，并更新相关变量
				unsat(c);
			} // end else if

		} // end else
	}
	// flipvar翻转后，分数为翻转前的相反数，邻居分数已经在上面更新过了
	score[flipvar] = -org_flipvar_score;
	score[flipvar] = -orig_flipvar_score;
	/*update CCD */
	int index;
	// 因为flipvar刚翻转过，conf_change设置为unflippable
	conf_change[flipvar] = 0;
	// flipvar翻转后，更新goodvar_stack中元素，选择1-step q-flippable变量
	// 条件1：score>0；条件2：conf_change=1
	// remove the vars no longer goodvar in goodvar stack
	for (index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	{
		v = goodvar_stack[index];
		// 分数不满足移除，这里会把 flipvar 移除，因为其分数已被更新为负
		if (score[v] <= 0)
		{
			goodvar_stack[index] = stack_pop(goodvar_stack);
			already_in_goodvar_stack[v] = 0;
		}
	}

	// update all flipvar's neighbor's conf_change to be 1, add goodvar
	//  唯一使用了邻居关系的地方
	int *p;
	for (p = var_neighbor[flipvar]; (v = *p) != 0; p++)
	{
		conf_change[v] = 1;
		// 分数大于0，且还未在goodvar_stack，则入栈
		if (score[v] > 0 && already_in_goodvar_stack[v] == 0)
		{
			stack_push(v, goodvar_stack);
			already_in_goodvar_stack[v] = 1;
		}
	}

	// 更新LCQ,LCR

	for (p = var_neighbor[flipvar]; (v = *p) != 0; p++)
	{
		// 如果变量 xi 在 LCP 中有记录v
		if (LCP.find(v) != LCP.end())
		{
			// 遍历 LCP[xi] 中的每个 pair
			const vector<pair<int, int>> &pairList = LCP[v];
			for (const auto &p : pairList)
			{
				// 这里的 p.first 和 p.second 是 pair 的两个元素
				// 更新该 pair 是否属于 LCQ 或 LCR
				// 这里直接调用 updatePairStructures
				// cout << "Updating pair structures for (" << p.first << ", " << p.second << ")" << endl;
				updatePairStructures(p.first, p.second);
				updatePairStructures(p.second, p.first);
			}
		}
	}
	// cout << LCP.size() << endl;
}

// ------------------------------------------------------------------------new
bool is_qualified_pairs(const std::pair<int, int> &pairs)
{
	const auto &xi = var_change[pairs.first];
	const auto &xj = var_change[pairs.second];
	if (xi.a < 0 || xi.b < 0 || xj.a < 0 || xj.b < 0)
		return true;

	return !(xi.a == xj.a && xi.b == xj.b);
}

struct Result
{
	int value; // 关联的整数值
	bool re;   // 操作是否成功
};
Result is_valuable_for_critical(int xi, int xj)
{
	// 根据你的说明：
	// score(F, X_j, s_i_t) = computePairScore(xi, xj) - score[xi]
	// score(F, X_i, s_i,j_t) = computePairScore(xi, xj) - score[xj]
	//
	// 条件要求：
	// 1. score[xi] + (computePairScore(xi, xj) - score[xi]) > 0   => computePairScore(xi, xj) > 0
	// 2. (computePairScore(xi, xj) - score[xi]) > 0
	// 3. (computePairScore(xi, xj) - score[xi]) > score[xj]
	// 4. (computePairScore(xi, xj) - score[xj]) <= 0
	//
	// 下面将 computePairScore(xi, xj) 用 n_i_j 表示：
	int n_i_j = computePairScore(xi, xj);
	// 条件2
	bool cond2 = (n_i_j - score[xi] > 0);
	// 条件1: 其实就是 n_i_j > 0
	bool cond1 = (n_i_j > 0);
	// 条件3: (n_i_j - score[xi]) > score[xj]
	bool cond3 = ((n_i_j - score[xi]) > score[xj]);
	// 条件4: (n_i_j - score[xj]) <= 0
	bool cond4 = ((score[xj] - n_i_j) <= 0);
	// std::cout << "Checking valuable for critical for pair (" << xi << ", " << xj << "):\n"
	// 		  << "    computePairScore = " << n_i_j << "\n"
	// 		  << "    cond1 (score>0): " << cond1 << "\n"
	// 		  << "    cond2 (n_i_j - score[" << xi << "] > 0): " << cond2 << "\n"
	// 		  << "    cond3 (n_i_j - score[" << xi << "] > score[" << xj << "]): " << cond3 << "\n"
	// 		  << "    cond4 (n_i_j - score[" << xj << "] <= 0): " << cond4 << std::endl;

	if (cond1 && cond2 && cond3 && cond4)
		return {n_i_j, true};
	else
		return {n_i_j, false};
}

Result is_valuable_for_noncritical(int xi, int xj)
{
	// 确保键是 canonical 格式
	int n_i_j = score[xj] + score[xi];
	// 条件3：得分条件，根据论文描述，可以判断 (score(xj) >= 0 && score(xi) >= 0) 或 (score(xj) >= 1 && score(xi) == -1)
	if ((score[xj] >= 0 && score[xi] >= 0) || (score[xj] >= 1 && score[xi] == -1))
		return {n_i_j, true};
	return {n_i_j, false};
}

// bool is_valuable_for_noncritical(int xi, int xj)

// 占位函数：计算变量对 (xi, xj) 的分数 N(F, xi, xj, s)
// 此处假设 N_score[v] 已经记录了单个变量 v 的得分
// 并且使用前面实现的 computePairDeltaOverlap(xi, xj) 计算 Delta_overlap

bool clauseSatisfiedWithFlips(int c, int flipXi, int flipXj)
{
	// 遍历子句 c 中的每个文字
	for (int j = 0; j < clause_lit_count[c]; j++)
	{
		int var = clause_lit[c][j].var_num;
		if (var == 0)
			break;
		int sense = clause_lit[c][j].sense;
		// 取当前变量的值
		int val = cur_soln[var];
		// 如果 var 等于 flipXi，则模拟翻转该变量
		if (var == flipXi)
			val = 1 - val;
		// 如果 var 等于 flipXj，则模拟翻转该变量
		if (var == flipXj)
			val = 1 - val;
		// 对于文字：若 sense==1，则文字为真要求变量值==1；若 sense==0，则要求变量值==0
		bool literalTrue = (sense == 1 ? (val == 1) : (val == 0));
		if (literalTrue)
			return true; // 子句中只要有一个文字为真，则子句满足
	}
	return false;
}

// 下面函数实现伪代码计算 Delta_overlap
// 计算变量对 (xi, xj) 对应的 Delta_overlap，依赖于 LCC(xi,xj)
int computePairDeltaOverlap(int xi, int xj)
{
	int Delta_overlap = 0;
	// 确保 xi < xj
	int a = min(xi, xj), b = max(xi, xj);
	PairKey key = pair_key_directed(xi, xj);
	// 如果 LCC 中没有该对，则返回 0
	if (LCC.find(key) == LCC.end())
	{
		return 0;
	}

	vector<int> &clauseList = LCC[key];
	// 遍历 LCC(xi, xj) 中所有子句 C_t
	for (int c : clauseList)
	{
		// old_satisfied：在当前赋值 s 下，子句 c 是否满足（1或0）
		int old_satisfied = clauseSatisfiedWithFlips(c, -1, -1) ? clause_weight[c] : 0;
		// new_satisfied_ij：在同时翻转 xi 和 xj 后，子句 c 是否满足
		int new_satisfied_ij = clauseSatisfiedWithFlips(c, xi, xj) ? clause_weight[c] : 0;
		int change_for_ij = new_satisfied_ij - old_satisfied;
		// onlyXi_satisfied：只翻转 xi 后子句 c 是否满足
		int onlyXi_satisfied = clauseSatisfiedWithFlips(c, xi, -1) ? clause_weight[c] : 0;
		int change_for_i = onlyXi_satisfied - old_satisfied;
		// onlyXj_satisfied：只翻转 xj 后子句 c 是否满足
		int onlyXj_satisfied = clauseSatisfiedWithFlips(c, -1, xj) ? clause_weight[c] : 0;
		int change_for_j = onlyXj_satisfied - old_satisfied;
		int overlap_change_for_C = change_for_ij - change_for_i - change_for_j;
		Delta_overlap += overlap_change_for_C;
	}
	// cout << "Delta_overlap for pair (" << xi << ", " << xj << ") = " << Delta_overlap << endl;
	return Delta_overlap;
}

int computePairScore(int xi, int xj)
{
	// 假设 N_score 是一个全局数组，其中 N_score[v] 表示 N(F, v, s)

	int delta_overlap = computePairDeltaOverlap(xi, xj);
	// cout << "Delta_overlap for pair (" << xi << ", " << xj << ") = " << delta_overlap << endl;
	return score[xi] + score[xj] + delta_overlap;
}

// 更新函数：直接使用传入的对 (xi,xj) 的顺序，不转换
void updatePairStructures(int xi, int xj)
{
	PairKey key = pair_key_directed(xi, xj);

	bool valuable = is_valuable_for_critical(xi, xj).re;
	bool qualified = is_qualified_pairs({xi, xj});

	bool inLCQ = LCQ.find(key) != LCQ.end();
	bool inLCR = LCR.find(key) != LCR.end();

	/* ---------- ❶  如果不再 valuable : 直接删除 ---------- */
	if (!valuable)
	{
		if (inLCQ)
			LCQ.erase(key);
		if (inLCR)
			LCR.erase(key);
		return; // 结束，没算 score
	}

	/* ---------- ❷  already in right bucket? ---------- */
	if (qualified && inLCQ)
		return; // 好的 pair 已在 LCQ ✔
	if (!qualified && inLCR)
		return; // 不 qualified 已在 LCR ✔

	/* ---------- ❸  其余情况才需要计算分数 ---------- */
	int scoreVal = computePairScore(xi, xj);

	if (qualified)
	{
		LCQ[key] = scoreVal; // 插或覆盖
		if (inLCR)
			LCR.erase(key); // 从另一桶移除
	}
	else
	{
		LCR[key] = scoreVal;
		if (inLCQ)
			LCQ.erase(key);
	}
}

void initializePairStructures(const std::set<std::pair<int, int>> &criticalPairs)
{
	LCQ.clear();
	LCR.clear();
	LCQ.reserve(criticalPairs.size() * 2); // 预留哈希桶
	LCR.reserve(criticalPairs.size() * 2);

	std::cout << "Initializing Pair Structures\n";

	for (const auto &p : criticalPairs)
	{
		int xi = p.first, xj = p.second;

		Result res_xy = is_valuable_for_critical(xi, xj);
		Result res_yx = is_valuable_for_critical(xj, xi);
		if (!res_xy.re && !res_yx.re)
			continue; // 两向都不 valuable

		/* 选方向：若两向都可，则把 time_stamp 小的做第一 */
		int a = xi, b = xj;
		if (res_xy.re && res_yx.re && time_stamp[xi] > time_stamp[xj])
			std::swap(a, b);
		else if (!res_xy.re) // 只有 y→x valuable
			std::swap(a, b); // 方向取 (xj,xi)

		PairKey key = pair_key_directed(a, b);
		int s = computePairScore(a, b);

		LCQ[key] = s;
	}

	std::cout << "Initialization complete. LCQ size = "
			  << LCQ.size() << ", LCR size = "
			  << LCR.size() << "\n";
}

/*******************************************************
 * updateNonCriticalClausesInLN
 * 需求：
 *   - 遍历 LU 中所有变量 x
 *   - 对 LN[x] 中所有子句 c，若 T_C[c] != currentStep，则进行更新
 *     (即根据论文 4.3.3 中描述的逻辑，更新 Q(C), R(C), S(C), P(C), T(C))
 *******************************************************/

// 示例：
// - LN[x] 记录 x 参与的、满足 N(C)=1 的所有非关键子句编号
// - T_C[c] 上次更新的步骤，如果 == currentStep 表示已更新过
// - Q_C[c], R_C[c], S_C[c] 为全局数组，存储 Q(C), R(C), S(C)
// - P_C[c] 建议使用全局 array / map 存储 pair<int,int>，也可以内置在 NonCriticalClause 中
// - getSingleSatisfiedVar(c) / checkAndUpdateClause(c) 等函数需要你自行实现
// void removeOldRecordInLNQorLNR(int c, bool oldQ, bool oldR, int oldScore)
// {
// 	// 若旧状态 Q=1 => c 在 LNQ[oldScore] 里
// 	if (oldQ)
// 	{
// 		auto it = LNQ.find(oldScore);
// 		if (it != LNQ.end())
// 		{
// 			auto &dq = it->second;
// 			// O(n) 在 dq 中找 c 并删除
// 			for (auto dit = dq.begin(); dit != dq.end(); ++dit)
// 			{
// 				if (*dit == c)
// 				{
// 					dq.erase(dit);
// 					break;
// 				}
// 			}
// 			if (dq.empty())
// 			{
// 				LNQ.erase(it);
// 			}
// 		}
// 	}
// 	// 若旧状态 R=1 => c 在 LNR[oldScore] 里
// 	if (oldR)
// 	{
// 		auto it = LNR.find(oldScore);
// 		if (it != LNR.end())
// 		{
// 			auto &dq = it->second;
// 			// 同理在 dq 中找 c
// 			for (auto dit = dq.begin(); dit != dq.end(); ++dit)
// 			{
// 				if (*dit == c)
// 				{
// 					dq.erase(dit);
// 					break;
// 				}
// 			}
// 			if (dq.empty())
// 			{
// 				LNR.erase(it);
// 			}
// 		}
// 	}
// }
void pickOthers(int c, int xj, int &xk, int &xl);
void checkQFlipOrRev(int c, int a, int b, bool &foundUQ, bool &foundR,
					 int &bestScore, std::pair<int, int> &bestPair);

void updateNonCriticalClausesInLN(int currentStep)
{
	// 遍历 LU 中每个变量 x
	for (auto x : LU)
	{
		// 遍历 LN[x] 中所有子句 c
		for (int c : LN[x])
		{

			// // 若子句 c 在本 step 已更新过，跳过
			if (T_C[c] == currentStep)
				continue;

			// 否则设置 T_C[c] = currentStep，表示本 step 已更新
			T_C[c] = currentStep;

			// 在这里执行论文 4.3.3 中描述的逻辑：
			// 1) 找到该子句的唯一满足变量 Xj
			// 2) 找到另两个变量 Xk, Xl
			// 3) 尝试判断 (Xj, Xk) / (Xk, Xj) 是否 u-q-flippable
			//    否则判断 (Xj, Xl) / (Xl, Xj)
			// 4) 若都不 q-flippable，再看是否 reversible
			// 5) 最终根据是否找到 u-q-flippable / reversible 来设置 Q_C[c], R_C[c], S_C[c], P_C[c]

			// 例：先找到唯一满足变量 xj
			int xj = sat_var[c];
			// 再找另外两个
			int xk = -1, xl = -1;
			pickOthers(c, xj, xk, xl); // 你需要实现 pickOthers 函数

			// 优先判断 (xj, xk)/(xk, xj) 是否 u-q-flippable
			//     如果是，Q_C[c]=1, R_C[c]=0, S_C[c]=..., P_C[c]=(xj,xk) or (xk,xj)
			// 否则再判断 (xj, xl)/(xl, xj)
			// 如果都不 u-q-flippable, 看是否 reversible ...
			// 以下仅给出示例调用，具体需要你自行完成

			bool foundUQ = false;
			bool foundR = false;
			int bestScore = 0;
			pair<int, int> bestPair = {0, 0};

			checkQFlipOrRev(c, xj, xk, foundUQ, foundR, bestScore, bestPair);
			checkQFlipOrRev(c, xk, xj, foundUQ, foundR, bestScore, bestPair);
			checkQFlipOrRev(c, xl, xj, foundUQ, foundR, bestScore, bestPair);
			checkQFlipOrRev(c, xj, xl, foundUQ, foundR, bestScore, bestPair);

			if (foundUQ)
			{
				Q_C[c] = 1;
				R_C[c] = 0;
				S_C[c] = bestScore;
				// P_C[] 你可用全局 array 或 map
				P_C[c] = bestPair;
				LNQ[bestScore].push_back(c);
			}
			else if (foundR)
			{
				Q_C[c] = 0;
				R_C[c] = 1;
				S_C[c] = bestScore;
				P_C[c] = bestPair;
				LNR[bestScore].push_back(c);
			}
			else
			{
				Q_C[c] = 0;
				R_C[c] = 0;
				S_C[c] = 0;
				P_C[c] = {0, 0};
			}
		}
	}
	LU.clear();
}

void pickOthers(int c, int xj, int &xk, int &xl)
{
	// 根据 clause_lit[c] 遍历子句中的变量
	// 假设子句长度 <= 3
	// 这里演示直接找
	xk = -1;
	xl = -1;
	int foundCount = 0;

	for (int i = 0; i < clause_lit_count[c]; i++)
	{
		int var = clause_lit[c][i].var_num;
		if (var == 0)
			break; // end
		if (var == xj)
			continue; // 跳过 Xj
		if (foundCount == 0)
		{
			xk = var;
			foundCount++;
		}
		else if (foundCount == 1)
		{
			xl = var;
			foundCount++;
		}
		else
			break; // 对于 3-SAT，只取3个变量
	}
}

/*******************************************************
 * checkQFlipOrRev
 * 传入 (a,b)，先尝试u-q-flippable，如果找到则更新 foundUQ，
 * 否则再看是否reversible。如果 foundUQ=true，不再看 foundR
 *******************************************************/
void checkQFlipOrRev(int c, int a, int b,
					 bool &foundUQ, bool &foundR,
					 int &bestScore, pair<int, int> &bestPair)
{
	// 如果已经 foundUQ=true，则优先级最高不再判断
	if (foundUQ)
		return;

	// 先看是否 u-q-flippable
	if (is_valuable_for_noncritical(a, b).re)
	{
		if (is_qualified_pairs({a, b}))
		{
			// 计算分数
			int sc = score[a] + score[b] + clause_weight[c];
			// 比较 sc 与 bestScore
			if (!foundUQ)
			{
				foundUQ = true;
				bestScore = sc;
				bestPair = {a, b};
			}
			else
			{
				// 如果原先也是 foundUQ=true，看谁分数更大
				if (sc > bestScore)
				{
					bestScore = sc;
					bestPair = {a, b};
				}
			}
		}
		else
		{
			int sc = score[a] + score[b] + clause_weight[c];
			if (!foundR)
			{
				foundR = true;
				bestScore = sc;
				bestPair = {a, b};
			}
			else
			{
				// 之前也 foundR=true => 分数更大才更新
				if (sc > bestScore)
				{
					bestScore = sc;
					bestPair = {a, b};
				}
			}
		}
	}
}

/**
 * 返回分数最高的 u-q 子句编号
 * 如果 LNQ 为空则返回 -1
 */
/* ------------------------------------------------------------------
 * 取 LNQ 中分数最大的子句，返回 (pair.first, score)
 * 若 LNQ 为空或所有桶都空，则返回 (0,0)
 * ------------------------------------------------------------------ */
std::pair<int, int> getBestUQFirstVarAndScore()
{
	if (LNQ.empty()) // 没有任何 Q(C)=1
		return {0, 0};

	/* step‑1: 找最大的 score（键值） */
	int maxScore = std::numeric_limits<int>::min();
	for (const auto &kv : LNQ) // kv.first = score
		if (!kv.second.empty() && kv.first > maxScore)
			maxScore = kv.first;

	if (maxScore == std::numeric_limits<int>::min())
		return {0, 0}; // 所有桶都空

	/* step‑2: 在该桶内找 time_stamp 最早的变量 */
	const std::deque<int> &dq = LNQ[maxScore];

	int bestVar = 0;
	int bestTime = std::numeric_limits<int>::max();
	for (int cid : dq)
	{
		int v = P_C[cid].first; // 只取 pair.first
		int t = time_stamp[v];
		if (t < bestTime)
		{
			bestTime = t;
			bestVar = v;
		}
	}
	return {bestVar, maxScore};
}

/* ------------------------------------------------------------------
 * 取 LNR 中分数最大的子句，返回 (pair.first, score)
 * ------------------------------------------------------------------ */
std::pair<int, int> getBestRevFirstVarAndScore()
{
	if (LNR.empty())
		return {0, 0};

	int maxScore = std::numeric_limits<int>::min();
	for (const auto &kv : LNR)
		if (!kv.second.empty() && kv.first > maxScore)
			maxScore = kv.first;

	if (maxScore == std::numeric_limits<int>::min())
		return {0, 0};

	const std::deque<int> &dq = LNR[maxScore];

	int bestVar = 0;
	int bestTime = std::numeric_limits<int>::max();
	for (int cid : dq)
	{
		int v = P_C[cid].first;
		int t = time_stamp[v];
		if (t < bestTime)
		{
			bestTime = t;
			bestVar = v;
		}
	}
	return {bestVar, maxScore};
}

#endif
