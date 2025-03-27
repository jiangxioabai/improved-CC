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

// -----------------------------------------------------------------------new
#include <iostream>
#include <unordered_map>
#include <map>
#include <deque>
#include <vector>
#include <utility>
#include <unordered_set>
#include <set>

// 用vector来管理，代码更简洁易懂
#define pop(stack) stack[--stack ## _fill_pointer] //pop则_fill_pointer--
#define push(item, stack) stack[stack ## _fill_pointer++] = item //push则_fill_pointer++

using namespace std;
int T_C[MAX_CLAUSES];                      // T(C)
int Q_C[MAX_CLAUSES];                      // Q(C)
int R_C[MAX_CLAUSES];                      // R(C)
int S_C[MAX_CLAUSES];                      // S(C)

int computePairScore(int xi, int xj);

extern int key_flip;


// LN 用来保存所有非关键且 N(C)==1 的子句编号
// LN[i] 存储所有满足条件的子句编号，其中 i 为变量编号（1 <= i <= num_vars）
std::vector<vector<int>> LN;
extern std::set<int> noncritical_clauses;
struct LCQEntry {
    int var1;      // 例如保留原始顺序
    int var2;
    int pairScore; // 综合分数，计算方式为 computePairScore(var1, var2)
};
std::vector<LCQEntry> LCR;


//criticalVars 为全局变量，存储所有 critical 变量的编号
extern std::vector<int> criticalVars;
// 全局 LCQ 列表
vector<LCQEntry> LCQ;

bool U_array[MAX_VARS];  
std::vector<int> LU;

// 全局定义两个集合，类型使用 std::set 保证唯一性和有序性
extern std::set<std::pair<int,int>> qualified_pairs_in_critical;
std::set<std::pair<int,int>> valuable_pairs_for_critical;

// 全局变量var_change[i]表示变量 i 的邻域内最近两次改变的变量队列，长度为2（只记录近两次的）
std::vector<std::deque<int>> var_change;
// 需要每次遍历flipvar及其邻居和二次邻居的var_change，用于判断受到影响的是否为unqualified_pairs
// 定义全局变量 neighbor_pairs 和 unqualified_pairs
// 定义存储所有相邻变量对的集合（每个对保证 (v, u) 中 v < u）
// set<pair<int, int>> neighbor_pairs;
set<pair<int, int>> unqualified_pairs;
// // 定义存储 critical pairs 的集合（即重复出现的对）
// set<pair <int, int>> critical_pairs;
// // 定义存储 noncritical pairs 的集合（即重复出现的对）
// map<pair <int, int>, int> noncritical_pairs;


// 用vector来管理，代码更简洁易懂
#define pop(stack) stack[--stack ## _fill_pointer] //pop则_fill_pointer--
#define push(item, stack) stack[stack ## _fill_pointer++] = item //push则_fill_pointer++


// 将子句标记为不满足，并更新相关变量
inline void unsat(int clause) //这里clause应该表示子句在整个公式F中的下标（从0开始）
{   //unsat_stack_fill_pointer指当前新入stack的元素下标，也表示当前stack元素数量
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer; // 记录子句在不满足栈中的位置
	push(clause,unsat_stack); // 入栈
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	//p是一个lit结构体向量，每个lit包含 子句下标（0开始） 变量下标（1开始） 从句真值
	//clause_lit[i][j]表示第i个子句的第j个lit，
	//这里p初始化指向为clause_lit的第clause个子句的第一个lit的指针，子句包含了很多lit结构体
	//v表示p所指向的lit结构体的变量数这一成员，子句末尾变量一般用0作为标记
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]++;// 增加变量（下标为v）在不满足子句中的出现次数
		if(unsat_app_count[v]==1)//首次出现，则压入不满足变量栈，并记录位置
		{
			index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
			push(v,unsatvar_stack);	// 将变量压入不满足变量栈
		}
	}
}

// 将子句标记为满足，并更新相关变量
inline void sat(int clause)
{
	int index,last_unsat_clause;

	//since the clause is satisfied, its position can be reused to store the last_unsat_clause
	//交换函数输入clause和unsat_stack最后一个子句位置，并将clause出栈
	last_unsat_clause = pop(unsat_stack);// 从不满足栈中移除最新一条不满足的子句
	index = index_in_unsat_stack[clause];// 获得clause在不满足栈中的index
	unsat_stack[index] = last_unsat_clause;// 将last_unsat_clause插入到该index中
	index_in_unsat_stack[last_unsat_clause] = index;// 更新last_unsat_clause的index
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v,last_unsat_var;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]--;// 减少变量（下标为v）在不满足子句中的出现次数
		if(unsat_app_count[v]==0)// 如果次数减少为0，则将其出栈，同样是交换v和unsat_stack最后一个变量位置，并将v出栈
		{
			last_unsat_var = pop(unsatvar_stack);
			index = index_in_unsatvar_stack[v];
			unsatvar_stack[index] = last_unsat_var;
			index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

void init()
{
	int 		v,c;
	int			i,j;
	int			clause;
	// 初始化var_change，长度为 count，每个队列为空
	var_change = std::vector<std::deque<int>>(num_vars+1); 
	// 初始化qualified_pair



	//Initialize edge weights 初始化子句权重为1
	for (c = 0; c<num_clauses; c++)
		clause_weight[c] = 1;

	//init unsat_stack
	// 初始化不满足子句栈和不满足变量栈
	unsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;

	//init solution
	for (v = 1; v <= num_vars; v++) {

        if(fix[v]==0){
            if(rand()%2==1) cur_soln[v] = 1;
            else cur_soln[v] = 0;

			time_stamp[v] = 0;
			conf_change[v] = 1;
			unsat_app_count[v] = 0;
		
			//pscore[v] = 0;
		}
		
	}

	/* figure out sat_count, and init unsat_stack */
	for (c=0; c<num_clauses; ++c) 
	{
		if(clause_delete[c]==1) continue;
		
		sat_count[c] = 0;
		
		for(j=0; j<clause_lit_count[c]; ++j)
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
	for (v=1; v<=num_vars; v++) 
	{

		U_array[v] = false; // 初始化bool_U_array
		// 如果变量被固定，则将其得分设置为一个极小值
		if(fix[v]==1) 
		{
			score[v] = -100000;
			continue;
		}
		
		score[v] = 0;
		orig_score[v] = 0;
		// 获取变量所在的所有文字数量
		lit_count = var_lit_count[v];
		// 遍历变量的所有文字，计算得分
		for(i=0; i<lit_count; ++i)
		{	// 获取该文字所在子句的编号
			c = var_lit[v][i].clause_num;
            if (sat_count[c] == 1) {
                if (var_lit[v][i].sense == cur_soln[v])
                    score[v]--;  // 子句仅由当前变量满足，则得分减1
					orig_score[v]--;  // 子句仅由当前变量满足，则得分减1
                if (noncritical_clauses.find(c) != noncritical_clauses.end() && find(LN[v].begin(), LN[v].end(), c) == LN[v].end())
                    LN[v].push_back(c);
            }
            else if (sat_count[c] == 0) {
                score[v]++;  // 子句不满足，则翻转该变量后子句满足，得分+1
				orig_score[v]++;  // 子句不满足，则翻转该变量后子句满足，得分+1
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
	
		
	//init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v=1; v<=num_vars; v++) 
	{
		if(fix[v]==1)  continue;
		// 如果变量得分大于 0，则将其加入 goodvar_stack
		if(score[v]>0)// && conf_change[v]==1)
		{
			already_in_goodvar_stack[v] = 1;
			push(v,goodvar_stack);
			
		}// 否则标记为未在 goodvar_stack 中
		else already_in_goodvar_stack[v] = 0;
	}
	
	//setting for the virtual var 0 时戳初始化为0
	time_stamp[0]=0;
	//pscore[0]=0;

    // 解、子句状态、得分初始化完毕后，初始化 LCQ
    // build_qualified_pairs_in_critical();
    // build_valuable_pairs_for_critical();
    // init_LCQ();
}


void flip(int flipvar)
{
	cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转 flipvar 的值
	//选择翻转变量后应该更新flipvar及其邻居的var_change
	//var_change用于判断其和邻居是否为qualifie pair
	//below
    //更新flipvar自己的var_change
	int i,j;
	// 如果历史记录已经有两事件，则移除最早的一个
	if (var_change[flipvar].size() == 2) {
		var_change[flipvar].pop_front();
	}
	var_change[flipvar].push_back(flipvar);
	//更新flipvar邻居的var_change
	for(i = 0; var_neighbor[flipvar][i] != 0; i++)
	{
		// 获取邻居编号
		j = var_neighbor[flipvar][i];
		// 如果历史记录已经有两事件，则移除最早的一个
		if (var_change[j].size() == 2) {
			var_change[j].pop_front();
		}
		var_change[j].push_back(flipvar);
	}
	//above 



	cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转 flipvar 的值
	
	

	cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转 flipvar 的值
	
	int v,c;

	lit* clause_c;
	// 在分数没更新时，保存flipvar的原始得分
	int org_flipvar_score = score[flipvar];
	int orig_flipvar_score = orig_score[flipvar];

	//update related clauses and neighbor vars 遍历flipvar所在的子句，q是flipvar的所有文字，c是文字对应的子句编号
	for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = clause_lit[c];// 获取当前子句的文字列表
		// 如果翻转后 flipvar 的当前值==子句中的文字真值
		// 如，q->sense=0时，变量1->0，则文字假变真；q->sense=1时，变量0->1，则文字假变真。else则子句满足数-1
		if(cur_soln[flipvar] == q->sense)
		{
			++sat_count[c];
			
			if (sat_count[c] == 2){ //sat_count from 1 to 2
				// 增加满足子句的另一个变量的得分
				//∵之前翻转另一变量,子句从满足变成不满足,因此子句对另一变量的分数贡献为-clause_weight[c]
				// 这儿要修改成不加权和加权的两种
				score[sat_var[c]] += clause_weight[c];
                orig_score[sat_var[c]] += 1; // 使用固定权重1
			}else if (sat_count[c] == 1) // sat_count from 0 to 1
			{
				sat_var[c] = flipvar;//record the only true lit's var
				// flipvar翻转后子句才满足
				// ∵子句其他变量翻转后sat_count由增加变不增加，∴得分减少
				// ∵flipvar再翻转后sat_count-1，，∴得分也减少
                for(lit* p = clause_c; (v = p->var_num) != 0; p++) {
                    score[v] -= clause_weight[c];
                    orig_score[v] -= 1; // 固定权重1
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
			if (sat_count[c] == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					// q->sense=0时,cur_soln[v]=0,则当前文字为真，翻转v，sat-1；
					// q->sense=1时,cur_soln[v]=1,则当前文字为真，翻转v，sat-1；
					if(p->sense == cur_soln[v])
					{
						
						score[v] -= clause_weight[c];
						orig_score[v] -= 1; // 固定权重1
						sat_var[c] = v;// 目前唯一满足子句c的变量是v
						break;
					}
				}
			}
			else if (sat_count[c] == 0) //sat_count from 1 to 0
			{
				// 此时子句c不满足，任意翻转c包含的变量均可使其满足，得分+
                for(lit* p = clause_c; (v = p->var_num) != 0; p++) {
                    score[v] += clause_weight[c];
                    orig_score[v] += 1; // 固定权重1
                }
				// 将子句标记为不满足，并更新相关变量
				unsat(c);
			}//end else if
			
		}//end else

        // // ----- LN 更新开始 -----
        // // 对于每个子句 c，根据 sat_count[c] 是否等于 1，
        // // 若 sat_count[c]==1 并且 c 属于 noncritical_clauses，则加入 LN（避免重复）
        // // 否则如果 sat_count[c] != 1，则从 LN 中删除 c（如果存在）
        // if (sat_count[c] == 1) {
        //     if (noncritical_clauses.find(c) != noncritical_clauses.end()) {
        //         if (find(LN.begin(), LN.end(), c) == LN.end())
        //             LN.push_back();
        //     }
        // } else {
        //     auto it = find(LN.begin(), LN.end(), c);
        //     if (it != LN.end())
        //         LN.erase(it);
        // }
        // // ----- LN 更新结束 -----
	}
	// flipvar翻转后，分数为翻转前的相反数，邻居分数已经在上面更新过了
	score[flipvar] = -org_flipvar_score;
	orig_score[flipvar] = -orig_flipvar_score;
	/*update CCD */
	int index;
	// 因为flipvar刚翻转过，conf_change设置为unflippable
	conf_change[flipvar] = 0;
	// flipvar翻转后，更新goodvar_stack中元素，选择1-step q-flippable变量
	// 条件1：score>0；条件2：conf_change=1
	//remove the vars no longer goodvar in goodvar stack 
	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = goodvar_stack[index];
		// 分数不满足移除，这里会把 flipvar 移除，因为其分数已被更新为负
		if(score[v]<=0)
		{
			goodvar_stack[index] = pop(goodvar_stack);
			already_in_goodvar_stack[v] = 0;
		}	
	}

	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	// 唯一使用了邻居关系的地方
	int* p;
	for(p=var_neighbor[flipvar]; (v=*p)!=0; p++)
	{
		conf_change[v] = 1;
		if (key_flip == 1){
		    U_array[v] = true;
			LU.push_back(v);
		}
		// 分数大于0，且还未在goodvar_stack，则入栈
		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
		{
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] = 1;
		}
	}



    // // ===== 新增 LCQ 更新 =====
    // update_qualified_pairs_for_critical(flipvar);
	// update_valuable_pairs_for_critical(flipvar);
	// init_LCQ();
	// init_LCR();
}

// ------------------------------------------------------------------------new








bool is_qualified_pairs(pair<int,int> pairs) {
    // 取出两个变量对应的变化队列
    std::deque<int>& dq_xi = var_change[pairs.first];
    std::deque<int>& dq_xj = var_change[pairs.second];
    
    // 仅当两个队列都恰好包含两个事件时才判断；否则直接返回 true
    if (dq_xi.size() == 2 && dq_xj.size() == 2) {
        // 检查各自队列中元素是否不同
        if (dq_xi[0] == dq_xj[0] && dq_xi[1] == dq_xj[1]) {
            // 如果两个集合完全相同，则返回 false
            return false;
        }
    }
    return true;
}
struct Result {
	int value;    // 关联的整数值
    bool re; // 操作是否成功
};
Result is_valuable_for_critical(int xi, int xj) {
    // 根据你的说明：
    // score(F, X_j, s_i_t) = computePairScore(xi, xj) - orig_score[xi]
    // score(F, X_i, s_i,j_t) = computePairScore(xi, xj) - orig_score[xj]
    //
    // 条件要求：
    // 1. orig_score[xi] + (computePairScore(xi, xj) - orig_score[xi]) > 0   => computePairScore(xi, xj) > 0
    // 2. (computePairScore(xi, xj) - orig_score[xi]) > 0
    // 3. (computePairScore(xi, xj) - orig_score[xi]) > orig_score[xj]
    // 4. (computePairScore(xi, xj) - orig_score[xj]) <= 0
    //
    // 下面将 computePairScore(xi, xj) 用 n_i_j 表示：
    int n_i_j = computePairScore(xi, xj);
    // 条件2
    bool cond2 = (n_i_j - orig_score[xi] > 0);
    // 条件1: 其实就是 n_i_j > 0
    bool cond1 = (n_i_j > 0);
    // 条件3: (n_i_j - orig_score[xi]) > orig_score[xj]
    bool cond3 = ((n_i_j - orig_score[xi]) > orig_score[xj]);
    // 条件4: (n_i_j - orig_score[xj]) <= 0
    bool cond4 = ((n_i_j - orig_score[xj]) <= 0);
    
    if (cond1 && cond2 && cond3 && cond4)
        return {n_i_j, true};
    else
        return {n_i_j, false};
}


Result is_valuable_for_noncritical(int xi, int xj) {
    // 确保键是 canonical 格式
	int n_i_j = computePairScore(xi, xj);
    int a = min(xi, xj);
    int b = max(xi, xj);
    auto it = noncriticalpairs.find({a, b});
    // 如果没有记录，则说明该对不出现，返回 false
    // if (it == noncriticalpairs.end())
    //     return {n_i_j, false};
    int clauses = it->second;
    // 条件1：必须恰好只有一个子句中同时出现
    // if (clauses.size() != 1)
    //     return {n_i_j, false};
    int c = clauses;
    // 条件2：该子句下，只有一个变量满足，即 sat_count[c] == 1 且唯一满足的变量是 xi 或 xj
    if (sat_count[c] != 1)
        return {n_i_j, false};
    if (sat_var[c] != xi && sat_var[c] != xj)
        return {false};
    // 条件3：得分条件，根据论文描述，可以判断 (score(xj) >= 0 && score(xi) >= 0) 或 (score(xj) >= 1 && score(xi) == -1)
    if ((orig_score[xj] >= 0 && orig_score[xi] >= 0) || (orig_score[xj] >= 1 && orig_score[xi] == -1))
        return {n_i_j, true};
    return {n_i_j, false};
}




// bool is_valuable_for_noncritical(int xi, int xj)

// 占位函数：计算变量对 (xi, xj) 的分数 N(F, xi, xj, s)
// 此处假设 N_score[v] 已经记录了单个变量 v 的得分
// 并且使用前面实现的 computePairDeltaOverlap(xi, xj) 计算 Delta_overlap


bool clauseSatisfiedWithFlips(int c, int flipXi, int flipXj) {
    // 遍历子句 c 中的每个文字
    for (int j = 0; j < clause_lit_count[c]; j++) {
        int var = clause_lit[c][j].var_num;
        if (var == 0) break;
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
            return true;  // 子句中只要有一个文字为真，则子句满足
    }
    return false;
}

// 下面函数实现伪代码计算 Delta_overlap
// 计算变量对 (xi, xj) 对应的 Delta_overlap，依赖于 LCC(xi,xj)
int computePairDeltaOverlap(int xi, int xj) {
    int Delta_overlap = 0;
    // 确保 xi < xj
    int a = min(xi, xj), b = max(xi, xj);
    long long key = ((long long)a) * MAX_VARS + b;
    // 如果 LCC 中没有该对，则返回 0
    if (LCC.find(key) == LCC.end())
        return 0;
    vector<int>& clauseList = LCC[key];
    // 遍历 LCC(xi, xj) 中所有子句 C_t
    for (int c : clauseList) {
        // old_satisfied：在当前赋值 s 下，子句 c 是否满足（1或0）
        int old_satisfied = clauseSatisfiedWithFlips(c, -1, -1) ? 1 : 0;
        // new_satisfied_ij：在同时翻转 xi 和 xj 后，子句 c 是否满足
        int new_satisfied_ij = clauseSatisfiedWithFlips(c, xi, xj) ? 1 : 0;
        int change_for_ij = new_satisfied_ij - old_satisfied;
        // onlyXi_satisfied：只翻转 xi 后子句 c 是否满足
        int onlyXi_satisfied = clauseSatisfiedWithFlips(c, xi, -1) ? 1 : 0;
        int change_for_i = onlyXi_satisfied - old_satisfied;
        // onlyXj_satisfied：只翻转 xj 后子句 c 是否满足
        int onlyXj_satisfied = clauseSatisfiedWithFlips(c, -1, xj) ? 1 : 0;
        int change_for_j = onlyXj_satisfied - old_satisfied;
        int overlap_change_for_C = change_for_ij - change_for_i - change_for_j;
        Delta_overlap += overlap_change_for_C;
    }
    return Delta_overlap;
}

int computePairScore(int xi, int xj) {
    // 假设 N_score 是一个全局数组，其中 N_score[v] 表示 N(F, v, s)
  
    int delta_overlap = computePairDeltaOverlap(xi, xj);
    return orig_score[xi] + orig_score[xj] + delta_overlap;
}

// 全局定义两个集合，类型使用 std::set 保证唯一性和有序性
// std::set<std::pair<int,int>> qualified_pairs_in_critical;
// std::set<std::pair<int,int>> valuable_pairs_for_critical;

// 构建 qualified 的 critical pair 集合：
// 遍历 global criticalPairs（假设为 std::vector<std::pair<int,int>> 或其他容器），
// 若某个 pair 满足 is_qualified_pairs 条件，则同时将 (xi,xj) 和 (xj,xi) 插入。
// void build_qualified_pairs_in_critical() {
//     qualified_pairs_in_critical.clear();
//     for (const auto &p : criticalpairs) {
//         int xi = p.first;
//         int xj = p.second;
//         if (is_qualified_pairs(xi, xj)) {
//             qualified_pairs_in_critical.insert({xi, xj});
//             qualified_pairs_in_critical.insert({xj, xi});
//         }
//     }
// }

// 初始化：遍历 global criticalPairs 中的所有 pair，如果不满足 qualified 条件，则插入
// void build_unqualified_pairs_for_critical() {
//     unqualified_pairs.clear();
//     for (const auto &p : criticalpairs) {
//         int xi = p.first;
//         int xj = p.second;
//         if (!is_qualified_pairs(xi, xj)) {
//             unqualified_pairs.insert({xi, xj});
//             unqualified_pairs.insert({xj, xi});
//         }
//     }
// }

// 构建 valuable 的 critical pair 集合：
// 遍历 global criticalPairs，对于每个 pair，
 // 如果 (xi,xj) 或 (xj,xi) 至少有一方向满足 is_valuable_for_critical，则插入对应的顺序，
 // 如果只有后者满足，则插入 (xj,xi)；否则（两方向都满足或只有正向满足）插入 (xi,xj)。
// void build_valuable_pairs_for_critical() {
//     valuable_pairs_for_critical.clear();
//     for (const auto &p : criticalpairs) {
//         int xi = p.first;
//         int xj = p.second;
//         bool valuable_xy = is_valuable_for_critical(xi, xj);
//         bool valuable_yx = is_valuable_for_critical(xj, xi);
//         if (valuable_xy || valuable_yx) {
//             if (valuable_yx && !valuable_xy)
//                 valuable_pairs_for_critical.insert({xj, xi});
//             else
//                 valuable_pairs_for_critical.insert({xi, xj});
//         }
//     }
// }


// void update_qualified_pairs_for_critical(int v) {
//     // 遍历 v 的每个邻居 u
//     for (int i = 0; var_neighbor[v][i] != 0; i++) {
//         int u = var_neighbor[v][i];
//         // 如果 u 在 LCP 中没有记录，则跳过
//         if (LCP.find(u) == LCP.end())
//             continue;
//         // 遍历 LCP[u] 中所有 pair
//         for (const auto &p : LCP[u]) {
//             int xi = p.first;
//             int xj = p.second;
//             // 判断 qualified 条件
//             // 判断 qualified 条件
//             if (is_qualified_pairs(xi, xj)) {
//                 // 满足 qualified：确保加入 qualified_pairs_in_critical，并删除 unqualified_pairs 中的对应记录（正向和反向）
//                 qualified_pairs_in_critical.insert({xi, xj});
//                 qualified_pairs_in_critical.insert({xj, xi});
//                 unqualified_pairs.erase({xi, xj});
//                 unqualified_pairs.erase({xj, xi});
//             } else {
//                 // 不满足：删除 qualified_pairs_in_critical 中的记录，并插入到 unqualified_pairs 中（正向和反向）
//                 qualified_pairs_in_critical.erase({xi, xj});
//                 qualified_pairs_in_critical.erase({xj, xi});
//                 unqualified_pairs.insert({xi, xj});
//                 unqualified_pairs.insert({xj, xi});
//             }
//         }
//     }
// }

// void update_valuable_pairs_for_critical(int v) {
//     // 遍历变量 v 的每个邻居 u
//     for (int i = 0; var_neighbor[v][i] != 0; i++) {
//         int u = var_neighbor[v][i];
//         // 如果 u 没有在 LCP 中记录，则直接跳过
//         if (LCP.find(u) == LCP.end())
//             continue;
//         // 遍历 LCP[u] 中的每个 pair
//         for (const auto &p : LCP[u]) {
//             int xi = p.first;
//             int xj = p.second;
//             // 分别检查 (xi, xj) 与 (xj, xi) 是否满足 valuable 条件
//             bool valuable_xy = is_valuable_for_critical(xi, xj);
//             bool valuable_yx = is_valuable_for_critical(xj, xi);
//             if (valuable_xy || valuable_yx) {
//                 // 如果只有后者满足，则按 (xj, xi) 存入；否则存 (xi, xj)
//                 if (valuable_yx && !valuable_xy)
//                     valuable_pairs_for_critical.insert({xj, xi});
//                 else
//                     valuable_pairs_for_critical.insert({xi, xj});
//             } else {
//                 // 两方向都不满足，则删除已有记录
//                 valuable_pairs_for_critical.erase({xi, xj});
//                 valuable_pairs_for_critical.erase({xj, xi});
//             }
//         }
//     }
// }



void init_LCQ() {
    std::set<std::pair<int,int>> intersection;
    std::set_intersection(qualified_pairs_in_critical.begin(), qualified_pairs_in_critical.end(),
                        valuable_pairs_for_critical.begin(), valuable_pairs_for_critical.end(),
                        std::inserter(intersection, intersection.begin()));
    
    LCQ.clear();
    for (auto &p : intersection) {
        int pairScore = computePairScore(p.first, p.second);
        LCQ.push_back({p.first, p.second, pairScore});
    }
}

void init_LCR() {
    LCR.clear();
    // 求 unqualified_pairs 和 valuable_pairs_for_critical 的交集
    std::set<std::pair<int,int>> intersection;
    std::set_intersection(unqualified_pairs.begin(), unqualified_pairs.end(),
                        valuable_pairs_for_critical.begin(), valuable_pairs_for_critical.end(),
                        std::inserter(intersection, intersection.begin()));
    // 对交集中的每个 pair 计算分数并存入 LCR
    for (auto &p : intersection) {
        int pairScore = computePairScore(p.first, p.second);
        LCR.push_back({p.first, p.second, pairScore});
    }
}


//initiation of the algorithm
// void init()
// {
// 	int 		v,c;
// 	int			i,j;
// 	int			clause;
	
// 	//Initialize edge weights 初始化子句权重为1
// 	for (c = 0; c<num_clauses; c++)
// 		clause_weight[c] = 1;

// 	//init unsat_stack
// 	// 初始化不满足子句栈和不满足变量栈
// 	unsat_stack_fill_pointer = 0;
// 	unsatvar_stack_fill_pointer = 0;

// 	//init solution
// 	for (v = 1; v <= num_vars; v++) {
        
//         if(fix[v]==0){
//             if(rand()%2==1) cur_soln[v] = 1;
//             else cur_soln[v] = 0;

// 			time_stamp[v] = 0;
// 			conf_change[v] = 1;
// 			unsat_app_count[v] = 0;
		
// 			//pscore[v] = 0;
// 		}
		
// 	}

// 	/* figure out sat_count, and init unsat_stack */
// 	for (c=0; c<num_clauses; ++c) 
// 	{
// 		if(clause_delete[c]==1) continue;
		
// 		sat_count[c] = 0;
		
// 		for(j=0; j<clause_lit_count[c]; ++j)
// 		{
// 			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
// 			{
// 				sat_count[c]++;
// 				sat_var[c] = clause_lit[c][j].var_num;	
// 			}
// 		}

// 		if (sat_count[c] == 0) 
// 			unsat(c);
// 	}

// 	// figure out var score 可以作为一个函数
// 	int lit_count;
// 	for (v=1; v<=num_vars; v++) 
// 	{
// 		// 如果变量被固定，则将其得分设置为一个极小值
// 		if(fix[v]==1) 
// 		{
// 			score[v] = -100000;
// 			continue;
// 		}
		
// 		score[v] = 0;
// 		// 获取变量所在的所有文字数量
// 		lit_count = var_lit_count[v];
// 		// 遍历变量的所有文字，计算得分
// 		for(i=0; i<lit_count; ++i)
// 		{	// 获取该文字所在子句的编号
// 			c = var_lit[v][i].clause_num;
// 			if (sat_count[c]==0) score[v]++; // 子句不满足，则flip该变量后，子句满足，因此得分+1
// 			else if (sat_count[c]==1 && var_lit[v][i].sense==cur_soln[v]) score[v]--;// 子句仅由当前变量满足，则得分减1
// 		}
// 	}
	
// 	/*
// 	int flag;
// 	//compute pscore and record sat_var and sat_var2 for 2sat clauses
// 	for (c=0; c<num_clauses; ++c) 
// 	{
// 		if(clause_delete[c]==1) continue;
		
// 		if (sat_count[c]==1)
// 		{
// 			for(j=0;j<clause_lit_count[c];++j)
// 			{
// 				v=clause_lit[c][j].var_num;
// 				if(v!=sat_var[c])pscore[v]++;
// 			}
// 		}
// 		else if(sat_count[c]==2)
// 		{
// 			flag=0;
// 			for(j=0;j<clause_lit_count[c];++j)
// 			{
// 				v=clause_lit[c][j].var_num;
// 				if(clause_lit[c][j].sense == cur_soln[v])
// 				{
// 					pscore[v]--;
// 					if(flag==0){sat_var[c] = v; flag=1;}
// 					else	{sat_var2[c] = v; break;}
// 				}
// 			}
		
// 		}
// 	}
// 	*/
	
		
// 	//init goodvars stack
// 	goodvar_stack_fill_pointer = 0;
// 	for (v=1; v<=num_vars; v++) 
// 	{
// 		if(fix[v]==1)  continue;
// 		// 如果变量得分大于 0，则将其加入 goodvar_stack
// 		if(score[v]>0)// && conf_change[v]==1)
// 		{
// 			already_in_goodvar_stack[v] = 1;
// 			push(v,goodvar_stack);
			
// 		}// 否则标记为未在 goodvar_stack 中
// 		else already_in_goodvar_stack[v] = 0;
// 	}
	
// 	//setting for the virtual var 0 时戳初始化为0
// 	time_stamp[0]=0;
// 	//pscore[0]=0;
// }

// void flip(int flipvar)
// {
// 	cur_soln[flipvar] = 1 - cur_soln[flipvar]; // 翻转 flipvar 的值
	
// 	// int i,j; 没用到
// 	int v,c;

// 	lit* clause_c;
// 	// 在分数没更新时，保存flipvar的原始得分
// 	int org_flipvar_score = score[flipvar];
	
// 	//update related clauses and neighbor vars 遍历flipvar所在的子句，q是flipvar的所有文字，c是文字对应的子句编号
// 	for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
// 	{
// 		clause_c = clause_lit[c];// 获取当前子句的文字列表
// 		// 如果翻转后 flipvar 的当前值==子句中的文字真值
// 		// 如，q->sense=0时，变量1->0，则文字假变真；q->sense=1时，变量0->1，则文字假变真。else则子句满足数-1
// 		if(cur_soln[flipvar] == q->sense)
// 		{
// 			++sat_count[c];
			
// 			if (sat_count[c] == 2) //sat_count from 1 to 2
// 				// 增加满足子句的另一个变量的得分
// 				//∵之前翻转另一变量,子句从满足变成不满足,因此子句对另一变量的分数贡献为-clause_weight[c]
// 				// 这儿要修改成不加权和加权的两种
// 				score[sat_var[c]] += clause_weight[c];
// 			else if (sat_count[c] == 1) // sat_count from 0 to 1
// 			{
// 				sat_var[c] = flipvar;//record the only true lit's var
// 				// flipvar翻转后子句才满足
// 				// ∵子句其他变量翻转后sat_count由增加变不增加，∴得分减少
// 				// ∵flipvar再翻转后sat_count-1，，∴得分也减少
// 				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] -= clause_weight[c];
//                 // 将子句标记为满足，并更新相关变量
// 				sat(c);
// 			}
// 		}
// 		// 如果翻转后 flipvar 的当前值！=子句中的文字真值
// 		// 如，q->sense=0时，变量0->1，则文字真变假；q->sense=1时，变量1->0，则文字真变假。else则子句满足数-1
// 		else // cur_soln[flipvar] != cur_lit.sense
// 		{
// 			--sat_count[c];
// 			if (sat_count[c] == 1) //sat_count from 2 to 1
// 			{
// 				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
// 				{
// 					// q->sense=0时,cur_soln[v]=0,则当前文字为真，翻转v，sat-1；
// 					// q->sense=1时,cur_soln[v]=1,则当前文字为真，翻转v，sat-1；
// 					if(p->sense == cur_soln[v])
// 					{
						
// 						score[v] -= clause_weight[c];
// 						sat_var[c] = v;// 目前唯一满足子句c的变量是v
// 						break;
// 					}
// 				}
// 			}
// 			else if (sat_count[c] == 0) //sat_count from 1 to 0
// 			{
// 				// 此时子句c不满足，任意翻转c包含的变量均可使其满足，得分+
// 				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] += clause_weight[c];
// 				// 将子句标记为不满足，并更新相关变量
// 				unsat(c);
// 			}//end else if
			
// 		}//end else
// 	}
// 	// flipvar翻转后，分数为翻转前的相反数，邻居分数已经在上面更新过了
// 	score[flipvar] = -org_flipvar_score;
	
// 	/*update CCD */
// 	int index;
// 	// 因为flipvar刚翻转过，conf_change设置为unflippable
// 	conf_change[flipvar] = 0;
// 	// flipvar翻转后，更新goodvar_stack中元素，选择1-step q-flippable变量
// 	// 条件1：score>0；条件2：conf_change=1
// 	//remove the vars no longer goodvar in goodvar stack 
// 	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
// 	{
// 		v = goodvar_stack[index];
// 		// 分数不满足移除，这里会把 flipvar 移除，因为其分数已被更新为负
// 		if(score[v]<=0)
// 		{
// 			goodvar_stack[index] = pop(goodvar_stack);
// 			already_in_goodvar_stack[v] = 0;
// 		}	
// 	}

// 	//update all flipvar's neighbor's conf_change to be 1, add goodvar
// 	// 唯一使用了邻居关系的地方
// 	int* p;
// 	for(p=var_neighbor[flipvar]; (v=*p)!=0; p++)
// 	{
// 		conf_change[v] = 1;
// 		// 分数大于0，且还未在goodvar_stack，则入栈
// 		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
// 		{
// 			push(v,goodvar_stack);
// 			already_in_goodvar_stack[v] = 1;
// 		}
// 	}
// }

#endif

