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
#include <algorithm>
#include <deque>   // 记录最近 M 步

#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
std::vector<uint32_t> active_LCQ, active_LCR;   // 更合适
// 保存最近由 SD 或 Diversification 产生的翻转变量
// const int MAX_RECENT = 10;                 // M，可随时调大/小
// static std::deque<int> recent_vars;        // 只存 var 编号
// 单参数控制 recent：k=窗口大小=扫描数；0=禁用




struct Last2Flip
{
	int a = -1, b = -2;

	void record(int x)
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

// 判断 (xi,xj) 是否 critical
/* cca.h 旧版 */
inline bool is_critical_pair(int xi,int xj)
{
    // return criticalDir.count(pair_key_directed(xi,xj));   // ← 慢

    /* 新版：利用 LCP_vec 扫描 */
    for (uint32_t cid : LCP_vec[xi])    // xi 出现在哪些 critical pair 中
        if (crit_pairs[cid].second == xj)   // directed (xi,xj)
            return true;
    return false;
}


/* 是否 valuable（Observation 21，非-critical 版本）
 * 前两条完全照抄；条款③ 按 score[] 判定 */
// ------------------------------------------------------------------
// 新版：两指针第一次相交即返回 —— 仅在一个子句中共现时返回 true
// ------------------------------------------------------------------
inline bool is_valuable_noncritical_pair(int xi,int xj)
{
    /* 3. 分数条件 */
    int Nxi = score[xi], Nxj = score[xj];
    if (!((Nxi >= 0 && Nxj >= 0) || (Nxj >= 1 && Nxi == -1)))
        return false;     
    /* 0. 若是 critical pair 直接排除（理论上出现 ≥2 子句） */
    if (is_critical_pair(xi,xj)) return false;

    /* 1. 用“两指针”扫描 var_lit[xi] 与 var_lit[xj] 寻找唯一子句 */
    /* 2. O(1) 查唯一子句表 */
    auto it = uniq_pair_clause.find(pair_key_directed(xi,xj));
    if (it == uniq_pair_clause.end()) return false;        // 根本未共现
    uint32_t cid = it->second;                             // 唯一子句 (>=1)

    /* 2. 该子句下恰好 1 个变量满足，且满足的是 xi 或 xj */
    if (sat_count[cid] != 1) return false;
    if (sat_var[cid] != xi && sat_var[cid] != xj) return false;

    /* 3. 分数条件 */
    return true;  // 满足所有条件，返回 true
}






bool is_qualified_pairs(uint32_t cid)
{
	const auto &xi = var_change[crit_pairs[cid].first];
	const auto &xj = var_change[crit_pairs[cid].second];
	if (xi.a < 0 || xi.b < 0 || xj.a < 0 || xj.b < 0)
		return true;

	return !((xi.a == xj.a && xi.b == xj.b) || (xi.a == xj.a && xi.b == xj.b));
}

inline bool var_satisfies_clause_scan(int v, int c)
{
	for (lit *p = clause_lit[c]; p->var_num != 0; ++p)
	{
		if (p->var_num == v && cur_soln[v] == p->sense)
			return true;
	}
	return false;
}

// 旧：compute_pair_correction(int a,int b)
// 新：只收 cid；若其他地方已拿到 (xi,xj)，先用 cid_of_critical 转 cid
inline int compute_pair_correction(uint32_t cid)
{
    int corr = 0;

    /* 遍历所有包含该 pair 的子句 */
    for (int c : LCC_vec[cid])
    {
        if (sat_count[c] == 0 ||
            (sat_count[c] == 2 &&
             var_satisfies_clause_scan(crit_pairs[cid].first,  c) &&
             var_satisfies_clause_scan(crit_pairs[cid].second, c)))
        {
            corr -= clause_weight[c];
        }
        else if ((sat_count[c] == 1 && sat_var[c] == crit_pairs[cid].first) ||
                 (sat_count[c] == 1 && sat_var[c] == crit_pairs[cid].second))
        {
            corr += clause_weight[c];
        }
    }
    return corr;
}

void initialize_PD()
{
    size_t K = crit_pairs.size();          // ← K 就在这里定义
    for (uint32_t cid = 0; cid < K; ++cid){
        PD[cid] = compute_pair_correction(cid);
	}
}


/* 辅助：快速从 active_XXX 中 O(1) 删元素 */
inline void erase_from_vec(std::vector<uint32_t>& vec, uint32_t cid)
{
    for (size_t i = 0; i < vec.size(); ++i)
        if (vec[i] == cid) { vec[i] = vec.back(); vec.pop_back(); break; }
}

/* 主函数 —— 只传变量 v，下层全用 cid ---------------------------------- */
void update_deltas_on_flip(int v)
{
    /* ---------- ① 扫描 v 所在子句，对每条 (x,y) 重新算 correction ---------- */
    for (int i = 0; i < var_lit_count[v]; ++i)
    {
        int c = var_lit[v][i].clause_num;          // 该子句编号

        /* 摘出除 v 以外的两个变量 x,y（3-SAT） ------------------------- */
        int x = 0, y = 0;
        for (lit* q = clause_lit[c]; q->var_num; ++q) {
            int u = q->var_num;
            if (u == v) continue;
            (!x ? x : y) = u;
        }
        if (!x || !y) continue;
        /* ---- 使用有向 key 过滤非-critical ---- */
        PairKey k = pair_key_directed(x, y);     // 顺序 x→y

        uint32_t idx = uint32_t(k) & MASK;        // 位 AND —— 1 条指令
        uint32_t cid = cid_of_key[idx];

        if (cid == UINT32_MAX || dir_keys[cid] != k)
            continue;                             // 不是 critical-pair，跳过

        /* 重新计算 correction 并更新 PD -------------------------------- */
        int corr = compute_pair_correction(cid);   // 新版收 cid
        int old  = PD[cid];
        PD[cid]  = corr;

        /* 若你维护 active_LCQ/LCR，需要根据 Δ 调桶 -------------------- */
        if (old >= 0 && corr < 0) {
            erase_from_vec(active_LCQ, cid);
            active_LCR.push_back(cid);
        } else if (old < 0 && corr >= 0) {
            erase_from_vec(active_LCR, cid);
            active_LCQ.push_back(cid);
        }
    }

    /* ---------- ② v 参与的所有 critical-pair（cid 已预存） ------------ */
    for (uint32_t cid : LCP_vec[v])
    {
        int corr = compute_pair_correction(cid);
        int old  = PD[cid];
        PD[cid]  = corr;

        if (old >= 0 && corr < 0) {
            erase_from_vec(active_LCQ, cid);
            active_LCR.push_back(cid);
        } else if (old < 0 && corr >= 0) {
            erase_from_vec(active_LCR, cid);
            active_LCQ.push_back(cid);
        }
    }
}


struct Result
{
	int value; // 关联的整数值
	bool re;   // 操作是否成功
};

inline Result is_valuable_for_critical(uint32_t cid)
{
    int  xi = crit_pairs[cid].first;
    int  xj = crit_pairs[cid].second;
    int  n  = compute_pair_correction(cid) + score[xi] + score[xj];   // computePairScore

    bool ok = (n > 0) &&
              (n - score[xi] > 0) &&
              ((n - score[xi]) >  score[xj]) &&
              ((n - score[xj]) <= 0);
    return {n, ok};
}

/* 新版：只接收 cid */
inline void updatePairStructures(uint32_t cid)
{
    int xi = crit_pairs[cid].first;
    int xj = crit_pairs[cid].second;

    /* ① 重新计算属性 */
    bool valuable  = is_valuable_for_critical(cid).re;
    bool qualified = is_qualified_pairs(cid);
    int  scoreVal  = PD[cid] + score[xi] + score[xj];   // PD 里已是 Δ

    /* ② 按三种情形维护 LCQ / LCR */
    if (!valuable) {                            /* ❶ no longer valuable */
        erase_from_vec(active_LCQ, cid);
        erase_from_vec(active_LCR, cid);
        // PD[cid] = scoreVal;                     // 或设成 -32768
        return;
    }

    // PD[cid] = scoreVal;                         // 存最新分数

    if (qualified) {                            /* ❷ valuable & qualified */
        erase_from_vec(active_LCR, cid);
        if (std::find(active_LCQ.begin(), active_LCQ.end(), cid) == active_LCQ.end())
            active_LCQ.push_back(cid);
    } else {                                    /* ❸ valuable & !qualified */
        erase_from_vec(active_LCQ, cid);
        if (std::find(active_LCR.begin(), active_LCR.end(), cid) == active_LCR.end())
            active_LCR.push_back(cid);
    }
}



/* 预处理后：crit_pairs[cid] 已填好，PD[cid] 也在 initialize_PD() 初始化 */
/* active_LCQ / active_LCR 只存 cid                                    */

void initializePairStructures()          // 不再传 set
{
    active_LCQ.clear();
    active_LCR.clear();                  // 如果后面要用 LCR

    std::cout << "Initializing Pair Structures\n";

    const size_t K = crit_pairs.size();

    for (uint32_t cid = 0; cid < K; ++cid)
    {
        int xi = crit_pairs[cid].first;
        int xj = crit_pairs[cid].second;

        /* 判定 valuable / qualified（沿用你原逻辑） */
        Result res_xy = is_valuable_for_critical(cid);
        if (!res_xy.re) continue;
        bool qualified = is_qualified_pairs(cid);     // 双向都不 valuable

        /* 方向选择：保持 time_stamp 小的在前，可选也可省略 */
        int a = xi, b = xj;

        /* cid 已固定，无需再重新编号 —— 直接用 PD[cid] */
        int val = PD[cid] + score[a] + score[b];
        // PD[cid] = val;                  // 存最新综合分
        if (qualified)
            active_LCQ.push_back(cid);      // 进 LCQ
		else
			active_LCR.push_back(cid);      // 进 LCR
        // 若还需初始化 LCR，这里按你的 qualified 判据 push 到 active_LCR
    }

    std::cout << "Initialization complete. LCQ size = "
              << active_LCQ.size() << ", LCR size = "
              << active_LCR.size()  << '\n';
}


inline void unsat(int clause)
{
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
	push(clause,unsat_stack);
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]++;
		if(unsat_app_count[v]==1)
		{
			index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
			push(v,unsatvar_stack);	
		}
	}
}


inline void sat(int clause)
{
	int index,last_unsat_clause;

	//since the clause is satisfied, its position can be reused to store the last_unsat_clause
	last_unsat_clause = pop(unsat_stack);
	index = index_in_unsat_stack[clause];
	unsat_stack[index] = last_unsat_clause;
	index_in_unsat_stack[last_unsat_clause] = index;
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v,last_unsat_var;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]--;
		if(unsat_app_count[v]==0)
		{
			last_unsat_var = pop(unsatvar_stack);
			index = index_in_unsatvar_stack[v];
			unsatvar_stack[index] = last_unsat_var;
			index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

//initiation of the algorithm
void init()
{
	int 		v,c;
	int			i,j;
	int			clause;
	
	var_change = std::vector<Last2Flip>(num_vars + 1);
	//Initialize edge weights
	for (c = 0; c<num_clauses; c++)
		clause_weight[c] = 1;

	//init unsat_stack
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

	/*figure out var score*/
	int lit_count;
	for (v=1; v<=num_vars; v++) 
	{
		if(fix[v]==1) 
		{
			score[v] = -100000;
			continue;
		}
		
		score[v] = 0;

		lit_count = var_lit_count[v];
		
		for(i=0; i<lit_count; ++i)
		{
			c = var_lit[v][i].clause_num;
			if (sat_count[c]==0) score[v]++;
			else if (sat_count[c]==1 && var_lit[v][i].sense==cur_soln[v]) score[v]--;
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
		if(score[v]>0)// && conf_change[v]==1)
		{
			already_in_goodvar_stack[v] = 1;
			push(v,goodvar_stack);
			
		}
		else already_in_goodvar_stack[v] = 0;
	}
	
	//setting for the virtual var 0
	time_stamp[0]=0;
	//pscore[0]=0;
	initialize_PD();
	// pscore[0]=0;
	//  解、子句状态、得分初始化完毕后，初始化 LCQ,LCR
	// initializePairStructures();
}


void flip(int flipvar)
{
	cur_soln[flipvar] = 1 - cur_soln[flipvar];
	
	int i,j;
	int v,c;

	// 如果历史记录已经有两事件，则移除最早的一个
	var_change[flipvar].record(flipvar);
	// 翻转之后，输出flipvar对应var_change情况
	for (i = 0; var_neighbor[flipvar][i] != 0; i++)
	{
		j = var_neighbor[flipvar][i];
		var_change[j].record(flipvar);
	}
	lit* clause_c;
	
	int org_flipvar_score = score[flipvar];
	
	//update related clauses and neighbor vars
	for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = clause_lit[c];
		if(cur_soln[flipvar] == q->sense)
		{
			++sat_count[c];
			
			if (sat_count[c] == 2) //sat_count from 1 to 2
				score[sat_var[c]] += clause_weight[c];
			else if (sat_count[c] == 1) // sat_count from 0 to 1
			{
				sat_var[c] = flipvar;//record the only true lit's var
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] -= clause_weight[c];
                
				sat(c);
			}
		}
		else // cur_soln[flipvar] != cur_lit.sense
		{
			--sat_count[c];
			if (sat_count[c] == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					if(p->sense == cur_soln[v] )
					{
						score[v] -= clause_weight[c];
						sat_var[c] = v;
						break;
					}
				}
			}
			else if (sat_count[c] == 0) //sat_count from 1 to 0
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] += clause_weight[c];
				unsat(c);
			}//end else if
			
		}//end else
	}

	score[flipvar] = -org_flipvar_score;
	
	/*update CCD */
	int index;
	
	conf_change[flipvar] = 0;
	//remove the vars no longer goodvar in goodvar stack 
	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = goodvar_stack[index];
		if(score[v]<=0)
		{
			goodvar_stack[index] = pop(goodvar_stack);
			already_in_goodvar_stack[v] = 0;
		}	
	}

	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	int* p;
	for(p=var_neighbor[flipvar]; (v=*p)!=0; p++)
	{
		conf_change[v] = 1;
		
		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
		{
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] = 1;
		}
	}

	// update_deltas_on_flip(flipvar);
    // /* 1. 已经更新过 flipvar 自身相关 pair 的 Δ */


    // /* 2. 扫描与 flipvar 相邻的变量 v */
    // for (int* p = var_neighbor[flipvar]; int v = *p; ++p)
    // {
    //     /* 若变量 v 参与任何 critical-pair，就一定记录在 LCP_vec[v] 里 */
    //     for (uint32_t cid : LCP_vec[v])           // ← 这里的元素已是 cid
    //     {
    //         updatePairStructures(cid);            // 新版接口只收 cid
    //     }
    // }

}

#endif

