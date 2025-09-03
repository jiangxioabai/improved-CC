#include "basis.h"
#include "cca.h"
#include "cw.h"
#include "preprocessor.h"
#include <climits>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>
#include <signal.h>
#include <cstdlib>   // getenv, atoi
// static long long g_sd_pick = 0;  // 记录 pick_var() 里 SD 模式命中 valuable/reversible 的次数
// static long long g_sd_pick_val = 0;  // 命中 valuable 的次数
// static long long g_sd_pick_rev = 0;  // 命中 reversible 的次数
#ifndef MAX_TOPK_SD
#define MAX_TOPK_SD 40          // Top-K 允许的最大上限
#endif
int g_topk_sd = 10;             // 运行时的 Top-K，默认 10
int g_recent_k = 10;
std::deque<int> recent_vars;        // 只存 var 编号
// 顶部新增
int g_tabu_tenure = 0;                // 默认关闭；用 env: TABU_TENURE=3 来启用
static std::vector<int> tabu_until;   // tabu 过期步数（size = num_vars+1）
static int best_unsat = INT_MAX;      // 历史最小未满足子句数（用于更激进的志向准则，可选）


inline void push_recent_var(int v) {
    if (g_recent_k <= 0) return;          // 关闭 recent 时不记录
    if (v <= 0 || v > num_vars) return;
    // 去重：若已存在，先移除旧位置
    for (auto it = recent_vars.begin(); it != recent_vars.end(); ++it) {
        if (*it == v) { recent_vars.erase(it); break; }
    }
    // 最新放最前
    recent_vars.push_front(v);
    // 裁到 g_recent_k
    while ((int)recent_vars.size() > g_recent_k) recent_vars.pop_back();
}

void handle_sigterm(int signum)
{
	std::cerr << "Timeout reached!" << std::endl;
	std::cerr << "Steps: " << step << ", Tries: " << tries << std::endl;
    // std::cerr << "sd_pick_val = " << g_sd_pick_val << std::endl;
    // std::cerr << "sd_pick_rev = " << g_sd_pick_rev << std::endl;
	std::cout.flush();
	exit(0);
}


//pick a var to be flip
int pick_var()
{
	int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(goodvar_stack_fill_pointer>0)
	{
		best_var = goodvar_stack[0];
		
		for(i=1; i<goodvar_stack_fill_pointer; ++i)
		{
			v=goodvar_stack[i];
			if(score[v]>score[best_var]) best_var = v;
			else if(score[v]==score[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
		}

		return best_var;
	}
	
	/*SD (significant decreasing) mode, the level with aspiration*/
/* SD (significant decreasing) mode, with Top-10 + critical/noncritical valuable check */
{
    // const int TOPK = (g_topk_sd > MAX_TOPK_SD ? MAX_TOPK_SD : g_topk_sd);
    const int TOPK = MAX_TOPK_SD; 
    int cand_v[MAX_TOPK_SD];
    int cand_s[MAX_TOPK_SD];

    for (int k = 0; k < TOPK; ++k) { cand_v[k] = 0; cand_s[k] = INT_MIN; }

    for (int ii = 0; ii < unsatvar_stack_fill_pointer; ++ii) {
        int v = unsatvar_stack[ii];
        int s = score[v];
        if (s <= sigscore) continue;

        int pos = -1;
        for (int k = 0; k < TOPK; ++k) {
            if (cand_v[k] == 0 || s > cand_s[k] ||
               (s == cand_s[k] && time_stamp[v] < time_stamp[cand_v[k]])) { pos = k; break; }
        }
        if (pos < 0) continue;
        for (int k = TOPK - 1; k > pos; --k) { cand_v[k] = cand_v[k-1]; cand_s[k] = cand_s[k-1]; }
        cand_v[pos] = v; cand_s[pos] = s;
    }

    // 2) 在 Top-10 里优先找 valuable，其次 reversible；最后用 Top-10 分数第一
    int chosen_val = 0, best_val_score = INT_MIN;
    int chosen_rev = 0, best_rev_score = INT_MIN;

    for (int k = 0; k < TOPK; ++k) {
        int v = cand_v[k]; if (!v) continue;

        if (!LCP_vec[v].empty()) {
            // —— critical：复用你现有的 API —— //
            for (size_t t = 0; t < LCP_vec[v].size(); ++t) {
                uint32_t cid = LCP_vec[v][t];
                Result r = is_valuable_for_critical(cid);   // r.re 说明这对在当前状态 valuable
                if (!r.re) continue;

                // 分数：你已有 r.value（等于 PD[cid] + score[xi] + score[xj]）
                int s = r.value;

                if (is_qualified_pairs(cid)) { // 你已有的“qualified==1 归为 valuable；0 归为 reversible”
                    if (!chosen_val || s > best_val_score ||
                       (s == best_val_score && time_stamp[v] < time_stamp[chosen_val])) {
                        chosen_val = v; best_val_score = s;
                    }
                } else {
                    if (!chosen_rev || s > best_rev_score ||
                       (s == best_rev_score && time_stamp[v] < time_stamp[chosen_rev])) {
                        chosen_rev = v; best_rev_score = s;
                    }
                }
            }
        } else {
            // —— noncritical：复用 uniq_pair_clause + is_valuable_noncritical_pair —— //
            // 注：我们只做“方向判断”，其余条件交给现有的 is_valuable_noncritical_pair 过滤
            for (int *p = var_neighbor[v]; *p; ++p) {
                int u = *p;

                // 先用你的快速筛选（唯一共现 + 1-sat 等必要条件）
                if (!is_valuable_noncritical_pair(v, u)) continue;

                // 拿到这对（v->u）的唯一共现子句
                auto it = uniq_pair_clause.find(pair_key_directed(v, u));
                if (it == uniq_pair_clause.end()) continue;
                uint32_t c = it->second;

                // 面向变量的方向判断：对 v valuable ⇔ 该唯一子句当前由 v 满足
                // 可逆（次优）⇔ 当前由 u 满足
                if (sat_count[c] == 1 && sat_var[c] == v) {
                    int s = score[v] + score[u];  // noncritical 的比较分，保持你既有口径
                    if (!chosen_val || s > best_val_score ||
                       (s == best_val_score && time_stamp[v] < time_stamp[chosen_val])) {
                        chosen_val = v; best_val_score = s;
                    }
                } else if (sat_count[c] == 1 && sat_var[c] == u) {
                    int s = score[v] + score[u];
                    if (!chosen_rev || s > best_rev_score ||
                       (s == best_rev_score && time_stamp[v] < time_stamp[chosen_rev])) {
                        chosen_rev = v; best_rev_score = s;
                    }
                }
            }
        }
    }

    // 3) 三层保底：valuable > reversible > Top-10 分数第一（不再全扫一遍）
    if (chosen_val) { return chosen_val; }
    if (chosen_rev) { return chosen_rev; }
    if (cand_v[0])  { return cand_v[0];  }
}
// 若 Top-10 为空，就落到后续阶段（2-step/随机等）


// Top-10 为空则继续后续 2-step / 随机等



	// 2step_q-flippable变量
// 	best_var = 0;
// 	int xi = 0, xj = 0;
// 	int maxscore = 0;
// // ── DEBUG: 打印 LCQ 大小 ───────────────────────────────
// // std::cerr << "[DEBUG] active_LCQ.size() = " << active_LCQ.size()
// //           << ", initial maxscore = " << maxscore << "\n";
// // ────────────────────────────────────────────────────
//     for (uint32_t cid : active_LCQ) {
//         xi = crit_pairs[cid].first;
//         xj = crit_pairs[cid].second;
//         int s = PD[cid]+score[xi] + score[xj];
//         if (s > maxscore) {
//             maxscore = s;
//             best_var = xi;   // keep your “direction” choice
//         }
//     }

// 	if (best_var != 0)
// 	{
// 	 	return best_var;
// 	}

// 	// reversible变量


// // ── DEBUG: 打印 LCR 大小 ───────────────────────────────
// // std::cerr << "[DEBUG] active_LCR.size() = " << active_LCR.size()
// //           << ", carryover maxscore = " << maxscore << "\n";
// // ────────────────────────────────────────────────────
//     for (uint32_t cid : active_LCR) {
//         // PD[cid] already contains Δ + score[xi] + score[xj]
//         xi = crit_pairs[cid].first;
//         xj = crit_pairs[cid].second;
//         int s = PD[cid]+score[xi] + score[xj];
//         if (s > maxscore) {
//             maxscore = s;
//             best_var = xi;   // keep your “direction” choice
//         }
//     }


// 	if (best_var != 0)
// 	{

// 		return best_var;
// 	}

/* ======================= Recent-Var 阶段 ======================= */
if (g_recent_k > 0 && !recent_vars.empty()) {
    int rv_best = 0, rv_best_score = INT_MIN;
    bool rv_best_is_val = false;

    // 扫描数 = min(g_recent_k, 当前队列长度)
    int limit = std::min<int>(g_recent_k, (int)recent_vars.size());
    int scanned = 0;

    for (int rv : recent_vars) {
        if (scanned >= limit) break;
        ++scanned;

        if (!LCP_vec[rv].empty()) {
            // ---------- critical ----------
            for (size_t t = 0; t < LCP_vec[rv].size(); ++t) {
                uint32_t cid = LCP_vec[rv][t];
                Result r = is_valuable_for_critical(cid);
                if (!r.re) continue;
                int s = r.value;
                bool is_val = is_qualified_pairs(cid);

                if (is_val) {
                    if (!rv_best || !rv_best_is_val || s > rv_best_score ||
                        (s == rv_best_score && time_stamp[rv] < time_stamp[rv_best])) {
                        rv_best = rv; rv_best_score = s; rv_best_is_val = true;
                    }
                } else {
                    if (!rv_best || (!rv_best_is_val && (s > rv_best_score ||
                        (s == rv_best_score && time_stamp[rv] < time_stamp[rv_best])))) {
                        rv_best = rv; rv_best_score = s; rv_best_is_val = false;
                    }
                }
            }
        } else {
            // ---------- noncritical ----------
            // for (int *p = var_neighbor[rv]; int nb = *p; ++p) {
            for (int *p = var_neighbor[rv]; *p; ++p) {
                int nb = *p;
                if (!is_valuable_noncritical_pair(rv, nb)) continue;
                auto it = uniq_pair_clause.find(pair_key_directed(rv, nb));
                if (it == uniq_pair_clause.end()) continue;
                uint32_t cc = it->second;

                int s = score[rv] + score[nb];
                if (sat_count[cc] == 1 && sat_var[cc] == rv) {
                    // valuable
                    if (!rv_best || !rv_best_is_val || s > rv_best_score ||
                        (s == rv_best_score && time_stamp[rv] < time_stamp[rv_best])) {
                        rv_best = rv; rv_best_score = s; rv_best_is_val = true;
                    }
                } else if (sat_count[cc] == 1 && sat_var[cc] == nb) {
                    // reversible
                    if (!rv_best || (!rv_best_is_val && (s > rv_best_score ||
                        (s == rv_best_score && time_stamp[rv] < time_stamp[rv_best])))) {
                        rv_best = rv; rv_best_score = s; rv_best_is_val = false;
                    }
                }
            }
        }
    }

    if (rv_best) return rv_best;  // valuable 优先，其次 reversible
}
/* ======================= Recent-Var 阶段结束 ======================= */


	/**Diversification Mode**/

	update_clause_weights();
	
	/*focused random walk*/
	c = unsat_stack[rand()%unsat_stack_fill_pointer];
	clause_c = clause_lit[c];
	best_var = clause_c[0].var_num;
	for(k=1; k<clause_lit_count[c]; ++k)
	{
		v=clause_c[k].var_num;
		if(time_stamp[v]<time_stamp[best_var]) best_var = v;
		// if(score[v]>score[best_var]) best_var = v;
		// else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
	}
	// 记录 diversification 的时间

    push_recent_var(best_var);
	return best_var;
}


//set functions in the algorithm
void settings()
{
	set_clause_weighting();
}

void local_search(int max_flips)
{
	int flipvar;
     
	for (step = 0; step<max_flips; step++)
	{
		//find a solution
		if(unsat_stack_fill_pointer==0) return;

		flipvar = pick_var();

		flip(flipvar);

		time_stamp[flipvar] = step;
	}
}


int main(int argc, char* argv[])
{
	int     seed,i;
	int		satisfy_flag=0;
	struct 	tms start, stop;
    
    cout<<"c This is CCAnr [Version: 2013.4.18] [Author: Shaowei Cai]."<<endl;	
	
	times(&start);

	if (build_instance(argv[1])==0)
	{
		cout<<"Invalid filename: "<< argv[1]<<endl;
		return -1;
	}

    sscanf(argv[2],"%d",&seed);
    
    srand(seed);
    
    if(unitclause_queue_end_pointer>0) preprocess();
    
    build_neighbor_relation();
    build_critical_pairs(); 
    build_critical_index(num_vars); 
	build_LCC_from_criticalPairs();         // ← 🔧 补上

	cout<<"c Instance: Number of variables = "<<num_vars<<endl;
	cout<<"c Instance: Number of clauses = "<<num_clauses<<endl;
	cout<<"c Instance: Ratio = "<<instanceratio<<endl;
	cout<<"c Instance: Formula length = "<<formula_len<<endl;
	cout<<"c Instance: Avg (Min,Max) clause length = "<<avg_clause_len<<" ("<<min_clause_len<<","<<max_clause_len<<")"<<endl;
	cout<<"c Algorithmic: Random seed = "<<seed<<endl;
    cout << "c critical pairs: " << crit_pairs.size() << endl;
    // 运行时读取 Top-K：仅环境变量 TOPK_SD（无命令行解析）
    // if (const char* env = std::getenv("TOPK_SD")) {
    //     int k = std::atoi(env);
    //     if (k >= 2 && k <= MAX_TOPK_SD) g_topk_sd = k;   // 夹在 [2, 40]
    // }

    // 读取 RECENT_K（0=禁用 recent）
    if (const char* s = std::getenv("RECENT_K")) {
        int k = std::atoi(s);
        if (k >= 0 && k <= 512) g_recent_k = k;
    }
    cout << "c recent_k=" << g_recent_k << endl;
	for (tries = 0; tries <= max_tries; tries++) 
	{
		settings();
		 
		 init();
	 
		 local_search(max_flips);

		 if (unsat_stack_fill_pointer==0) 
		 {
		 	if(verify_sol()==1) {satisfy_flag = 1; break;}
		    else cout<<"c Sorry, something is wrong."<<endl;/////
		 }
	}

	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

    if(satisfy_flag==1)
    {
    	cout<<"s SATISFIABLE"<<endl;
		print_solution();
    }
    else  cout<<"s UNKNOWN"<<endl;
    
    cout<<"c solveSteps = "<<tries<<" tries + "<<step<<" steps (each try has "<<max_flips<<" steps)."<<endl;
    cout<<"c solveTime = "<<comp_time<<endl;
    // cout << "c sd_pick_val = " << g_sd_pick_val << endl;
    // cout << "c sd_pick_rev = " << g_sd_pick_rev << endl;
    // cout << "c sd_pick     = " << g_sd_pick << endl;


    free_memory();

    return 0;
}
