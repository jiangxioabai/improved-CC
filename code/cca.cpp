#include "basis.h"
#include "cca.h"
#include "cw.h"
#include "preprocessor.h"
#include <functional>
#include <signal.h>
#include <stdlib.h>
#include <iostream>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>

#include <functional> // 引入std::function
#include <chrono>	  // 用于计时
int Q_C[MAX_CLAUSES];
int R_C[MAX_CLAUSES];
int T_C[MAX_CLAUSES];
int S_C[MAX_CLAUSES];
// P_C 是 array of pair<int,int>
std::pair<int, int> P_C[MAX_CLAUSES];

// 在全局作用域或main函数之前定义统计变量
double step1_flip_time = 0, step2_flip_time = 0, reversible_flip_time = 0, diversification_flip_time = 0;
int step1_flip_count = 0, sd_flip_count = 0, step2_flip_count = 0, reversible_flip_count = 0, diversification_flip_count = 0;

void handle_sigterm(int signum)
{
	std::cerr << "Timeout reached!" << std::endl;
	std::cerr << "Steps: " << step << ", Tries: " << tries << std::endl;

	std::cerr << "1-step flips: " << step1_flip_count
			  << ", Total time: " << step1_flip_time << " s"
			  << ", Average time: "
			  << (step1_flip_count > 0 ? step1_flip_time / step1_flip_count : 0) << " s"
			  << std::endl;

	std::cerr << "sd flips: " << sd_flip_count
			  << std::endl;

	std::cerr << "2-step flips: " << step2_flip_count
			  << ", Total time: " << step2_flip_time << " s"
			  << ", Average time: "
			  << (step2_flip_count > 0 ? step2_flip_time / step2_flip_count : 0) << " s"
			  << std::endl;

	std::cerr << "Reversible flips: " << reversible_flip_count
			  << ", Total time: " << reversible_flip_time << " s"
			  << ", Average time: "
			  << (reversible_flip_count > 0 ? reversible_flip_time / reversible_flip_count : 0) << " s"
			  << std::endl;

	std::cerr << "Diversification flips: " << diversification_flip_count
			  << ", Total time: " << diversification_flip_time << " s"
			  << ", Average time: "
			  << (diversification_flip_count > 0 ? diversification_flip_time / diversification_flip_count : 0) << " s"
			  << std::endl;

	std::cout.flush();
	exit(0);
}
static int last_picked_var = 0;
// 初始为0，表示尚未有上一次选的变量

int pick_var_1()
{
	int i, k, c, v;
	int best_var;
	lit *clause_c;
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if (goodvar_stack_fill_pointer > 0) // 如果存在1-step q-flippable变量，goodvar_stack存的1-step q-flippable变量
	{
		auto step1_start = std::chrono::high_resolution_clock::now();
		best_var = goodvar_stack[0]; // 选择第一个变量作为候选
		// 遍历所有1-step q-flippable变量，选分数最高的变量，相同则选上次翻转最早的变量，这里time_stamp[]初始化应该是0，表示上次反转时间
		for (i = 1; i < goodvar_stack_fill_pointer; ++i)
		{
			v = goodvar_stack[i];
			if (score[v] > score[best_var])
				best_var = v;
			else if (score[v] == score[best_var] && time_stamp[v] < time_stamp[best_var])
				best_var = v;
		}
		// 记录 1-step 的时间
		auto step1_end = std::chrono::high_resolution_clock::now();
		step1_flip_time += std::chrono::duration<double>(step1_end - step1_start).count();
		step1_flip_count++;
		// 更新 last_picked_var
		last_picked_var = best_var;
		// cout << "[DEBUG] 1-step q-flippable var = " << best_var
		// 	 << ", score[" << best_var << "]=" << score[best_var]
		// 	 << ", original score=" << score[best_var]
		// 	 << std::endl;
		return best_var;
	}

	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for (i = 0; i < unsatvar_stack_fill_pointer; ++i)
	{
		if (score[unsatvar_stack[i]] > sigscore)
		{
			best_var = unsatvar_stack[i];
			break;
		}
	}

	for (++i; i < unsatvar_stack_fill_pointer; ++i)
	{
		v = unsatvar_stack[i];
		if (score[v] > score[best_var])
			best_var = v;
		else if (score[v] == score[best_var] && time_stamp[v] < time_stamp[best_var])
			best_var = v;
	}

	if (best_var != 0)
	{
		sd_flip_count++;
		// 更新 last_picked_var
		last_picked_var = best_var;
		return best_var;
	}

	updateNonCriticalClausesInLN(step);

	// 2step_q-flippable变量
	auto step2_start = std::chrono::high_resolution_clock::now();
	best_var = 0;
	// 先遍历critical ，再遍历noncritical，判断是否是qualified_pairs，再判断是否是valuable
	pair<int, int> pairs;
	int maxscore = 0;
	// 调试：看看 LCQ 是否有数据
	// cout << "[DEBUG] LCQ size = " << LCQ.size() << std::endl;
	for (const auto &entry : LCQ)
	{ // 假设 LCQ_unordered 是 unordered_map<pair<int,int>, int, pair_hash>
		if (entry.second > maxscore)
		{
			maxscore = entry.second;
			int xi = int(entry.first >> 32); // 高 32 位
			best_var = xi;
		}
	}

	// noncritical
	auto uqvresult = getBestUQFirstVarAndScore();
	int firstVar = uqvresult.first;
	int uqScore = uqvresult.second;
	if (firstVar != 0 && uqScore > maxscore)
	{
		// cout << "[DEBUG] getBestUQFirstVarAndScore => firstVar = "
		// 	 << firstVar << ", uqcore=" << uqScore << std::endl;
		maxscore = uqScore;
		best_var = firstVar;
		// cout << "[DEBUG] 2-step q-flippable var from LNQ = " << std::endl;
	}
	// else{
	// 	cout << "[DEBUG] 2-step q-flippable var from LCQ = " << std::endl;
	// }

	// 记录 2-step 的时间
	auto step2_end = std::chrono::high_resolution_clock::now();
	step2_flip_time += std::chrono::duration<double>(step2_end - step2_start).count();
	if (best_var != 0)
	{


		// // 如果想判断是否“连续”选同一个变量:
		// bool isConsecutive = (best_var == last_picked_var);
		// std::cerr << "   => consecutive pick: "
		//     << (isConsecutive ? "YES" : "NO") << std::endl;
		step2_flip_count++;
		// 更新 last_picked_var
		last_picked_var = best_var;
		return best_var;
	}
	// else
	// {
	// 	// 如果没进入 return，看看具体是哪个条件失败
	// 	if (best_var == 0)
	// 	{
	// 		std::cerr << "[DEBUG] 2-step no best_var found (best_var=0)" << std::endl;
	// 	}
	// 	else
	// 	{
	// 		std::cerr << "[DEBUG] 2-step best_var=" << best_var
	// 				  << ", but score[" << best_var << "]="
	// 				  << score[best_var]
	// 				  << " <= sigscore=" << sigscore << std::endl;
	// 	}
	// }

	// reversible变量
	auto reversible_start = std::chrono::high_resolution_clock::now();
	maxscore = 0;
	for (const auto &entry : LCR)
	{ // 假设 LCQ_unordered 是 unordered_map<pair<int,int>, int, pair_hash>
		if (entry.second > maxscore)
		{
			maxscore = entry.second;
			int xi = int(entry.first >> 32); // 高 32 位
			best_var = xi;
		}
	}
	// cout << "[DEBUG] from LCR manual iteration => best_var=" << best_var 
	// << ", maxscore=" << maxscore << endl;
	// noncritical
	auto result = getBestRevFirstVarAndScore();

	int bestVar = result.first;
	int bestScore = result.second;
	// cout << "[DEBUG] getBestRevFirstVarAndScore => bestVar=" 
	// << bestVar << ", bestScore=" << bestScore << endl;
	if (bestVar != 0 && bestScore > maxscore)
	{
		// cout << "[DEBUG] getBestRevFirstVarAndScore => bestVar = "
		// 	 << bestVar << ", score=" << bestScore << std::endl;
		// cout << "[DEBUG] reversible var from LNR " << std::endl;
		maxscore = bestScore;
		best_var = bestVar;
	}
	auto reversible_end = std::chrono::high_resolution_clock::now();
	reversible_flip_time += std::chrono::duration<double>(reversible_end - reversible_start).count();
	
	
	if (best_var != 0)
	{
		// 在进行 return best_var 之前:
		// std::cerr << "[DEBUG pick_var_1] step=" << step
		//         << " pick current=" << best_var
		//         << ", last=" << last_picked_var << std::endl;
		reversible_flip_count++;
		return best_var;
	}

	// 如果既没有 q-flippable变量，也没有reversible变量，则更新子句权重，并随机游走
	/**Diversification Mode**/

	update_clause_weights();

	/*focused random walk*/
	auto diversifacation_start = std::chrono::high_resolution_clock::now();
	c = unsat_stack[rand() % unsat_stack_fill_pointer]; // 随机选择一个不满足子句
	clause_c = clause_lit[c];
	best_var = clause_c[0].var_num; // 将子句中的第一个变量作为候选
	// 同样倾向于选择该随机子句中分数最高的变量，相同则选上次翻转最早的变量
	for (k = 1; k < clause_lit_count[c]; ++k)
	{
		v = clause_c[k].var_num;
		if (time_stamp[v] < time_stamp[best_var])
			best_var = v;
		// if(score[v]>score[best_var]) best_var = v;
		// else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
	}
	// 记录 diversification 的时间
	auto diversifacation_end = std::chrono::high_resolution_clock::now();
	diversification_flip_time += std::chrono::duration<double>(diversifacation_end - diversifacation_start).count();
	diversification_flip_count++; // 增加次数
	// 更新 last_picked_var
	last_picked_var = best_var;
	return best_var;
}

// set functions in the algorithm 设置子句权重
void settings()
{
	set_clause_weighting();
}

void local_search(int max_flips)
{
	int flipvar;

	for (step = 0; step < max_flips; step++)
	{
		// find a solution
		if (unsat_stack_fill_pointer == 0)
			return;

		flipvar = pick_var_1();

		flip(flipvar);

		time_stamp[flipvar] = step;
	}
}

int main(int argc, char *argv[])
{
	int seed, i;
	int satisfy_flag = 0;
	struct tms start, stop;
	// 注册 SIGTERM 信号处理器
	signal(SIGTERM, handle_sigterm);
	cout << "c This is CCAnr [Version: 2013.4.18] [Author: Shaowei Cai]." << endl;

	times(&start);

	if (build_instance(argv[1]) == 0) // 构建实例
	{

		cout << "Invalid filename: " << argv[1] << endl;
		return -1;
	}

	sscanf(argv[2], "%d", &seed);

	srand(seed);

	if (unitclause_queue_end_pointer > 0)
		preprocess(); // 进行预处理，消掉单变量子句

	build_neighbor_relation(); // 构建变量邻居关系

	cout << "c Instance: Number of variables = " << num_vars << endl;
	cout << "c Instance: Number of clauses = " << num_clauses << endl;
	cout << "c Instance: Ratio = " << instance_ratio << endl;
	cout << "c Instance: Formula length = " << formula_len << endl;
	cout << "c Instance: Avg (Min,Max) clause length = " << avg_clause_len << " (" << min_clause_len << "," << max_clause_len << ")" << endl;
	cout << "c Algorithmic: Random seed = " << seed << endl;
	cout << "c criticalpair size = " << criticalpairs.size() << endl;
	cout << "c noncriticalpair size = " << noncritical_set.size() << endl;

	// 多次局部搜索
	for (tries = 0; tries <= max_tries; tries++)
	{
		settings(); // 初始化设置子句权重

		init(); // 初始化

		local_search(max_flips); // 局部搜索

		if (unsat_stack_fill_pointer == 0)
		{
			if (verify_sol() == 1)
			{
				satisfy_flag = 1;
				break;
			}
			else
				cout << "c Sorry, something is wrong." << endl; /////
		}
	}

	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime + stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

	if (satisfy_flag == 1)
	{
		cout << "s SATISFIABLE" << endl;
		print_solution();
	}
	else
		cout << "s UNKNOWN" << endl;

	cout << "c solveSteps = " << tries << " tries + " << step << " steps (each try has " << max_flips << " steps)." << endl;
	cout << "c solveTime = " << comp_time << endl;

	// 输出统计数据：四种 flip 类型的时间和次数
	cout << "1-step flips: " << step1_flip_count << ", Total time: " << step1_flip_time << " seconds" << endl;
	cout << "2-step flips: " << step2_flip_count << ", Total time: " << step2_flip_time << " seconds" << endl;
	cout << "Reversible flips: " << reversible_flip_count << ", Total time: " << reversible_flip_time << " seconds" << endl;
	cout << "Diversification flips: " << diversification_flip_count << ", Total time: " << diversification_flip_time << " seconds" << endl;

	free_memory();

	return 0;
}
