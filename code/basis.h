#ifndef _BASIS_H_
#define _BASIS_H_

#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <utility>
#include <set>
#include <map>
#include <iterator>   // ← 最后一行 include
using namespace std;   // ← 然后统一只写这一次


enum type{SAT3, SAT5, SAT7, strSAT} probtype;

/* limits on the size of the problem. */
#define MAX_VARS    4000010
#define MAX_CLAUSES 20000000

// 关于critical的数据定义 
// noncritical_clauses：用于存储所有在 noncriticalpairs 中出现过的子句编号
std::set<int> noncritical_clauses;

// 用于标记每个变量是否出现在某个 critical pair 中
bool isCriticalVar[MAX_VARS];

// Global集合：criticalPairs 存放所有 critical pair（变量对，满足 i < j），noncriticalPairs 存放所有非关键变量对
#include <vector>
#include <utility>
#include <set>

// 非关键 pair集合：键为 canonical pair (min, max)，值为出现该 pair 的不同子句编号列表
map<pair<int,int>, int> noncriticalpairs;
// 关键 pair集合：存储那些在不同子句中至少出现两次的 pair（canonical 形式）
set<pair<int,int>> criticalpairs;


using namespace std;
// 定义存储所有相邻变量对的集合（每个对保证 (v, u) 中 v < u）
set<pair<int, int>> neighbor_pairs;
// 定义存储 critical pairs 的集合（即重复出现的对）
set<std::pair<int,int>> qualified_pairs_in_critical;

// 我们定义 LCP 用于存储关键变量对应的 critical pair 列表，键为变量编号，值为该变量参与的所有 critical pair
unordered_map<int, vector<pair<int, int>>> LCP;

// 对于每个 critical pair (X_i, X_j)，使用 LCC 来记录所有出现该对的 critical 子句
// 这里使用 unordered_map，键构造方式与之前一致：key = (long long) i * MAX_VARS + j（保证 i < j）
#include <unordered_map>
unordered_map<long long, vector<int> > LCC;

// Define a data structure for a literal in the SAT problem.
// 有子句数量 变量数量 真值
struct lit {
    int clause_num;		//clause num, begin with 0
    int var_num;		//variable num, begin with 1
    int sense;			//is 1 for true literals, 0 for false literals. // 
};

/*parameters of the instance*/
int     num_vars;		//var index from 1 to num_vars
int     num_clauses;	//clause index from 0 to num_clauses-1
int		max_clause_len;
int		min_clause_len;
int		formula_len=0;
double	avg_clause_len;
double 	ratio;

/* literal arrays */				
lit*	var_lit[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
int		var_lit_count[MAX_VARS];        //amount of literals of each var
lit*	clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
int		clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause		

lit*	org_clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
int		org_clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause
int		simplify=0;
			
/* Information about the variables. */
int     orig_score[MAX_VARS]; //score without weight
int     score[MAX_VARS];				
int		time_stamp[MAX_VARS];
int		conf_change[MAX_VARS];
int*	var_neighbor[MAX_VARS]; //var_neighbor[i][j]： var i 的第j个邻居的编号
int		var_neighbor_count[MAX_VARS];
//int		pscore[MAX_VARS];
int		fix[MAX_VARS];

// sat_count = 1  以及 sat_var = xi or xj  for noncritical 2
// 不加权的单个变量的分数 for noncritical 3
/* Information about the clauses */			
int     clause_weight[MAX_CLAUSES];		
int     sat_count[MAX_CLAUSES];			
int		sat_var[MAX_CLAUSES]; //每个子句只有一个sat_var。初始化为0，sat_var[c]=0表示无变量满足子句c
// 问题：在多个变量满足子句c的情况下，只会记录其中一个；初始化时，记录的是编号最大的那个变量
//int		sat_var2[MAX_CLAUSES];

//unsat clauses stack
int		unsat_stack[MAX_CLAUSES];		//store the unsat clause number
int		unsat_stack_fill_pointer;
int		index_in_unsat_stack[MAX_CLAUSES];//which position is a clause in the unsat_stack

//variables in unsat clauses
int		unsatvar_stack[MAX_VARS];		
int		unsatvar_stack_fill_pointer;
int		index_in_unsatvar_stack[MAX_VARS];
int		unsat_app_count[MAX_VARS];		//a varible appears in how many unsat clauses

//configuration changed decreasing variables (score>0 and confchange=1)
int		goodvar_stack[MAX_VARS];		
int		goodvar_stack_fill_pointer;
int		already_in_goodvar_stack[MAX_VARS];

//unit clauses preprocess
lit		unitclause_queue[MAX_VARS];		
int		unitclause_queue_beg_pointer=0;
int     unitclause_queue_end_pointer=0;
int     clause_delete[MAX_CLAUSES];

/* Information about solution */    // 表示变量在当前解下的值
int             cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables

//cutoff
int		max_tries = 10000;
int		tries;
int		max_flips = 2000000000;
int		step;

void setup_datastructure();
void free_memory();
int build_instance(char *filename);
void build_neighbor_relation();

void free_memory()
{
	int i;
	for (i = 0; i < num_clauses; i++) 
	{
		delete[] clause_lit[i];
	}
	
	for(i=1; i<=num_vars; ++i)
	{
		delete[] var_lit[i];
		delete[] var_neighbor[i];
	}
}

/*
 * Read in the problem.
 */
int temp_lit[MAX_VARS]; //the max length of a clause can be MAX_VARS
int build_instance(char *filename)
{
	char    line[1000000];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i,j;
	int		v,c;//var, clause
	
	ifstream infile(filename);
	if(!infile.is_open())
		return 0;

	/*** build problem data structures of the instance ***/
	infile.getline(line,1000000);
	while (line[0] != 'p')
		infile.getline(line,1000000);

	sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);
	ratio = double(num_clauses)/num_vars;
	
	if(num_vars>=MAX_VARS || num_clauses>=MAX_CLAUSES)
	{
		cout<<"the size of instance exceeds out limitation, please enlarge MAX_VARS and (or) MAX_CLAUSES."<<endl;
		exit(-1);
	}
	
	for (c = 0; c < num_clauses; c++) 
	{
		clause_lit_count[c] = 0;
		clause_delete[c] = 0;
	}
	for (v=1; v<=num_vars; ++v)
	{
		var_lit_count[v] = 0;
		fix[v] = 0;
	}
		
	max_clause_len = 0;
	min_clause_len = num_vars;
		
	//Now, read the clauses, one at a time.
	for (c = 0; c < num_clauses; c++) 
	{
		infile>>cur_lit;

		while (cur_lit != 0) { 
			temp_lit[clause_lit_count[c]] = cur_lit;
			clause_lit_count[c]++;
		
			infile>>cur_lit;
		}
		
		clause_lit[c] = new lit[clause_lit_count[c]+1];
		
		for(i=0; i<clause_lit_count[c]; ++i)
		{
			clause_lit[c][i].clause_num = c;
			clause_lit[c][i].var_num = abs(temp_lit[i]);
			if (temp_lit[i] > 0) clause_lit[c][i].sense = 1;
				else clause_lit[c][i].sense = 0;
			
			var_lit_count[clause_lit[c][i].var_num]++;
		}
		clause_lit[c][i].var_num=0; 
		clause_lit[c][i].clause_num = -1;
        
        //unit clause
        if(clause_lit_count[c]==1)
        {
            unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][0];
            clause_delete[c]=1;
        }
		
		if(clause_lit_count[c] > max_clause_len)
			max_clause_len = clause_lit_count[c];
		else if(clause_lit_count[c] < min_clause_len)
			min_clause_len = clause_lit_count[c];
			
		formula_len += clause_lit_count[c];
	}
	infile.close();
	
	avg_clause_len = (double)formula_len/num_clauses;
	
	if(unitclause_queue_end_pointer>0)
	{
		simplify = 1;
		for (c = 0; c < num_clauses; c++) 
		{
			org_clause_lit_count[c] = clause_lit_count[c];
			org_clause_lit[c] = new lit[clause_lit_count[c]+1];
			for(i=0; i<org_clause_lit_count[c]; ++i)
			{
				org_clause_lit[c][i] = clause_lit[c][i];
			}
			
		}
	}

	
	//creat var literal arrays
	for (v=1; v<=num_vars; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v]+1];
		var_lit_count[v] = 0;	//reset to 0, for build up the array
	}
	//scan all clauses to build up var literal arrays
	for (c = 0; c < num_clauses; ++c) 
	{
		for(i=0; i<clause_lit_count[c]; ++i)
		{
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
	for (v=1; v<=num_vars; ++v) //set boundary
		var_lit[v][var_lit_count[v]].clause_num=-1;
	
	return 1;
}
// std::set<int, std::set<std::pair<int, int>>> neighbor_pairs;
// if find critical_set 
// else 存进去，记录子句编号
// 在这里面加
void build_neighbor_relation()
{
	// 动态分配一个数组，用于标记某个变量是否是当前变量的邻居，变量下标从1开始
	int*	neighbor_flag = new int[num_vars+1];
	// 临时变量：i, j 用于循环，count 用于计数，v, c 分别表示变量编号和子句编号
	int		i,j,count;
	int 	v,c;
	// 	v表示当前变量
	for(v=1; v<=num_vars; ++v)
	{
		// 初始化当前变量的邻居数量为 0
		var_neighbor_count[v] = 0;
		// fix[v] = 1 表示变量v是单变量
		if(fix[v]==1) continue;
		// 初始化 neighbor_flag 数组，标记所有变量初始为非邻居
		for(i=1; i<=num_vars; ++i)
			neighbor_flag[i] = 0;
		// 标记当前变量 v 自身，避免将其加入到自己的邻居列表中
		neighbor_flag[v] = 1;

		// 遍历变量 v 所在的所有子句
		for(i=0; i<var_lit_count[v]; ++i)
		{
			// var_lit[v][i]表示变量v的第i个lit，是一个结构体，获取当前子句编号
			c = var_lit[v][i].clause_num;
			// 个人理解，如果是子句c是被处理删除的单变量子句就继续下一个
			if(clause_delete[c]==1) continue;
			// 遍历当前子句中的所有文字（变量）
			for(j=0; j<clause_lit_count[c]; ++j)
			{
				// clause_lit[c][j]表示子句c的第j个lit，是一个结构体，clause_lit[c][j].var_num是c的第j个lit的变量编号
				if(neighbor_flag[clause_lit[c][j].var_num]==0)// 如果当前变量未被标记为邻居，则标记该变量为邻居，邻居+1
				{
					var_neighbor_count[v]++;
					neighbor_flag[clause_lit[c][j].var_num] = 1;

					int u = clause_lit[c][j].var_num;
                    // --- 更新 criticalpairs 和 noncriticalpairs ---
                    // 构造 canonical 形式的 pairKey: 较小的编号在前
                    int a = (v < u) ? v : u;
                    int b = (v < u) ? u : v;
                    std::pair<int,int> pairKey = {a, b};

					// 如果该 pairKey 不存在于 criticalpairs 中，则继续
                    if (criticalpairs.find(pairKey) == criticalpairs.end())
                    {
                        // 在 noncriticalpairs 中查找该 pairKey
                        auto it = noncriticalpairs.find(pairKey);
                        if (it != noncriticalpairs.end())
                        {
                            // 已经记录过，检查存储的子句编号是否与当前不同
                            if (it->second != c)
                            {
                                // 出现于不同子句中，将其视为 critical
                                criticalpairs.insert(pairKey);
                                noncriticalpairs.erase(it);
                            }
                            // 如果相同，则不用重复记录
                        }
                        else
                        {
                            // 第一次出现该 pairKey，记录当前子句编号 c
                            noncriticalpairs[pairKey] = c;
                        }
                    }
                    // --- 更新结束 ---


				}
			}
		}
		// 还原当前变量 v 的标记，确保其不会被加入到邻居列表中
		neighbor_flag[v] = 0;
 		// 动态分配数组，存储变量 v 的邻居变量列表
		var_neighbor[v] = new int[var_neighbor_count[v]+1];

		count = 0;
		// 遍历所有变量，将标记为邻居的变量加入到邻居列表中
		for(i=1; i<=num_vars; ++i)
		{
			// 如果变量被固定，则跳过
			if(fix[i]==1) continue;
			// 将标记为邻居的变量加入到邻居列表中
			if(neighbor_flag[i]==1)
			{
				var_neighbor[v][count] = i;
				count++;
			}
		}
		// 在邻居列表的末尾添加 0，作为结束标记
		var_neighbor[v][count]=0;
	}
	// 释放动态分配的数组
	delete[] neighbor_flag; neighbor_flag=NULL;
}

std::set<int> build_critical_vars() {
    std::set<int> criticalVars;
    for (const auto& pr : criticalpairs) {
        criticalVars.insert(pr.first);
        criticalVars.insert(pr.second);
    }
    return criticalVars;
}


void update_noncritical_clauses() {
    noncritical_clauses.clear();
    for (const auto &entry : noncriticalpairs) {
        noncritical_clauses.insert(entry.second);
    }
}


// void build_neighbor_pairs() {
//     neighbor_pairs.clear();
//     criticalPairs.clear();
    
//     // 遍历每个变量 v（变量编号从 1 开始）
//     for (int v = 1; v <= num_vars; v++) {
//         // var_neighbor[v] 是一个以 0 结束的数组，存储变量 v 的所有邻居
//         for (int i = 0; var_neighbor[v][i] != 0; i++) {
//             int u = var_neighbor[v][i];
//             // 只考虑 v < u 以避免重复（保证每个对只记录一次）
//             if (v < u) {
//                 std::pair<int, int> pr = std::make_pair(v, u);
//                 // 如果该对已存在于 neighbor_pairs 中，则将其插入 criticalPairs
//                 if (neighbor_pairs.find(pr) != neighbor_pairs.end()) {
//                     criticalPairs.insert(pr);
//                 } else {
//                     // 否则，将其插入 neighbor_pairs
//                     neighbor_pairs.insert(pr);
//                 }
//             }
//         }
//     }
//     // 利用 std::set_difference 求出非关键对：noncriticalPairs = neighbor_pairs - criticalPairs
//     noncriticalPairs.clear();
//     std::set_difference(neighbor_pairs.begin(), neighbor_pairs.end(),
//                         criticalPairs.begin(), criticalPairs.end(),
//                         std::inserter(noncriticalPairs, noncriticalPairs.begin()));
// }

void build_LCP() {
    LCP.clear();
    // 遍历 global criticalPairs 中的每个 pair
    for (const auto &pr : criticalpairs) {
        int a = pr.first;
        int b = pr.second;
        // 只有 a 和 b 出现在 criticalPairs 中才需要记录
        LCP[a].push_back(pr);
        LCP[b].push_back(pr);
    }
}

void build_LCC_from_criticalPairs() {
    LCC.clear();
    // 遍历每个 critical pair (xi, xj)
    for (const auto &pr : criticalpairs) {
        int xi = pr.first;
        int xj = pr.second;
        
        // 获取变量 xi 出现的所有子句（去重）
        vector<int> clauses_xi;
        for (int k = 0; var_lit[xi][k].clause_num != -1; k++) {
            clauses_xi.push_back(var_lit[xi][k].clause_num);
        }
        sort(clauses_xi.begin(), clauses_xi.end());
        clauses_xi.erase(unique(clauses_xi.begin(), clauses_xi.end()), clauses_xi.end());
        
        // 获取变量 xj 出现的所有子句（去重）
        vector<int> clauses_xj;
        for (int k = 0; var_lit[xj][k].clause_num != -1; k++) {
            clauses_xj.push_back(var_lit[xj][k].clause_num);
        }
        sort(clauses_xj.begin(), clauses_xj.end());
        clauses_xj.erase(unique(clauses_xj.begin(), clauses_xj.end()), clauses_xj.end());
        
        // 计算两个集合的交集，存入 common_clauses
        vector<int> common_clauses;
        set_intersection(clauses_xi.begin(), clauses_xi.end(),
                        clauses_xj.begin(), clauses_xj.end(),
                        back_inserter(common_clauses));
        
        // 构造键，保证 xi < xj
        long long key = ((long long)xi) * MAX_VARS + xj;
        LCC[key] = common_clauses;
    }
}

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

void print_solution()
{
    int    i;

    cout<<"v ";
    for (i=1; i<=num_vars; i++) {
        if(cur_soln[i]==0) cout<<"-";
        cout<<i;
        if(i%10==0) cout<<endl<<"v ";
        else	cout<<' ';
    }
    cout<<"0"<<endl;
}


int verify_sol()
{
	int c,j; 
	int flag;
	
	if(simplify==0)
	{
	
		for (c = 0; c<num_clauses; ++c) 
		{
			flag = 0;
			for(j=0; j<clause_lit_count[c]; ++j)
				if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense) {flag = 1; break;}

			if(flag ==0){//output the clause unsatisfied by the solution
				cout<<"c clause "<<c<<" is not satisfied"<<endl;
			
				cout<<"c ";
				for(j=0; j<clause_lit_count[c]; ++j)
				{
					if(clause_lit[c][j].sense==0)cout<<"-";
					cout<<clause_lit[c][j].var_num<<" ";
				}
				cout<<endl;
			
				for(j=0; j<clause_lit_count[c]; ++j)
					cout<<cur_soln[clause_lit[c][j].var_num]<<" ";
				cout<<endl;

				return 0;
			}
		}
	}
	
	if(simplify==1)
	{
		for (c = 0; c<num_clauses; ++c) 
		{
			flag = 0;
			for(j=0; j<org_clause_lit_count[c]; ++j)
				if (cur_soln[org_clause_lit[c][j].var_num] == org_clause_lit[c][j].sense) {flag = 1; break;}

			if(flag ==0){//output the clause unsatisfied by the solution
				cout<<"c clause "<<c<<" is not satisfied"<<endl;
				
				if(clause_delete[c]==1)cout<<"c this clause is deleted by UP."<<endl;
			
				cout<<"c ";
				for(j=0; j<org_clause_lit_count[c]; ++j)
				{
					if(org_clause_lit[c][j].sense==0)cout<<"-";
					cout<<org_clause_lit[c][j].var_num<<" ";
				}
				cout<<endl;
			
				for(j=0; j<org_clause_lit_count[c]; ++j)
					cout<<cur_soln[org_clause_lit[c][j].var_num]<<" ";
				cout<<endl;

				return 0;
			}
		}
		
	}
	
	return 1;
}

#endif

