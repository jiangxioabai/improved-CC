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
using namespace std;

enum type{SAT3, SAT5, SAT7, strSAT} probtype;

/* limits on the size of the problem. */
#define MAX_VARS    4000010
#define MAX_CLAUSES 20000000

// 关于critical的数据定义 
// 用于标记每个子句是否为 critical
bool isCriticalClause[MAX_CLAUSES];

// 用于标记每个变量是否出现在某个 critical pair 中
bool isCriticalVar[MAX_VARS];

// Global集合：criticalPairs 存放所有 critical pair（变量对，满足 i < j），noncriticalPairs 存放所有非关键变量对
#include <vector>
#include <utility>
using namespace std;
vector< pair<int, int> > criticalPairs;
vector< pair<int, int> > noncriticalPairs;

// 为每个 critical 变量，记录包含它的 critical pair 列表：LCP(X_i)
vector< pair<int, int> > LCP[MAX_VARS];

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
int orig_score[MAX_VARS]; //score without weight
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


// 我们将所有变量对都记录到 allPairs 中
// 每个 pair 记录的是 (i, j) 且保证 i < j
#include <vector>
#include <unordered_map>
#include <algorithm>
#include <utility>
using namespace std;

void init_critical_pairs() {
    // 清空全局集合
    criticalPairs.clear();
    noncriticalPairs.clear();
    LCC.clear();
    // 对于 LCP，每个变量的 vector 也清空
    for (int v = 0; v < MAX_VARS; v++) {
        LCP[v].clear();
    }

    // 使用 unordered_map 统计每个变量对出现的次数
    // 键的构造： key = (long long) i * MAX_VARS + j，保证 i < j
    unordered_map<long long, int> pairCount;

    // 第一遍遍历：统计所有子句中所有变量对出现的次数
    for (int c = 0; c < num_clauses; c++) {
        vector<int> vars;
        // 提取子句 c 中所有变量（遇到 var_num==0 结束）
        for (int j = 0; j < clause_lit_count[c]; j++) {
            int var = clause_lit[c][j].var_num;
            if (var == 0) break;
            vars.push_back(var);
        }
        if (vars.empty()) continue;
        sort(vars.begin(), vars.end());
        // 枚举当前子句中所有变量对 (i, j)（i < j）
        for (size_t i = 0; i < vars.size(); i++) {
            for (size_t j = i + 1; j < vars.size(); j++) {
                int vi = vars[i], vj = vars[j];
                long long key = ((long long) vi) * MAX_VARS + vj;
                pairCount[key]++;
            }
        }
    }

    // 初始化所有子句和变量的标记为 false
    for (int c = 0; c < num_clauses; c++) {
        isCriticalClause[c] = false;
    }
    for (int v = 0; v < MAX_VARS; v++) {
        isCriticalVar[v] = false;
    }

    // 第二遍遍历：对每个子句，枚举其所有变量对，并根据 pairCount 分为 critical 和 noncritical
    for (int c = 0; c < num_clauses; c++) {
        vector<int> vars;
        for (int j = 0; j < clause_lit_count[c]; j++) {
            int var = clause_lit[c][j].var_num;
            if (var == 0) break;
            vars.push_back(var);
        }
        if (vars.empty()) continue;
        sort(vars.begin(), vars.end());
        // 局部 vector 用于保存当前子句中 critical pair
        vector< pair<int, int> > localCritical;
        // 局部 vector 用于保存当前子句中 noncritical pair
        vector< pair<int, int> > localNoncritical;
        for (size_t i = 0; i < vars.size(); i++) {
            for (size_t j = i + 1; j < vars.size(); j++) {
                int vi = vars[i], vj = vars[j];
                long long key = ((long long) vi) * MAX_VARS + vj;
                if (pairCount[key] > 1) {
                    localCritical.push_back(make_pair(vi, vj));
                    // 同时，更新 LCC：记录当前子句 c 属于此 critical pair
                    LCC[key].push_back(c);
                } else {
                    localNoncritical.push_back(make_pair(vi, vj));
                }
            }
        }
        // 如果当前子句中至少有一个 critical pair，则标记该子句为 critical，
        // 并将局部 critical pair 添加到 global criticalPairs，同时标记相关变量
        if (!localCritical.empty()) {
            isCriticalClause[c] = true;
            for (size_t k = 0; k < localCritical.size(); k++) {
                criticalPairs.push_back(localCritical[k]);
                isCriticalVar[ localCritical[k].first ] = true;
                isCriticalVar[ localCritical[k].second ] = true;
            }
        }
        // 将当前子句中所有 noncritical pair 添加到 global noncriticalPairs
        for (size_t k = 0; k < localNoncritical.size(); k++) {
            noncriticalPairs.push_back(localNoncritical[k]);
        }
    }

    // 对 global criticalPairs 进行排序和去重
    sort(criticalPairs.begin(), criticalPairs.end());
    criticalPairs.erase(unique(criticalPairs.begin(), criticalPairs.end()), criticalPairs.end());
    
    // 同理，对 global noncriticalPairs 进行排序和去重
    sort(noncriticalPairs.begin(), noncriticalPairs.end());
    noncriticalPairs.erase(unique(noncriticalPairs.begin(), noncriticalPairs.end()), noncriticalPairs.end());

    // 根据 global criticalPairs 构建每个 critical 变量的 LCP
    // 对于每个 critical pair (vi, vj) 在 criticalPairs 中，分别加入 LCP[vi] 和 LCP[vj]
    for (size_t k = 0; k < criticalPairs.size(); k++) {
        int vi = criticalPairs[k].first;
        int vj = criticalPairs[k].second;
        LCP[vi].push_back(criticalPairs[k]);
        LCP[vj].push_back(criticalPairs[k]);
    }
    
    // 可选：对每个 LCP[v] 进行排序和去重
    for (int v = 0; v < MAX_VARS; v++) {
        if (!LCP[v].empty()) {
            sort(LCP[v].begin(), LCP[v].end());
            LCP[v].erase(unique(LCP[v].begin(), LCP[v].end()), LCP[v].end());
        }
    }
}



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

