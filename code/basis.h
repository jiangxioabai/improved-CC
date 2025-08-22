#ifndef _BASIS_H_
#define _BASIS_H_
#include "pair_key.h"
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cmath>
#include <algorithm>

using namespace std;

enum type{SAT3, SAT5, SAT7, strSAT} probtype;

/* limits on the size of the problem. */
#define MAX_VARS    4000010
#define MAX_CLAUSES 20000000


// Define a data structure for a literal in the SAT problem.
struct lit {
    int clause_num;		//clause num, begin with 0
    int var_num;		//variable num, begin with 1
    int sense;			//is 1 for true literals, 0 for false literals.
};

/*parameters of the instance*/
int     num_vars;		//var index from 1 to num_vars
int     num_clauses;	//clause index from 0 to num_clauses-1
int		max_clause_len;
int		min_clause_len;
int		formula_len=0;
double	avg_clause_len;
double 	instanceratio;

/* literal arrays */				
lit*	var_lit[MAX_VARS];				//var_lit[i][j] means the j'th literal of var i.
int		var_lit_count[MAX_VARS];        //amount of literals of each var
lit*	clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
int		clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause		

lit*	org_clause_lit[MAX_CLAUSES];		//clause_lit[i][j] means the j'th literal of clause i.
int		org_clause_lit_count[MAX_CLAUSES]; 	// amount of literals in each clause
int		simplify=0;
			
/* Information about the variables. */
int     score[MAX_VARS];				
int		time_stamp[MAX_VARS];
int		conf_change[MAX_VARS];
int*	var_neighbor[MAX_VARS];
int		var_neighbor_count[MAX_VARS];
//int		pscore[MAX_VARS];
int		fix[MAX_VARS];


/* Information about the clauses */			
int     clause_weight[MAX_CLAUSES];		
int     sat_count[MAX_CLAUSES];			
int		sat_var[MAX_CLAUSES];
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

/* Information about solution */
int             cur_soln[MAX_VARS];	//the current solution, with 1's for True variables, and 0's for False variables

//cutoff
int		max_tries = 10000;
int		tries;
int		max_flips = 2000000000;
int		step;

// 关于LCQ/LCR数据结构
std::vector<int16_t>            PD;
std::vector<std::vector<int>>   LCC_vec;
std::vector<std::vector<uint32_t>> LCP_vec;   // var → list<cid>
std::unordered_set<PairKey> criticalDir;
std::unordered_map<PairKey,uint32_t> dir_key2cid;
std::vector<std::pair<int,int>> crit_pairs;
std::vector<PairKey>              dir_keys;
// 非-critical 且只出现一次的有向 pair → 唯一子句 cid+1
static std::unordered_map<PairKey,uint32_t> uniq_pair_clause;

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

void build_critical_index(int num_vars)
{
    const uint32_t K = (uint32_t)crit_pairs.size();   // 有向条目数

    PD.assign(K, 0);
    LCC_vec.assign(K, {});
    LCP_vec.assign(num_vars+1, {});

    for (uint32_t cid = 0; cid < K; ++cid)
    {
        int xi = crit_pairs[cid].first;   // 有向：xi→xj
        int xj = crit_pairs[cid].second;
        LCP_vec[xi].push_back(cid);
        LCP_vec[xj].push_back(cid);
        PairKey k = pair_key_directed(crit_pairs[cid].first,
                                  crit_pairs[cid].second);
        dir_key2cid[k] = cid;        // 有向 key → cid
    }
    // 在 build_critical_index() 结束时（或紧跟着 dir_keys.assign(...) 之后）

    uint32_t N = 0;
    while ((1u << N) < K) ++N;          // 求最小 N 使得 2^N ≥ K
    const uint32_t M = 1u << N;         // M 真正数组长度（2 的幂）

    static uint32_t MASK = M - 1;       // 全局 / static 方便别处直接用
    cid_of_key.assign(M, UINT32_MAX);          // 先全部填无效值

    for (uint32_t cid = 0; cid < K; ++cid)
    {
        PairKey key = dir_keys[cid];           // 64-bit：hi‖lo
        uint32_t idx = uint32_t(key) & MASK;   // 低 N 位映射到 0 … M-1
        cid_of_key[idx] = cid;
    }
}
void build_LCC_from_criticalPairs()
{
    for(auto& v : LCC_vec) v.clear();       // 长度 = K

    for(uint32_t cid = 0; cid < crit_pairs.size(); ++cid){
        int xi = crit_pairs[cid].first;
        int xj = crit_pairs[cid].second;

        /* 收集 xi、xj 出现的子句编号（去重）——与原代码相同 */
        std::vector<int> c_xi, c_xj;
        for(int k=0; var_lit[xi][k].clause_num!=-1; ++k)
            c_xi.push_back(var_lit[xi][k].clause_num);
        for(int k=0; var_lit[xj][k].clause_num!=-1; ++k)
            c_xj.push_back(var_lit[xj][k].clause_num);

        std::sort(c_xi.begin(),c_xi.end());
        c_xi.erase(std::unique(c_xi.begin(),c_xi.end()),c_xi.end());
        std::sort(c_xj.begin(),c_xj.end());
        c_xj.erase(std::unique(c_xj.begin(),c_xj.end()),c_xj.end());

        std::set_intersection(c_xi.begin(),c_xi.end(),
                              c_xj.begin(),c_xj.end(),
                              std::back_inserter(LCC_vec[cid]));
    }
}


int temp_lit[MAX_VARS]; // the max length of a clause can be MAX_VARS

void build_critical_pairs()
{
    criticalDir.clear();
    uniq_pair_clause.clear();          // ☆ 新增
    std::unordered_map<PairKey,int> firstSeen;   // canonical key → 1st-clause id

    for (int c = 1; c <= num_clauses; ++c) {

        /* 取子句的去重变量列表 ------------------------------------------------ */
        std::vector<int> lits;
        lits.reserve(clause_lit_count[c]);
        for (int j = 0; j < clause_lit_count[c]; ++j)
            lits.push_back(std::abs(clause_lit[c][j].var_num));

        std::sort(lits.begin(), lits.end());
        lits.erase(std::unique(lits.begin(),lits.end()), lits.end());

        /* 枚举无向对 ---------------------------------------------------------- */
        const int L = (int)lits.size();
        for (int i = 0; i < L; ++i)
            for (int j = i+1; j < L; ++j) {
                int a = lits[i], b = lits[j];           // a<b
                PairKey kCanon = pair_key_directed(a,b);

                auto it = firstSeen.find(kCanon);
                if (it == firstSeen.end()) {            // 第一次见
                    firstSeen[kCanon] = c;
                    continue;
                }
                if (it->second == c)                    // 同一子句再次出现
                    continue;

                /* 第二次出现在不同子句 → 升格 critical (两个方向) ---------- */
                criticalDir.insert(pair_key_directed(a,b));  // a→b
                criticalDir.insert(pair_key_directed(b,a));  // b→a
            }
    }

    /* ③ 把“仍停留在 firstSeen 中、且不在 criticalDir 中”的 pair 认定为唯一 */
    for (auto &[kCanon, cid] : firstSeen) {
        if (criticalDir.count(kCanon)) continue;          // 已经升格 critical
        int a = key_hi(kCanon), b = key_lo(kCanon);       // 拆成 a<b
        uint32_t v = cid;                                 // cid≥1
        uniq_pair_clause[pair_key_directed(a,b)] = v;     // a→b
        uniq_pair_clause[pair_key_directed(b,a)] = v;     // b→a
    }

    /* ----------   把集合拍成顺序表 / 可读表 / 映射表   -------------------- */
    dir_keys.assign(criticalDir.begin(), criticalDir.end());   // 顺序可任意

    crit_pairs.clear();
    crit_pairs.reserve(dir_keys.size());
    dir_key2cid.clear();

    for (uint32_t cid = 0; cid < dir_keys.size(); ++cid) {
        PairKey k = dir_keys[cid];
        dir_key2cid[k] = cid;                               // 有向 key → cid
        crit_pairs.emplace_back(key_hi(k), key_lo(k));      // (xi,xj)
    }
}

/*
 * Read in the problem.
 */

int build_instance(char *filename)
{
	char    line[1000000];
	char    tempstr1[10];
	char    tempstr2[10];
	int     cur_lit;
	int     i,j;
	int		v,c;//var, clause
	
	ifstream infile(filename);
	if(!infile)
		return 0;

	/*** build problem data structures of the instance ***/
	infile.getline(line,1000000);
	while (line[0] != 'p')
		infile.getline(line,1000000);

	sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);
	instanceratio = double(num_clauses)/num_vars;
	
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
    // build_critical_pairs(); // 构建 critical pairs

	// build_critical_index(num_vars);
	return 1;
}


void build_neighbor_relation()
{
	int*	neighbor_flag = new int[num_vars+1];
	int		i,j,count;
	int 	v,c;

	for(v=1; v<=num_vars; ++v)
	{
		var_neighbor_count[v] = 0;
		
		if(fix[v]==1) continue;

		for(i=1; i<=num_vars; ++i)
			neighbor_flag[i] = 0;
		neighbor_flag[v] = 1;
		
		for(i=0; i<var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			if(clause_delete[c]==1) continue;
			
			for(j=0; j<clause_lit_count[c]; ++j)
			{
				if(neighbor_flag[clause_lit[c][j].var_num]==0)
				{
					var_neighbor_count[v]++;
					neighbor_flag[clause_lit[c][j].var_num] = 1;
				}
			}
		}

		neighbor_flag[v] = 0;
 
		var_neighbor[v] = new int[var_neighbor_count[v]+1];

		count = 0;
		for(i=1; i<=num_vars; ++i)
		{
			if(fix[i]==1) continue;
			
			if(neighbor_flag[i]==1)
			{
				var_neighbor[v][count] = i;
				count++;
			}
		}
		var_neighbor[v][count]=0;
	}
	
	delete[] neighbor_flag; neighbor_flag=NULL;
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

