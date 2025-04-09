#include "basis.h"
#include "cca.h"
#include "cw.h"
#include "preprocessor.h"

#include <sys/times.h> //these two h files are for linux
#include <unistd.h>

// 全局变量，初始设为 0
int key_flip = 0;





// 子句编号从0开始，变量编号从1开始
// var_neighbor[i][j]表示变量i的第j个邻居下标；如果是0，则表示数组末尾
int pick_var_1()
{
	int         i,k,c,v;
	int         best_var;
	lit*		clause_c;
	
	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(goodvar_stack_fill_pointer>0) // 如果存在1-step q-flippable变量，goodvar_stack存的1-step q-flippable变量
	{
		best_var = goodvar_stack[0];// 选择第一个变量作为候选
		// 遍历所有1-step q-flippable变量，选分数最高的变量，相同则选上次翻转最早的变量，这里time_stamp[]初始化应该是0，表示上次反转时间
		for(i=1; i<goodvar_stack_fill_pointer; ++i)
		{
			v=goodvar_stack[i];
			if(score[v]>score[best_var]) best_var = v;
			else if(score[v]==score[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
		}
		
		return best_var;
	}
	

	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<unsatvar_stack_fill_pointer; ++i)// 遍历所有不满足子句中的变量
	{
		if(score[unsatvar_stack[i]]>sigscore) 
		{
			best_var = unsatvar_stack[i];// 先找到一个满足大于sigscore的变量
			break;
		}
	}
	// 继续遍历不满足子句中的变量找到分数最大的变量，相同则选择最早翻转的变量（和上面相同）
	for(++i; i<unsatvar_stack_fill_pointer; ++i)
	{
		v=unsatvar_stack[i];
		if(score[v]>score[best_var]) best_var = v;
		else if(score[v]==score[best_var] && time_stamp[v]<time_stamp[best_var]) best_var = v;
	}

	// 2step_q-flippable变量

	// 先遍历critical ，再遍历noncritical，判断是否是qualified_pairs，再判断是否是valuable
	pair<int,int> pairs;
	int maxscore = 0;
	for(auto iter = criticalpairs.begin(); iter != criticalpairs.end(); ++iter){
		pairs = *iter;
		// 判断是qualified后，需要分别判断（xi，xj）和（xj，xi）是valuable
		if(is_qualified_pairs(pairs)){
			Result result1, result2;
			result1 = is_valuable_for_critical(pairs.first,pairs.second);
			result2 = is_valuable_for_critical(pairs.second,pairs.first);
			// 判断是（xi，xj）或（xj，xi）是valuable
			if(result1.re || result2.re){
				// 两个都是，则比较分数满足后取更久没更新的
				if(result1.re && result2.re){
					if(result1.value > maxscore){
						maxscore = result1.value;
						best_var = (time_stamp[pairs.first]<time_stamp[pairs.second]) ? pairs.first:pairs.second;
					}
				}
				// 其中一个是，则只比较是的那个的分数
				else{
					if(result1.re){
						if(result1.value > maxscore){
							maxscore = result1.value;
							best_var = pairs.first;
						}
					}
					else{
						if(result2.value > maxscore){
							maxscore = result2.value;
							best_var = pairs.second;
						}
					}
				}
			}
		}
	}
	for(auto iter = noncriticalpairs.begin(); iter != noncriticalpairs.end(); ++iter){
		pairs = (*iter).first;
		// 判断是qualified后，需要分别判断（xi，xj）和（xj，xi）是valuable
		if(is_qualified_pairs(pairs)){
			Result result1, result2;
			result1 = is_valuable_for_noncritical(pairs.first,pairs.second);
			result2 = is_valuable_for_noncritical(pairs.second,pairs.first);
			// 判断是（xi，xj）或（xj，xi）是valuable
			if(result1.re || result2.re){
				// 两个都是，则比较分数满足后取更久没更新的
				if(result1.re && result2.re){
					if(result1.value > maxscore){
						maxscore = result1.value;
						best_var = (time_stamp[pairs.first]<time_stamp[pairs.second]) ? pairs.first:pairs.second;
					}
				}
				// 其中一个是，则只比较是的那个的分数
				else{
					if(result1.re){
						if(result1.value > maxscore){
							maxscore = result1.value;
							best_var = pairs.first;
						}
					}
					else{
						if(result2.value > maxscore){
							maxscore = result2.value;
							best_var = pairs.second;
						}
					}
				}
			}
		}
	}
	if(best_var!=0) return best_var;

	// reversible变量
	for(auto iter = criticalpairs.begin(); iter != criticalpairs.end(); ++iter){
		pairs = *iter;
		// 判断是unqualified后，需要分别判断（xi，xj）和（xj，xi）是valuable
		Result result1, result2;
		result1 = is_valuable_for_critical(pairs.first,pairs.second);
		result2 = is_valuable_for_critical(pairs.second,pairs.first);
		// 判断是（xi，xj）或（xj，xi）是valuable
		if(result1.re || result2.re){
			// 两个都是，则比较分数满足后取更久没更新的
			if(result1.re && result2.re){
				if(result1.value > maxscore){
					maxscore = result1.value;
					best_var = (time_stamp[pairs.first]<time_stamp[pairs.second]) ? pairs.first:pairs.second;
				}
			}
			// 其中一个是，则只比较是的那个的分数
			else{
				if(result1.re){
					if(result1.value > maxscore){
						maxscore = result1.value;
						best_var = pairs.first;
					}
				}
				else{
					if(result2.value > maxscore){
						maxscore = result2.value;
						best_var = pairs.second;
					}
				}
			}
		}
	}
	for(auto iter = noncriticalpairs.begin(); iter != noncriticalpairs.end(); ++iter){
		pairs = (*iter).first;
		// 判断是qualified后，需要分别判断（xi，xj）和（xj，xi）是valuable
		Result result1, result2;
		result1 = is_valuable_for_noncritical(pairs.first,pairs.second);
		result2 = is_valuable_for_noncritical(pairs.second,pairs.first);
		// 判断是（xi，xj）或（xj，xi）是valuable
		if(result1.re || result2.re){
			// 两个都是，则比较分数满足后取更久没更新的
			if(result1.re && result2.re){
				if(result1.value > maxscore){
					maxscore = result1.value;
					best_var = (time_stamp[pairs.first]<time_stamp[pairs.second]) ? pairs.first:pairs.second;
				}
			}
			// 其中一个是，则只比较是的那个的分数
			else{
				if(result1.re){
					if(result1.value > maxscore){
						maxscore = result1.value;
						best_var = pairs.first;
					}
				}
				else{
					if(result2.value > maxscore){
						maxscore = result2.value;
						best_var = pairs.second;
					}
				}
			}
		}
	}
	if(best_var!=0) return best_var;

    key_flip = 1;
    // reversible 变量

    key_flip = 1;
	// 如果既没有 q-flippable变量，也没有reversible变量，则更新子句权重，并随机游走
	/**Diversification Mode**/

	update_clause_weights();
	
	/*focused random walk*/

	c = unsat_stack[rand()%unsat_stack_fill_pointer];//随机选择一个不满足子句
	clause_c = clause_lit[c];
	best_var = clause_c[0].var_num;//将子句中的第一个变量作为候选
	// 同样倾向于选择该随机子句中分数最高的变量，相同则选上次翻转最早的变量
	for(k=1; k<clause_lit_count[c]; ++k)
	{
		v=clause_c[k].var_num;
		if(time_stamp[v]<time_stamp[best_var]) best_var = v;
		// if(score[v]>score[best_var]) best_var = v;
		// else if(score[v]==score[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;
	}
	
	return best_var;
}





//set functions in the algorithm 设置子句权重
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

		flipvar = pick_var_1();

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

	if (build_instance(argv[1])==0)// 构建实例
	{    

		cout<<"Invalid filename: "<< argv[1]<<endl;
		return -1;
	}

    sscanf(argv[2],"%d",&seed);
    
    srand(seed);
    
    if(unitclause_queue_end_pointer>0) preprocess();// 进行预处理，消掉单变量子句
    
    build_neighbor_relation();// 构建变量邻居关系
    
	cout<<"c Instance: Number of variables = "<<num_vars<<endl;
	cout<<"c Instance: Number of clauses = "<<num_clauses<<endl;
	cout<<"c Instance: Ratio = "<<ratio<<endl;
	cout<<"c Instance: Formula length = "<<formula_len<<endl;
	cout<<"c Instance: Avg (Min,Max) clause length = "<<avg_clause_len<<" ("<<min_clause_len<<","<<max_clause_len<<")"<<endl;
	cout<<"c Algorithmic: Random seed = "<<seed<<endl;
    //多次局部搜索
	for (tries = 0; tries <= max_tries; tries++)
	{
		 settings(); //初始化设置子句权重
		 
		 init();  //初始化
	 
		 local_search(max_flips);//局部搜索

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
	 
    free_memory();

    return 0;
}
