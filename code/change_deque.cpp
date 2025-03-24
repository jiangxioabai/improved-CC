#include <iostream>
#include <unordered_map>
#include <deque>
#include <vector>
#include <unordered_set>
using namespace std;

// 定义变量类型，假设变量用整数表示
using Variable = int;

// 定义变化事件的类型
struct ChangeEvent {
    Variable variable; // 记录哪个变量发生变化
    bool new_value;    // 变化后的新值
    int timestamp;     // 变化发生的时间戳
};

// 定义一个数据结构来记录每个变量的最近两次变化
class ChangeQueue {
private:
    // 使用 unordered_map 存储每个变量的最近两次变化
    unordered_map<Variable, deque<ChangeEvent>> change_history;
public:
    // 添加一个变化事件
    void addChangeEvent(Variable var, bool new_value, int timestamp) {
        ChangeEvent event{var, new_value, timestamp};
        if (change_history.find(var) != change_history.end()) {
            auto& history = change_history[var];
            // 如果历史记录已经有两条，则移除最早的一条
            if (history.size() == 2) {
                history.pop_front();
            }
            history.push_back(event);
        } else {
            change_history[var] = deque<ChangeEvent>{event};
        }
    }
    
    // 获取某个变量的最近两次变化事件
    deque<ChangeEvent> getRecentChanges(Variable var) {
        if (change_history.find(var) != change_history.end()) {
            return change_history[var];
        } else {
            return deque<ChangeEvent>{};
        }
    }
    
    // 打印某个变量的最近两次变化事件
    void printRecentChanges(Variable var) {
        auto changes = getRecentChanges(var);
        cout << "Recent changes for variable " << var << ":\n";
        for (const auto& event : changes) {
            cout << "Variable " << event.variable << " changed to " 
                 << event.new_value << " at timestamp " << event.timestamp << "\n";
        }
    }
};
