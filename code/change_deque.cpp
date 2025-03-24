#include <iostream>
#include <unordered_map>
#include <deque>
#include <vector>

// 定义变量类型，假设变量用整数表示
using Variable = int;

// 定义变化事件的类型，可以是一个结构体或者简单的整数表示
struct ChangeEvent {
    Variable variable; // 变化的变量
    bool new_value;    // 变化后的新值
    int timestamp;     // 变化发生的时间戳
};

// 定义一个数据结构来记录每个变量及其邻居的最近两次变化
class ChangeQueue {
private:
    // 使用unordered_map来存储每个变量的最近两次变化
    // key: 变量，value: 最近两次变化的deque
    std::unordered_map<Variable, std::deque<ChangeEvent>> change_history;

public:
    // 添加一个变化事件
    void addChangeEvent(Variable var, bool new_value, int timestamp) {
        ChangeEvent event{var, new_value, timestamp};

        // 如果该变量的历史记录已存在，添加新事件
        if (change_history.find(var) != change_history.end()) {
            auto& history = change_history[var];
            // 如果历史记录已经有两事件，则移除最早的一个
            if (history.size() == 2) {
                history.pop_front();
            }
            history.push_back(event);
        } else {
            // 否则，创建新的历史记录
            change_history[var] = std::deque<ChangeEvent>{event};
        }
    }

    // 获取某个变量的最近两次变化事件
    std::deque<ChangeEvent> getRecentChanges(Variable var) {
        if (change_history.find(var) != change_history.end()) {
            return change_history[var];
        } else {
            return std::deque<ChangeEvent>{};
        }
    }

    // 打印某个变量的最近两次变化事件
    void printRecentChanges(Variable var) {
        auto changes = getRecentChanges(var);
        std::cout << "Recent changes for variable " << var << ":\n";
        for (const auto& event : changes) {
            std::cout << "Variable " << event.variable << " changed to " 
                      << event.new_value << " at timestamp " << event.timestamp << "\n";
        }
    }
};

int main() {
    ChangeQueue cq;

    // 添加一些变化事件
    cq.addChangeEvent(1, true, 1);
    cq.addChangeEvent(2, false, 2);
    cq.addChangeEvent(1, false, 3);
    cq.addChangeEvent(3, true, 4);

    // 打印变量1的最近两次变化事件
    cq.printRecentChanges(1);

    return 0;
}
