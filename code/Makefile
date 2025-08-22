# =====================  编译器通用设置  ======================
CXX        = g++
STD_WARN   = -std=c++17 -Wall -Wextra
COMMON     = $(STD_WARN) -fno-omit-frame-pointer

# ---------------------- 各模式追加选项 -----------------------
DEBUG_FLAGS   = -g -O0 -fsanitize=address -DENABLE_PAIR_ASSERT
PERF_FLAGS    = -O2 -g -DNDEBUG -march=native -fno-omit-frame-pointer \
            -fno-inline -fno-inline-functions -fno-default-inline                   # 行号 + 无 LTO
RELEASE_FLAGS = -O3 -DNDEBUG -march=native -flto               # 最高优化

# -------- 选择编译模式（默认 release，先 strip 空白）--------
CR    := $(shell printf '\r')
MODE ?= release
MODE  := $(subst $(CR),,$(MODE))
MODE  := $(strip $(MODE))


ifeq ($(MODE),debug)
  CXXFLAGS = $(COMMON) $(DEBUG_FLAGS)
else ifeq ($(MODE),perf)
  CXXFLAGS = $(COMMON) $(PERF_FLAGS)
else ifeq ($(MODE),release)
  CXXFLAGS = $(COMMON) $(RELEASE_FLAGS)
else
  $(error Unknown MODE: $(MODE))
endif

# =======================  文件定义  ==========================
SRCS   = cca.cpp
OBJS   = $(SRCS:.cpp=.o)
TARGET = CCAnr

# =======================  规则区  ============================
all: $(TARGET)

$(TARGET): $(OBJS)
	$(CXX) $(CXXFLAGS) -o $@ $^

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

clean:
	$(RM) $(TARGET) $(OBJS)

rebuild: clean all

.PHONY: all clean rebuild



