CC := g++
CFLAGS := -g -std=c++11
TARGET := solcCheck
SRCS := $(wildcard *.cpp)
OBJS := $(patsubst %cpp,%o,$(SRCS))
all:$(TARGET)
%.o:%.cpp
	$(CC) $(CFLAGS) -c -I ./ -I /usr/include $<
$(TARGET):$(OBJS)
	$(CC) $(CFLAGS) -o $@ $^ -lz3 -lpthread
clean:
	rm -rf $(TARGET) *.o
