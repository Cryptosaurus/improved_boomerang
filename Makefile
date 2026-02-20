CFLAGS = -Wall -Wextra -O3 -g -std=c99 -march=native -fopenmp

# CFLAGS+= -fsanitize=address -O0
# LDLIBS+= -lasan

all: boomerang6

clean:
	rm -f boomerang6 *.o

.phony: all
