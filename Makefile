CFLAGS = -Wall -Wextra -O3 -g -fopenmp -std=c99 -march=native

# CFLAGS+= -Og
# CFLAGS+= -fsanitize=address -O0
# LDLIBS+= -lasan

all: boomerang6

clean:
	rm -f boomerang6 *.o

.phony: all
