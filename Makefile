CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra

bin/tvim: tvim.c
	@mkdir -p bin
	$(CC) $(CFLAGS) -o $@ tvim.c

clean:
	rm -rf bin

.PHONY: clean
