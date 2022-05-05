INSTBIN=cm
OBJ= \
	gen.o \
	genc.o \
	main.o

DEPS=../parse/libparse.a ../mi/libmi.a ../util/libutil.a

include ../config.mk
include ../mk/c.mk

.PHONY: test
test:
	./cm -o out tests/hello.myr
	clang-format -i out.c
	gcc -std=gnu11 -fno-stack-protector -c -o out.o out.c
	gcc -std=gnu11 -static -nostdlib -nostartfiles -Wall -Wextra -o out.elf out.o ../out/lib/myr/_myrrt.o
	#gcc -std=gnu11 -static -Wall -Wextra -o out.elf out.o
	./out.elf || echo "exit($$?)"

gdb:
	gdb --args ./cm -o out tests/hello.myr
