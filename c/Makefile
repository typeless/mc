INSTBIN=cm
OBJ= \
	../6/typeinfo.o \
	../6/blob.o \
	gen.o \
	genc.o \
	main.o

DEPS=../parse/libparse.a ../mi/libmi.a ../util/libutil.a

include ../config.mk
include ../mk/c.mk

.PHONY: test
test:
	MYR_MC=./cm mbld -I../obj/lib/sys -o obj -b hello tests/hello.myr 2>&1 | tee hello.txt

gdb:
	gdb --args ./cm -o out tests/hello.myr


	#./cm -O obj tests/hello.myr
	#clang-format -i out.c
	#gcc -std=gnu11 -fno-stack-protector -c -o out.o out.c
	#gcc -std=gnu11 -static -nostdlib -nostartfiles -Wall -Wextra -o out.elf out.o ../out/lib/myr/_myrrt.o -L../out/lib/myr -lstd -lsys
	#gcc -std=gnu11 -static -Wall -Wextra -o out.elf out.o
	#./out.elf || echo "exit($$?)"

