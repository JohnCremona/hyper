ECLIB_BASE=$(HOME)/eclib
INCDIR = $(ECLIB_BASE)/include
LIBDIR = $(ECLIB_BASE)/lib

CFLAGS = -std=gnu++11 -O4 -I$(INCDIR)
LFLAGS =  -lm -lstdc++ -lpari -lec -lntl -L$(LIBDIR) -Wl,-rpath -Wl,$(LIBDIR)

sextic: sextic.cc
	gcc $(CFLAGS) sextic.cc -o sextic -g -lm -lstdc++ -lpari

sextic2: sextic2.cc
	gcc $(CFLAGS) sextic2.cc -o sextic2 -g -lm -lstdc++ -lpari

xdeg4: xhyper.cc
	gcc $(CFLAGS) xhyper.cc -o xdeg4 -g $(LFLAGS)

hdeg4: hhyper.cc
	gcc $(CFLAGS) -DDEGREE=4 hhyper.cc -o hdeg4 -g -lm -lstdc++ -lpari

xdeg6: xhyper.cc
	gcc $(CFLAGS) -DDEGREE=6 xhyper.cc -o xdeg6 -g -lm -lstdc++ -lpari

xdeg8: xhyper.cc
	gcc $(CFLAGS) -DDEGREE=8 xhyper.cc -o xdeg8 -g -lm -lstdc++ -lpari

xdeg10: xhyper.cc
	gcc $(CFLAGS) -DDEGREE=10 xhyper.cc -o xdeg10 -g -lm -lstdc++ -lpari

negdef: negdef.cc
	gcc $(CFLAGS) negdef.cc -o negdef -g -lm -lstdc++ -lpari

minpoints3: minpoints3.c
	gcc -O3 -funroll-loops -fopenmp minpoints3.c -lm -o minpoints3

minpoints3odd: minpoints3odd.c
	gcc -O3 -funroll-loops -fopenmp minpoints3odd.c -lm -o minpoints3odd

minpoints4: minpoints4.c
	gcc -O3 -funroll-loops -fopenmp minpoints4.c -lm -o minpoints4

mgamma.o: mgamma.h mgamma.c
	gcc -O3 -c mgamma.c -o mgamma.o

gamma3: gamma3.c
	gcc -O3 -funroll-loops -fopenmp gamma3.c -lm -o gamma3

gamma3mod3: gamma3mod3.c
	gcc -O3 -funroll-loops -fopenmp gamma3mod3.c -lm -o gamma3mod3

gamma4: gamma4.c
	gcc -O3 -funroll-loops -fopenmp gamma4.c -lm -o gamma4

gamma5: gamma5.c
	gcc -O3 -funroll-loops -fopenmp gamma5.c -lm -o gamma5

gamma5mod5: gamma5mod5.c
	gcc -O3 -funroll-loops -fopenmp gamma5mod5.c -lm -o gamma5mod5

gamma6: gamma6.c
	gcc -O3 -funroll-loops -fopenmp gamma6.c -lm -o gamma6

gamma6mod3: gamma6mod3.c
	gcc -O3 -funroll-loops -fopenmp gamma6mod3.c -lm -o gamma6mod3

gamma7: gamma7.c
	gcc -O3 -funroll-loops -fopenmp gamma7.c -lm -o gamma7

gamma7mod7: gamma7mod7.c
	gcc -O3 -funroll-loops -fopenmp gamma7mod7.c -lm -o gamma7mod7

gamma8: gamma8.c
	gcc -O3 -funroll-loops -fopenmp gamma8.c -lm -o gamma8

mgamma8: mgamma8.c mgamma.o
	gcc -O3 -funroll-loops -fopenmp mgamma8.c mgamma.o -lm -o mgamma8

gamma9: gamma9.c
	gcc -O3 -funroll-loops -fopenmp gamma9.c -lm -o gamma9

gamma9mod3: gamma9mod3.c
	gcc -O3 -funroll-loops -fopenmp gamma9mod3.c -lm -o gamma9mod3

gamma10: gamma10.c
	gcc -O3 -funroll-loops -fopenmp gamma10.c -lm -o gamma10

gamma10mod5: gamma10mod5.c
	gcc -O3 -funroll-loops -fopenmp gamma10mod5.c -lm -o gamma10mod5

gamma11: gamma11.c
	gcc -O3 -funroll-loops -fopenmp gamma11.c -lm -o gamma11

gamma12: gamma12.c
	gcc -O3 -funroll-loops -fopenmp gamma12.c -lm -o gamma12

gamma12mod3: gamma12mod3.c
	gcc -O3 -funroll-loops -fopenmp gamma12mod3.c -lm -o gamma12mod3

gamma13: gamma13.c
	gcc -O3 -funroll-loops -fopenmp gamma13.c -lm -o gamma13

gamma14: gamma14.c
	gcc -O3 -funroll-loops -fopenmp gamma14.c -lm -o gamma14

gamma14mod7: gamma14mod7.c
	gcc -O3 -funroll-loops -fopenmp gamma14mod7.c -lm -o gamma14mod7

gammas: gamma3 gamma4 gamma5 gamma6 gamma7 gamma8 gamma9 gamma10 gamma11 gamma12 gamma13 gamma14 gamma3mod3 gamma5mod5 gamma6mod3 gamma7mod7 gamma9mod3 gamma10mod5 gamma12mod3 gamma14mod7
