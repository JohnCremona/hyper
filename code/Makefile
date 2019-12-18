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
