CC ?= gcc
CFLAGS ?= -O2
skyglass: skyglass.c stb_truetype.h
	$(CC) $(CFLAGS) -o skyglass skyglass.c -lX11 -lXext -lm
install: skyglass
	install -Dm755 skyglass $(HOME)/.local/bin/skyglass
clean:
	rm -f skyglass
