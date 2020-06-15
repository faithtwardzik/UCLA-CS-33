HANDINDIR = /u/cs/class/cs33/cs33t10/threadlab/handin

CC = gcc
CFLAGS = -w -pthread -std=gnu99 -O3

thread: thread.c thread.h util.c 
	$(CC) $(CFLAGS) -o thread thread.c util.c 
 
handin:
	@USER=whoami
	cp thread.c $(HANDINDIR)/$(USER)-thread.c

clean:
	rm -f *~ thread
