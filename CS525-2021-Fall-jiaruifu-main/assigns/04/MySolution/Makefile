######
#
# A simple Makefile
#
######

PATSCC=patscc
PATSOPT=patsopt
MYATSCC=myatscc

######


assign04_sol: \
assign04_sol.dats; \
$(PATSCC) -o assign04_sol -DATS_MEMALLOC_LIBC assign04_sol.dats

######

clean:: ; rm -f *~
clean:: ; rm -f *_dats.c
cleanall:: clean
cleanall:: ; rm -f assign04_sol

############ end of [Makefile] ############