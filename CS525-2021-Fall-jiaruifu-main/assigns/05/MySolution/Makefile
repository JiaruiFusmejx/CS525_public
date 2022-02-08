######
#
# A simple Makefile
#
######

PATSCC=patscc
PATSOPT=patsopt
MYATSCC=myatscc

######


assign05_sol: \
assign05_sol.dats; \
$(PATSCC) -o assign05_sol -DATS_MEMALLOC_LIBC assign05_sol.dats

######

clean:: ; rm -f *~
clean:: ; rm -f *_dats.c
cleanall:: clean
cleanall:: ; rm -f assign05_sol

############ end of [Makefile] ############