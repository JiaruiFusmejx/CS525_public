######
#
# A simple Makefile
#
######

PATSCC=patscc
PATSOPT=patsopt
MYATSCC=myatscc

######


assign03_sol: \
assign03_sol.dats; \
$(PATSCC) -o assign03_sol -DATS_MEMALLOC_LIBC assign03_sol.dats

######

clean:: ; rm -f *~
clean:: ; rm -f *_dats.c
cleanall:: clean
cleanall:: ; rm -f assign03_sol

############ end of [Makefile] ############