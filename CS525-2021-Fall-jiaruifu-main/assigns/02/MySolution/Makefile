######
#
# A simple Makefile
#
######

PATSCC=patscc
PATSOPT=patsopt
MYATSCC=myatscc

######


lambda0_sol: \
lambda0_sol.dats; \
$(PATSCC) -o lambda0_sol -DATS_MEMALLOC_LIBC lambda0_sol.dats

######

clean:: ; rm -f *~
clean:: ; rm -f *_dats.c
cleanall:: clean
cleanall:: ; rm -f lambda0_sol

############ end of [Makefile] ############