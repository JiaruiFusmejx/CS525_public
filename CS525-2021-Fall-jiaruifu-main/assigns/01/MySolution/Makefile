######
#
# A simple Makefile
#
######

PATSCC=patscc
PATSOPT=patsopt
MYATSCC=myatscc

######

assign01_dats: ; \
$(MYATSCC) assign01.dats

######

clean:: ; rm -f *~
clean:: ; rm -f *_dats.c
cleanall:: clean
cleanall:: ; rm -f assign01_dats

############ end of [Makefile] ############