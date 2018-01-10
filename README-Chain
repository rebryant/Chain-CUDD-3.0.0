# Chain-CUDD-3.0.0
Modification of CUDD 3.0.0 to support chaining of BDDs and ZDDs

Only a subset of the functions have been updated to make use of
chaining.  As a result, some of the functionality of CUDD will not
work properly here.  In general, those that support Boolean operations
on BDDs, ZDDs, and ADDs work properly.  Most arithmetic operations on
ADDs should also work.  Those that involve quantification do not.
Dynamic variable ordering is not supported.


INSTALLATION NOTE:

If you retrieved the code via git, then the file dates will be
incorrect.  This can lead to problems with autoconfiguration, and
possibly cause the make command to fail.  The quick work around is to
execute the command:


	 touch Makefile.am Makefile.in aclocal.m4

before executing the make command.
