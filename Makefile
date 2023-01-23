COQINCLUDE := -R $(shell pwd) MUT
# The following flag avoids warnings about the use of Restart.
COQFLAGS   := -async-proofs-cache force
include Makefile.coq

clean::
	rm -rf `cat .gitignore | grep -v _CoqProject`
	rm -rf src/*.vok src/*.vos src/*.v.d src/*.glob
