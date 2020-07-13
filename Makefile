.PHONY : clean

chezlib = chez/intcode.so
out =

$(chezlib) : chez/intcode.sls
	echo "(compile-library \"$<\")" | scheme -q

build :
	make $(chezlib)

install : build
	mkdir -p $(out)
	cp $(chezlib) $(out)

clean :
	rm -f *~ $(chezlib) *.so
