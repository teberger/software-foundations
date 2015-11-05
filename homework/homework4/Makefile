default: compile

compile:
	ghc -o TLBN Main.hs

clean:
	rm *.hi
	rm *.o

run: TLBN
	echo "Running example 1"
	./TLBN example1.TLBN
	echo ""
	echo "Running example 2"
	./TLBN example2.TLBN
	echo ""
	echo "Running example 3"
	./TLBN example3.TLBN
	echo ""
	echo "Running example 4"
	./TLBN example4.TLBN
