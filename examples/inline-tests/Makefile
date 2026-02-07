
.PHONY: test clean

clean:
	rm -rf ./build ./depends

test:
	mkdir -p ./depends/type-test-0
	cp -r ../../build/ttc/* ./depends/type-test-0/
	cd src && \
    ../../../result/bin/type-test --find-ipkg TestCases.idr
