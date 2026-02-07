
.PHONY: test clean

clean:
	rm -rf ./build ./depends

test:
	mkdir -p ./depends/type-test-0
	cp -r ../../build/ttc/* ./depends/type-test-0/
	find src -name '*.idr' | \
    xargs ../../result/bin/type-test --find-ipkg
