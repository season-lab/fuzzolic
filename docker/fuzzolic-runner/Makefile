build: # --force-rm 
	(cd ../../ && git submodule sync && git submodule update --init)
	(cd ../../solver/fuzzy-sat && git fetch && git submodule sync && git submodule update --init)
	docker build -t ercoppa/fuzzolic-runner-v1 -f ./Dockerfile ../../

push:
	docker push ercoppa/fuzzolic-runner-v1

patch-afl:
	cd AFLplusplus && git diff > ../../../utils/afl-showmap.c.patch