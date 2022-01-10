all: setup
all: build-targets
all: build-analysis
all: run-analysis

help:
	@echo "Usage:"
	@echo "\t" make build-targets
	@echo "\t" make build-analysis
	@echo "\t" make run-analysis


.PHONY: setup
setup: environ.sh
environ.sh:
	bash setup.sh

build-targets:
	sh ./build-targets.sh

build-analysis:
	sh ./build-analysis.sh

run-analysis:
	sh ./run-analysis.sh



.PHONY: submission
submission:
	mkdir -p submission/
	cp \
		Analysis.java \
		PAVBase.java \
		Lattice.java \
		submission/
	cp README.md     submission/
	cp *.sh submission/
	cp -r target1-pub/  submission/
	-rm submission/target1-pub/*.class
	cp -r target2-mine/ submission/
	-rm submission/target2-mine/*.class
	cp Makefile         submission/
	tar -cvzf submission.tar.gz  submission/


