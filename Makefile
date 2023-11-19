
CXX=clang++ -std=c++17
CFLAGS= -g -O3 `llvm-config --cppflags --ldflags --system-libs --libs all` \
-Wno-unused-function -Wno-unknown-warning-option -frtti

FILES = mccomp.cpp computeSets.cpp

mccomp: $(FILES)
	$(CXX) $(FILES) $(CFLAGS) -o mccomp

clean:
	rm -rf mccomp 