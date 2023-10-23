CXX=clang++ -std=c++20
CFLAGS= -g -O3 `llvm-config --cppflags --ldflags --system-libs --libs all` \
-Wno-unused-function -Wno-unknown-warning-option -fno-rtti
OUTPUT = mccomp
SOURCES = mccomp.cpp computeSets.cpp
OBJECTS = $(SOURCES:.cpp=.o)

# Default target
all: $(OUTPUT)

# Rule to generate the output binary
$(OUTPUT): $(OBJECTS)
	$(CXX) $(CFLAGS) -o $(OUTPUT) $(OBJECTS)

# Rule to generate object files from source files
%.o: %.cpp
	$(CXX) $(CFLAGS) -c $< -o $@

clean:
	rm -rf $(OBJECTS) $(OUTPUT)
