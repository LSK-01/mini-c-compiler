#include <iostream>
#include <cstdio>

// clang++ driver.cpp addition.ll -o add

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

extern "C" DLLEXPORT int print_int(int X) {
  fprintf(stderr, "%d\n", X);
  return 0;
}

extern "C" DLLEXPORT float print_float(float X) {
  fprintf(stderr, "%f\n", X);
  return 0;
}

extern "C" {
    int associativity();
}

int main() {
    if(associativity() == -4)
      std::cout << "PASSED Result: " << associativity() << std::endl;
  	else 
  	  std::cout << "FALIED Result: " << associativity() << std::endl;
}