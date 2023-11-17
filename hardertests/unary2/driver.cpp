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
    int unary2();
}

int main() {
    if(unary2() == 1)
      std::cout << "PASSED Result: " << unary2() << std::endl;
  	else 
  	  std::cout << "FALIED Result: " << unary2() << std::endl;
}