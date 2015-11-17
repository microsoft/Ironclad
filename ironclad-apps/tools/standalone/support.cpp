#include <iostream>
#include <fstream>
#include <iomanip>
#include <assert.h>
#include <sstream>
#include <windows.h>
#include <winnt.h>
#include <string.h>
#include <stdint.h>

using namespace std;

void hello() {
  printf("Hello world\n");
}

void c_debug_print(int x, int y) {
  printf("%#2x, %#8x\n", x, y);




}

void c_exit() {
  exit(0);
}

void fixup_stack() {
  unsigned int* teb = (unsigned int*)NtCurrentTeb();

  NT_TIB* tib = (NT_TIB*)teb;

  tib->StackBase = (void*)0xffffffff;    
  tib->StackLimit = (void*)0;            

  //
  //*(teb + 4) = 0x44F000;  
  //*(teb + 8) = 0x44F400; 
  //
  ////*(teb + 4) = 0x44F400; 
  ////*(teb + 8) = 0x44F000; 
  
  
  

  
  
  
  
}

#define LOOP_COUNT (1<<25)

int total = 0;

void function5(int x) {
  for (int i = 0; i < LOOP_COUNT; i++) {
    total += i;
  }
}


void function4(int x) {
  for (int i = 0; i < LOOP_COUNT; i++) {
    total += i;
    if (i % 100000 == 0) {
      function5(x);
    }
  }
}

void function3(int x) {
  for (int i = 0; i < LOOP_COUNT; i++) {
    total += i;
    if (i % 100000 == 0) {
      function4(x);
    }
  }
}

void function2(int x) {
  for (int i = 0; i < LOOP_COUNT; i++) {
    total += i;
    if (i % 100000 == 0) {
      function3(x);
    }
  }
}

void function1(int x) {
  for (int i = 0; i < LOOP_COUNT; i++) {
    total += i;
    if (i % 100000 == 0) {
      function2(x);
    }
  }
}

void main() {
  hello();
  function1(24);
  hello();
}
