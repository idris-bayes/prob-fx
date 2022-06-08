// To compile this file for the samples `sample/ffi/Small.idr` and `sample/ffi/Struct.idr`, you will
// need to manually compile and link it into a `.so` file, and place it in a location where the
// resulting exectuable can find it. For example:
//      gcc -c -fPIC smallc.c -o smallc.o
//      gcc smallc.o -shared -o libsmallc.so
//      idris2 Small.idr
// For an example of using Idris packages to build external (FFI) libraries, see the `FFI-readline`
// sample, and specifically `readline.ipkg`

#include <stdlib.h>
#include <stdio.h>
#include <gsl/gsl_rng.h>
#include <gsl/gsl_randist.h> 

// sudo apt-get install libgsl-dev
// gcc -Wall -I/home/mn15104/gsl/include -c libsmall.c
// gcc -L/home/mn15104/gsl/lib libsmall.o -lgsl -lgslcblas -lm
// cc -shared libsmall.c -o libsmall.so


int add(int x, int y) {
    return x+y;
}

int addWithMessage(char* msg, int x, int y) {
    printf("%s: %d + %d = %d\n", msg, x, y, x+y);
    return x+y;
}


double normal_pdf(double mu, double std) {
    return (gsl_ran_gaussian_pdf(mu, std));
}