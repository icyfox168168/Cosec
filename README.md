# Cosec

Cosec is a toy optimising C compiler, written to learn more about compiler 
theory.

Cosec only generates x86-64 NASM assembly code (which is my MacBook Pro's 
architecture) for the moment.

My goals for the project are:

* **Maintainable**: the source code is clear and well commented, written in a
  clean, modular, easily maintainable, and extensible fashion.
* **Complete**: the compiler is compliant with the C99 standard (excluding a few
  minor features, and including a few extra GCC conveniences) and can compile itself.
* **Standalone**: the compiler doesn't have any external dependencies.

### Usage

You can build the compiler with [CMake](https://cmake.org/):

```bash
$ mkdir build
$ cd build
$ cmake -DCMAKE_BUILD_TYPE=Release ..
$ make
```

The compiler generates x86-64 NASM assembly code from C files. Provided you have NASM
installed, you can compile a C file (for execution on macOS) with:

```bash
$ ./Cosec -o test.s test.c
$ nasm -f macho64 test.s
$ ld -L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib -lSystem test.o
```

You can print the (optimised) SSA IR for a C file with:

```bash
$ ./Cosec -ir test.c
```
