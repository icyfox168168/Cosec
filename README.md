
# Cosec C Compiler

Cosec is a toy optimising C compiler, written to learn more about compiler
theory. Cosec only generates x86-64 NASM assembly code (which is my MacBook
Pro's architecture) for the moment.

My goals for the project are:

* **Maintainable**: the source code is clear and well commented, written in a
  clean, modular, easily maintainable, and extensible fashion.
* **Complete**: the compiler is compliant with the C99 standard (excluding a few
  minor features, and including a few extra GCC conveniences), and can compile
  itself.
* **Technically unique**: the compiler uses a select set of complex algorithms
  for parsing, optimisation, and code generation.
* **Standalone**: the compiler doesn't have any external dependencies.

Current features include:

* **Three levels of IR**: Cosec uses 3 levels of intermediate representation
  (IR) to compile C code, including a high-level abstract syntax tree (AST),
  intermediate-level static single assignment (SSA) form IR, and low-level
  assembly code IR.
* **Complex optimisations**: the compiler performs a complex set of
  optimisation and analysis passes on the SSA IR, to try and generate more
  efficient assembly.
* **Register allocation**: Cosec uses a complex graph-colouring algorithm for
  register allocation, including support for pre-coloured nodes, register
  coalescing, and spilling.

The compiler pipeline occurs in multiple stages, with the output of one stage
being fed into the next:

1. **Lexing**: the C source code is read and converted into a sequence of
   tokens.
2. **Preprocessing**: the C preprocessor is run on the output of the lexer,
   resolving things like `#include`s and `#define`s.
3. **Parsing**: an abstract syntax tree (AST) is constructed from the
   preprocessed sequence of tokens. Several validation steps occur in this
   process, such as ensuring the syntax is well-formed, variables are defined
   before use, type checking, etc.
4. **Compilation**: the static single assignment (SSA) form IR is generated
   from a well-formed AST. No validation occurs on the AST during this process;
   this is the responsibility of the parser (i.e., compilation shouldn't
   generate any errors).
5. **Optimisation and analysis**: various SSA IR analysis and optimisation
   passes are interleaved to try and generate more efficient assembly.
6. **Assembling**: the three-address SSA IR is lowered to the two-address
   target assembly language IR (only x86-64 is supported, for now).
8. **Register allocation**: the assembler generates IR that uses an unlimited
   number of virtual registers; it's the job of the register allocator to
   assign virtual registers to physical ones.
9. **Emission**: the final assembly code is written to an output file (only
   NASM assembly format is supported, for now).


## Using Cosec

You can compile a C file using Cosec with:

```bash
$ Cosec test.c
```

This generates the output x86-64 assembly file `test.s` in NASM format. You can
then assemble and link this file with:

```bash
$ nasm -f macho64 test.s
$ ld test.o
```

On macOS Big Sur (which is my MacBook Pro's operating system), you need to add
the following annoying linker arguments:

```bash
$ ld -lSystem -L/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk/usr/lib test.o
```

You can print the AST, (optimised) SSA IR, and assembly IR (prior to register
allocation) for a C file with:

```bash
$ ./Cosec --ir test.c
```

Other command line arguments include:

| Argument          | Description                                     |
|-------------------|-------------------------------------------------|
| `--version`, `-v` | Print version information                       |
| `--help`, `-h`    | Print usage information                         |
| `-o <file>`       | Set the output file                             |
| `--ir`            | Output AST, SSA, and assembly IR                |
| `--ast`           | Output the AST                                  |
| `--ssa`           | Output SSA IR                                   |
| `--asm`           | Output assembly IR (before register allocation) |


## Compiling Cosec

You can build a release version of Cosec with [CMake](https://cmake.org/):

```bash
$ mkdir build
$ cd build
$ cmake -DCMAKE_BUILD_TYPE=Release ..
$ make
```

You can build a debug version with:

```bash
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
```

Hopefully in the future, you'll be able to build Cosec with itself!
