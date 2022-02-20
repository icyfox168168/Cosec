cmake_minimum_required(VERSION 3.20)
project(Cosec C)

set(CMAKE_C_STANDARD 99)

# Set some debug and release flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall")
set(CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -O0 -g")
set(CMAKE_C_FLAGS_RELEASE "${CMAKE_C_FLAGS_RELEASE} -O3")

add_executable(Cosec
        src/analysis/Analysis.h
        src/analysis/CFG.c src/analysis/CFG.h
        src/analysis/UseChain.c src/analysis/UseChain.h
        src/Assembler.c src/Assembler.h
        src/Compiler.c src/Compiler.h
        src/Debug.c src/Debug.h
        src/Emitter.c src/Emitter.h
        src/Error.c src/Error.h
        src/Lexer.c src/Lexer.h
        src/main.c
        src/Parser.c src/Parser.h
        src/RegAlloc.c src/RegAlloc.h src/Type.c src/Type.h)

# Require Python for testing
include(FindPython3)
enable_testing()

macro(test name file)
    add_test(NAME ${name} COMMAND ${Python3_EXECUTABLE}
            ${PROJECT_SOURCE_DIR}/tests/RunTest.py $<TARGET_FILE:Cosec> ${PROJECT_SOURCE_DIR}/tests/${file})
endmacro()

test(arith1 expressions/arithmetic/1.c)
test(arith2 expressions/arithmetic/2.c)
test(arith3 expressions/arithmetic/3.c)
test(arith4 expressions/arithmetic/4.c)
test(arith5 expressions/arithmetic/5.c)
test(arith6 expressions/arithmetic/6.c)
test(arith7 expressions/arithmetic/7.c)
test(arith8 expressions/arithmetic/8.c)
test(arith9 expressions/arithmetic/9.c)
test(arith10 expressions/arithmetic/10.c)
test(arith11 expressions/arithmetic/11.c)
test(arith12 expressions/arithmetic/12.c)
test(arith13 expressions/arithmetic/13.c)

test(assign1 expressions/assignment/1.c)
test(assign2 expressions/assignment/2.c)
test(assign3 expressions/assignment/3.c)
test(assign4 expressions/assignment/4.c)
test(assign5 expressions/assignment/5.c)
test(assign6 expressions/assignment/6.c)
test(assign7 expressions/assignment/7.c)

test(cond1 expressions/conditional/1.c)
test(cond2 expressions/conditional/2.c)
test(cond3 expressions/conditional/3.c)
test(cond4 expressions/conditional/4.c)
test(cond5 expressions/conditional/5.c)
test(cond6 expressions/conditional/6.c)
test(cond7 expressions/conditional/7.c)
test(cond8 expressions/conditional/8.c)
test(cond9 expressions/conditional/9.c)
test(cond10 expressions/conditional/10.c)
test(cond11 expressions/conditional/11.c)
test(cond12 expressions/conditional/12.c)
test(cond13 expressions/conditional/13.c)
test(cond14 expressions/conditional/14.c)
test(cond15 expressions/conditional/15.c)
test(cond16 expressions/conditional/16.c)
test(cond17 expressions/conditional/17.c)
test(cond18 expressions/conditional/18.c)
test(cond19 expressions/conditional/19.c)
test(cond20 expressions/conditional/20.c)
test(cond21 expressions/conditional/21.c)
test(cond22 expressions/conditional/22.c)

test(ptrs1 expressions/pointers/1.c)
test(ptrs2 expressions/pointers/2.c)
test(ptrs3 expressions/pointers/3.c)
test(ptrs4 expressions/pointers/4.c)
test(ptrs5 expressions/pointers/5.c)
test(ptrs6 expressions/pointers/6.c)
test(ptrs7 expressions/pointers/7.c)
test(ptrs8 expressions/pointers/8.c)

test(float1 expressions/floats/1.c)
test(float2 expressions/floats/2.c)
test(float3 expressions/floats/3.c)
test(float4 expressions/floats/4.c)
test(float5 expressions/floats/5.c)
test(float6 expressions/floats/6.c)

test(string1 expressions/strings/1.c)
test(string2 expressions/strings/2.c)
test(string3 expressions/strings/3.c)

test(return1 return/1.c)
test(return2 return/2.c)
test(return3 return/3.c)

test(decl1 declarations/1.c)
test(decl2 declarations/2.c)
test(decl3 declarations/3.c)

test(if1 if/1.c)
test(if2 if/2.c)
test(if3 if/3.c)
test(if4 if/4.c)
test(if5 if/5.c)
test(if6 if/6.c)
test(if7 if/7.c)
test(if8 if/8.c)
test(if9 if/9.c)

test(loop1 loop/1.c)
test(loop2 loop/2.c)
test(loop3 loop/3.c)
test(loop4 loop/4.c)
test(loop5 loop/5.c)
test(loop6 loop/6.c)
test(loop7 loop/7.c)
test(loop8 loop/8.c)
test(loop9 loop/9.c)
test(loop10 loop/10.c)
test(loop11 loop/11.c)
test(loop12 loop/12.c)

test(types1 types/1.c)
test(types2 types/2.c)
test(types3 types/3.c)
test(types4 types/4.c)
test(types5 types/5.c)
