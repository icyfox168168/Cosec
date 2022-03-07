cmake_minimum_required(VERSION 3.20)
project(Cosec C)

set(CMAKE_C_STANDARD 99)

# Set some debug and release flags
set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra")
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

test(arith1 arithmetic/1.c)
test(arith2 arithmetic/2.c)
test(arith3 arithmetic/3.c)
test(arith4 arithmetic/4.c)
test(arith5 arithmetic/5.c)
test(arith6 arithmetic/6.c)
test(arith7 arithmetic/7.c)
test(arith8 arithmetic/8.c)
test(arith9 arithmetic/9.c)
test(arith10 arithmetic/10.c)
test(arith11 arithmetic/11.c)
test(arith12 arithmetic/12.c)
test(arith13 arithmetic/13.c)

test(assign1 assignment/1.c)
test(assign2 assignment/2.c)
test(assign3 assignment/3.c)
test(assign4 assignment/4.c)
test(assign5 assignment/5.c)
test(assign6 assignment/6.c)
test(assign7 assignment/7.c)

test(cond1 conditional/1.c)
test(cond2 conditional/2.c)
test(cond3 conditional/3.c)
test(cond4 conditional/4.c)
test(cond5 conditional/5.c)
test(cond6 conditional/6.c)
test(cond7 conditional/7.c)
test(cond8 conditional/8.c)
test(cond9 conditional/9.c)
test(cond10 conditional/10.c)
test(cond11 conditional/11.c)
test(cond12 conditional/12.c)
test(cond13 conditional/13.c)
test(cond14 conditional/14.c)
test(cond15 conditional/15.c)
test(cond16 conditional/16.c)
test(cond17 conditional/17.c)
test(cond18 conditional/18.c)
test(cond19 conditional/19.c)
test(cond20 conditional/20.c)
test(cond21 conditional/21.c)
test(cond22 conditional/22.c)

test(ptrs1 pointers/1.c)
test(ptrs2 pointers/2.c)
test(ptrs3 pointers/3.c)
test(ptrs4 pointers/4.c)
test(ptrs5 pointers/5.c)
test(ptrs6 pointers/6.c)
test(ptrs7 pointers/7.c)
test(ptrs8 pointers/8.c)

test(arrays1 arrays/1.c)
test(arrays2 arrays/2.c)
test(arrays3 arrays/3.c)
test(arrays4 arrays/4.c)
test(arrays5 arrays/5.c)
test(arrays6 arrays/6.c)
test(arrays7 arrays/7.c)

test(float1 floats/1.c)
test(float2 floats/2.c)
test(float3 floats/3.c)
test(float4 floats/4.c)
test(float5 floats/5.c)
test(float6 floats/6.c)

test(string1 strings/1.c)
test(string2 strings/2.c)
test(string3 strings/3.c)

test(sizeof1 sizeof/1.c)
test(sizeof2 sizeof/2.c)
test(sizeof3 sizeof/3.c)
test(sizeof4 sizeof/4.c)
test(sizeof5 sizeof/5.c)
test(sizeof6 sizeof/6.c)

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

test(fns1 functions/1.c)
test(fns2 functions/2.c)
test(fns3 functions/3.c)
