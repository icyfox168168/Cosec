cmake_minimum_required(VERSION 3.20)
project(Cosec C)

set(CMAKE_C_STANDARD 99)

add_executable(Cosec
        src/analysis/Analysis.h
        src/analysis/CFG.c src/analysis/CFG.h
        src/analysis/Liveness.c src/analysis/Liveness.h
        src/analysis/UseChain.c src/analysis/UseChain.h
        src/opt/Fold.c src/opt/Fold.h
        src/Assembler.c src/Assembler.h
        src/Debug.c src/Debug.h
        src/Encoder.c src/Encoder.h
        src/IR.h src/IR.c
        src/Lexer.c src/Lexer.h
        src/main.c
        src/Parser.c src/Parser.h
        src/RegAlloc.c src/RegAlloc.h)

include(CTest)
include(FindPython3)
enable_testing()

macro(test name file)
    add_test(NAME ${name} COMMAND ${Python3_EXECUTABLE}
            ${PROJECT_SOURCE_DIR}/tests/RunTest.py $<TARGET_FILE:Cosec> ${PROJECT_SOURCE_DIR}/tests/${file})
endmacro()

test(return1 return/1.c)
test(return2 return/2.c)
test(return3 return/3.c)

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

test(assign1 expressions/assignment/1.c)
test(assign2 expressions/assignment/2.c)
test(assign3 expressions/assignment/3.c)
test(assign4 expressions/assignment/4.c)

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
