cmake_minimum_required(VERSION 3.20)
project(Cosec C)

set(CMAKE_C_STANDARD 99)

add_executable(Cosec
        src/main.c
        src/IR.c src/IR.h
        src/Lexer.c src/Lexer.h
        src/Parser.c src/Parser.h
        src/Assembler.c src/Assembler.h
        src/Encoder.c src/Encoder.h
        src/Debug.c src/Debug.h src/opt/Fold.c src/opt/Fold.h)
