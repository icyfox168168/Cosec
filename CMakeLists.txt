cmake_minimum_required(VERSION 3.20)
project(Cosec C)

set(CMAKE_C_STANDARD 99)

add_executable(Cosec src/main.c src/Parser.c src/Parser.h src/IR.c src/IR.h src/Lexer.c src/Lexer.h src/Debug.c src/Debug.h)
