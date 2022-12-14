matrix: matrix.out
	@./matrix.out

matrix.out: matrix.cpp matrix.h biginteger.h
	@g++ -std=c++20 -o matrix.out matrix.cpp -Wall -Wextra -Werror -fsanitize=address
