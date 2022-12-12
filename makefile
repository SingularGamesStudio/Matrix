geom: geom.out
	@./geom.out

geom.out: main.cpp geometry.h
	@g++ -std=c++20 -o geom.out main.cpp -Wall -Wextra -Werror -fsanitize=address
