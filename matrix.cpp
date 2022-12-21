#include "matrix.h"

#include <bits/stdc++.h>

using namespace std;

int main() {
    BigInteger a(-5543);
    BigInteger b(20);
    auto t = a.smallDivide(b);
    cout << t.first << " " << t.second;
}