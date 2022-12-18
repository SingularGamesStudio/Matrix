#include "matrix.h"

#include <bits/stdc++.h>

using namespace std;

int main() {
    cout << Log2<4, 0, 30>::value;
    Matrix<3, 3> A = Matrix<3, 3>({{1, 2, 2}, {2, 4, 4}, {1, 2, 2}});
    Matrix<3, 3> B = Matrix<3, 3>({{1, 0, 3}, {3, 5, 8}, {5, 2, 7}});
    Matrix<3, 3> C = A * B;
    // cout << A.rank() << "\n";
    for (size_t i = 0; i < 3; i++) {
        for (size_t j = 0; j < 3; j++) {
            cout << C.val[i][j].asDecimal(2) << " ";
        }
        cout << "\n";
    }
}