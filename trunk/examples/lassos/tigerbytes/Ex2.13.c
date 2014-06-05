//#rTermination
/*
 * Date: 2014-06-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Example 2.13 from
 * https://tigerbytes2.lsu.edu/users/hchen11/lsl/LSL_benchmark.txt
 *
 * Comment: terminating, non-linear
 */

int main(int x, int y) {
    while (x - y > 0) {
        x = y - x;
        y++;
    }
    return 0;
}
