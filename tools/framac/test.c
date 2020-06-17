
/*@
    requires *arg == 0U;
    requires \valid(arg);
    assigns *arg;
    ensures *arg != 0U;
*/
void test(unsigned int * arg) {
    *arg = 1;
}