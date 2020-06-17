
/*@
 assigns \nothing;
*/
extern void *memset(void *__s, int __c, size_t __n)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__nonnull__(1)));

extern int printf(const char *__restrict __format, ...);