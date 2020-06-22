#ifndef MQTT_UTILS_H
#define MQTT_UTILS_H


#define SdkLog( string )    printf string


/*@
 assigns \nothing;
*/
extern void *memset(void *__s, int __c, size_t __n)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__nonnull__(1)));

extern int printf(const char *__restrict __format, ...);

/*@
 assigns \nothing;
*/
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

#endif