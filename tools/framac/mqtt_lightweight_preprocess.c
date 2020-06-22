# 1 "mqtt_lightweight.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "mqtt_lightweight.c"
# 22 "mqtt_lightweight.c"
# 1 "/usr/include/string.h" 1 3 4
# 26 "/usr/include/string.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 33 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 461 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 1 3 4
# 452 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 453 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/long-double.h" 1 3 4
# 454 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 462 "/usr/include/features.h" 2 3 4
# 485 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs-64.h" 1 3 4
# 11 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 2 3 4
# 486 "/usr/include/features.h" 2 3 4
# 34 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 2 3 4
# 27 "/usr/include/string.h" 2 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 1 3 4
# 209 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4

# 209 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 34 "/usr/include/string.h" 2 3 4
# 43 "/usr/include/string.h" 3 4
extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
       size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void *memmove (void *__dest, const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));





extern void *memccpy (void *__restrict __dest, const void *__restrict __src,
        int __c, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 91 "/usr/include/string.h" 3 4
extern void *memchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 122 "/usr/include/string.h" 3 4
extern char *strcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern char *strcat (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncat (char *__restrict __dest, const char *__restrict __src,
        size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern int strncmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcoll (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern size_t strxfrm (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));



# 1 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 1 3 4
# 22 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/__locale_t.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/types/__locale_t.h" 3 4
struct __locale_struct
{

  struct __locale_data *__locales[13];


  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;


  const char *__names[13];
};

typedef struct __locale_struct *__locale_t;
# 23 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 2 3 4

typedef __locale_t locale_t;
# 154 "/usr/include/string.h" 2 3 4


extern int strcoll_l (const char *__s1, const char *__s2, locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));


extern size_t strxfrm_l (char *__dest, const char *__src, size_t __n,
    locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));





extern char *strdup (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));






extern char *strndup (const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
# 226 "/usr/include/string.h" 3 4
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 253 "/usr/include/string.h" 3 4
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 273 "/usr/include/string.h" 3 4
extern size_t strcspn (const char *__s, const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern size_t strspn (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 303 "/usr/include/string.h" 3 4
extern char *strpbrk (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 330 "/usr/include/string.h" 3 4
extern char *strstr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strtok (char *__restrict __s, const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));



extern char *__strtok_r (char *__restrict __s,
    const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));

extern char *strtok_r (char *__restrict __s, const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
# 385 "/usr/include/string.h" 3 4
extern size_t strlen (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));




extern size_t strnlen (const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));




extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));
# 410 "/usr/include/string.h" 3 4
extern int strerror_r (int __errnum, char *__buf, size_t __buflen) __asm__ ("" "__xpg_strerror_r") __attribute__ ((__nothrow__ , __leaf__))

                        __attribute__ ((__nonnull__ (2)));
# 428 "/usr/include/string.h" 3 4
extern char *strerror_l (int __errnum, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));



# 1 "/usr/include/strings.h" 1 3 4
# 23 "/usr/include/strings.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 1 3 4
# 24 "/usr/include/strings.h" 2 3 4










extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bcopy (const void *__src, void *__dest, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 68 "/usr/include/strings.h" 3 4
extern char *index (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 96 "/usr/include/strings.h" 3 4
extern char *rindex (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));






extern int ffs (int __i) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));





extern int ffsl (long int __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__ extern int ffsll (long long int __ll)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));



extern int strcasecmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strncasecmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));






extern int strcasecmp_l (const char *__s1, const char *__s2, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));



extern int strncasecmp_l (const char *__s1, const char *__s2,
     size_t __n, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 4)));



# 433 "/usr/include/string.h" 2 3 4



extern void explicit_bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern char *strsep (char **__restrict __stringp,
       const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));


extern char *__stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));



extern char *__stpncpy (char *__restrict __dest,
   const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
# 499 "/usr/include/string.h" 3 4

# 23 "mqtt_lightweight.c" 2
# 1 "/usr/include/assert.h" 1 3 4
# 66 "/usr/include/assert.h" 3 4



extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));




extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));



# 24 "mqtt_lightweight.c" 2

# 1 "mqtt_lightweight.h" 1
# 27 "mqtt_lightweight.h"
    
# 27 "mqtt_lightweight.h"
   MQTT_PACKET_CONNECT_HEADER_SIZE






# 1 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 1 3 4
# 143 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4

# 143 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 321 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4
typedef int wchar_t;
# 415 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
# 426 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stddef.h" 3 4
} max_align_t;
# 35 "mqtt_lightweight.h" 2
# 1 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stdint.h" 1 3 4
# 9 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stdint.h" 3 4
# 1 "/usr/include/stdint.h" 1 3 4
# 26 "/usr/include/stdint.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 1 3 4
# 29 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;






typedef __int8_t __int_least8_t;
typedef __uint8_t __uint_least8_t;
typedef __int16_t __int_least16_t;
typedef __uint16_t __uint_least16_t;
typedef __int32_t __int_least32_t;
typedef __uint32_t __uint_least32_t;
typedef __int64_t __int_least64_t;
typedef __uint64_t __uint_least64_t;



typedef long int __quad_t;
typedef unsigned long int __u_quad_t;







typedef long int __intmax_t;
typedef unsigned long int __uintmax_t;
# 141 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/typesizes.h" 1 3 4
# 142 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/time64.h" 1 3 4
# 143 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;

typedef int __daddr_t;
typedef int __key_t;


typedef int __clockid_t;


typedef void * __timer_t;


typedef long int __blksize_t;




typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;


typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;


typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;


typedef long int __fsword_t;

typedef long int __ssize_t;


typedef long int __syscall_slong_t;

typedef unsigned long int __syscall_ulong_t;



typedef __off64_t __loff_t;
typedef char *__caddr_t;


typedef long int __intptr_t;


typedef unsigned int __socklen_t;




typedef int __sig_atomic_t;
# 28 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wchar.h" 1 3 4
# 29 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 30 "/usr/include/stdint.h" 2 3 4




# 1 "/usr/include/x86_64-linux-gnu/bits/stdint-intn.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdint-intn.h" 3 4
typedef __int8_t int8_t;
typedef __int16_t int16_t;
typedef __int32_t int32_t;
typedef __int64_t int64_t;
# 35 "/usr/include/stdint.h" 2 3 4


# 1 "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h" 3 4
typedef __uint8_t uint8_t;
typedef __uint16_t uint16_t;
typedef __uint32_t uint32_t;
typedef __uint64_t uint64_t;
# 38 "/usr/include/stdint.h" 2 3 4





typedef __int_least8_t int_least8_t;
typedef __int_least16_t int_least16_t;
typedef __int_least32_t int_least32_t;
typedef __int_least64_t int_least64_t;


typedef __uint_least8_t uint_least8_t;
typedef __uint_least16_t uint_least16_t;
typedef __uint_least32_t uint_least32_t;
typedef __uint_least64_t uint_least64_t;





typedef signed char int_fast8_t;

typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;
# 71 "/usr/include/stdint.h" 3 4
typedef unsigned char uint_fast8_t;

typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;
# 87 "/usr/include/stdint.h" 3 4
typedef long int intptr_t;


typedef unsigned long int uintptr_t;
# 101 "/usr/include/stdint.h" 3 4
typedef __intmax_t intmax_t;
typedef __uintmax_t uintmax_t;
# 10 "/usr/lib/gcc/x86_64-linux-gnu/9/include/stdint.h" 2 3 4
# 36 "mqtt_lightweight.h" 2




# 39 "mqtt_lightweight.h"
typedef uint8_t ** MQTTNetworkContext_t;
# 63 "mqtt_lightweight.h"
struct MQTTFixedBuffer;
typedef struct MQTTFixedBuffer MQTTFixedBuffer_t;

struct MQTTConnectInfo;
typedef struct MQTTConnectInfo MQTTConnectInfo_t;

struct MQTTSubscribeInfo;
typedef struct MQTTSubscribeInfo MQTTSubscribeInfo_t;

struct MqttPublishInfo;
typedef struct MqttPublishInfo MQTTPublishInfo_t;

struct MQTTPacketInfo;
typedef struct MQTTPacketInfo MQTTPacketInfo_t;
# 91 "mqtt_lightweight.h"
typedef int32_t (* MQTTTransportRecvFunc_t )( MQTTNetworkContext_t context,
                                              void * pBuffer,
                                              size_t bytesToRecv );




typedef enum MQTTStatus
{
    MQTTSuccess = 0,
    MQTTBadParameter,
    MQTTNoMemory,
    MQTTSendFailed,
    MQTTRecvFailed,
    MQTTBadResponse,
    MQTTServerRefused,
    MQTTNoDataAvailable,
    MQTTIllegalState,
    MQTTStateCollision,
    MQTTKeepAliveTimeout
} MQTTStatus_t;




typedef enum MQTTQoS
{
    MQTTQoS0 = 0,
    MQTTQoS1 = 1,
    MQTTQoS2 = 2
} MQTTQoS_t;







struct MQTTFixedBuffer
{
    uint8_t * pBuffer;
    size_t size;
};




struct MQTTConnectInfo
{



    bool cleanSession;




    uint16_t keepAliveSeconds;




    const char * pClientIdentifier;




    uint16_t clientIdentifierLength;




    const char * pUserName;




    uint16_t userNameLength;




    const char * pPassword;




    uint16_t passwordLength;
};




struct MQTTSubscribeInfo
{



    MQTTQoS_t qos;




    const char * pTopicFilter;




    uint16_t topicFilterLength;
};




struct MqttPublishInfo
{



    MQTTQoS_t qos;




    bool retain;




    bool dup;




    const char * pTopicName;




    uint16_t topicNameLength;




    const void * pPayload;




    size_t payloadLength;
};




struct MQTTPacketInfo
{



    uint8_t type;




    uint8_t * pRemainingData;




    size_t remainingLength;
};
# 275 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );
# 292 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );
# 308 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetSubscribePacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize );
# 326 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      const MQTTFixedBuffer_t * const pBuffer );
# 343 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetUnsubscribePacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                            size_t subscriptionCount,
                                            size_t * pRemainingLength,
                                            size_t * pPacketSize );
# 361 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * const pBuffer );
# 377 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );
# 398 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );
# 422 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize );
# 439 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * const pBuffer,
                                uint8_t packetType,
                                uint16_t packetId );
# 450 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetDisconnectPacketSize( size_t * pPacketSize );
# 461 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * const pBuffer );
# 470 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetPingreqPacketSize( size_t * pPacketSize );
# 481 "mqtt_lightweight.h"
MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_GetIncomingPacket( MQTTTransportRecvFunc_t recvFunc,
                                     MQTTNetworkContext_t networkContext,
                                     MQTTPacketInfo_t * const pIncomingPacket );
# 496 "mqtt_lightweight.h"
MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo );
# 511 "mqtt_lightweight.h"
MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent );
# 527 "mqtt_lightweight.h"
MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( MQTTTransportRecvFunc_t readFunc,
                                                  MQTTNetworkContext_t networkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket );
# 26 "mqtt_lightweight.c" 2
# 144 "mqtt_lightweight.c"
typedef enum MQTTSubscriptionType
{
    MQTT_SUBSCRIBE,
    MQTT_UNSUBSCRIBE
} MQTTSubscriptionType_t;
# 169 "mqtt_lightweight.c"
static void serializePublishCommon( const MQTTPublishInfo_t * pPublishInfo,
                                    size_t remainingLength,
                                    uint16_t packetIdentifier,
                                    const MQTTFixedBuffer_t * const pFixedBuffer,
                                    bool serializePayload );
# 186 "mqtt_lightweight.c"
static bool calculatePublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                        size_t * pRemainingLength,
                                        size_t * pPacketSize );
# 205 "mqtt_lightweight.c"
static MQTTStatus_t calculateSubscriptionPacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                     size_t subscriptionCount,
                                                     size_t * pRemainingLength,
                                                     size_t * pPacketSize,
                                                     MQTTSubscriptionType_t subscriptionType );
# 225 "mqtt_lightweight.c"
static MQTTStatus_t validateSubscriptionSerializeParams( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                         size_t subscriptionCount,
                                                         uint16_t packetId,
                                                         size_t remainingLength,
                                                         const MQTTFixedBuffer_t * const pBuffer );
# 240 "mqtt_lightweight.c"
static void serializeConnectPacket( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );



static size_t remainingLengthEncodedSize( size_t length )
{
    size_t encodedSize;





    if( length < 128U )
    {
        encodedSize = 1U;
    }

    else if( length < 16384U )
    {
        encodedSize = 2U;
    }

    else if( length < 2097152U )
    {
        encodedSize = 3U;
    }

    else
    {
        encodedSize = 4U;
    }

    LogDebug( ( "Encoded size for length =%ul is %ul.",
                length,
                encodedSize ) );

    return encodedSize;
}



static uint8_t * encodeRemainingLength( uint8_t * pDestination,
                                        size_t length )
{
    uint8_t lengthByte;
    uint8_t * pLengthEnd = 
# 288 "mqtt_lightweight.c" 3 4
                          ((void *)0)
# 288 "mqtt_lightweight.c"
                              ;
    size_t remainingLength = length;

    
# 291 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 291 "mqtt_lightweight.c"
   pDestination != 
# 291 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 291 "mqtt_lightweight.c"
   pDestination != 
# 291 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 291 "mqtt_lightweight.c"
   "pDestination != NULL"
# 291 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 291, __extension__ __PRETTY_FUNCTION__); }))
# 291 "mqtt_lightweight.c"
                                 ;

    pLengthEnd = pDestination;


    do
    {
        lengthByte = ( uint8_t ) ( remainingLength % 128U );
        remainingLength = remainingLength / 128U;


        if( remainingLength > 0U )
        {
            ( ( lengthByte ) = ( uint8_t ) ( ( lengthByte ) | ( 0x01U << ( 7 ) ) ) );
        }


        *pLengthEnd = lengthByte;
        pLengthEnd++;
    } while( remainingLength > 0U );

    return pLengthEnd;
}



static uint8_t * encodeString( uint8_t * pDestination,
                               const char * source,
                               uint16_t sourceLength )
{
    uint8_t * pBuffer = 
# 321 "mqtt_lightweight.c" 3 4
                       ((void *)0)
# 321 "mqtt_lightweight.c"
                           ;



    const uint8_t * pSourceBuffer = ( const uint8_t * ) source;

    
# 327 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 327 "mqtt_lightweight.c"
   pDestination != 
# 327 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 327 "mqtt_lightweight.c"
   pDestination != 
# 327 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 327 "mqtt_lightweight.c"
   "pDestination != NULL"
# 327 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 327, __extension__ __PRETTY_FUNCTION__); }))
# 327 "mqtt_lightweight.c"
                                 ;

    pBuffer = pDestination;


    *pBuffer = ( ( uint8_t ) ( ( sourceLength ) >> 8 ) );
    pBuffer++;


    *pBuffer = ( ( uint8_t ) ( ( sourceLength ) & 0x00ffU ) );
    pBuffer++;


    if( pSourceBuffer != 
# 340 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 340 "mqtt_lightweight.c"
                             )
    {
        ( void ) memcpy( pBuffer, pSourceBuffer, sourceLength );
    }


    pBuffer += sourceLength;

    return pBuffer;
}



static bool calculatePublishPacketSize( const MQTTPublishInfo_t * pPublishInfo,
                                        size_t * pRemainingLength,
                                        size_t * pPacketSize )
{
    bool status = true;
    size_t packetSize = 0, payloadLimit = 0;

    
# 360 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 360 "mqtt_lightweight.c"
   pPublishInfo != 
# 360 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 360 "mqtt_lightweight.c"
   pPublishInfo != 
# 360 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 360 "mqtt_lightweight.c"
   "pPublishInfo != NULL"
# 360 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 360, __extension__ __PRETTY_FUNCTION__); }))
# 360 "mqtt_lightweight.c"
                                 ;
    
# 361 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 361 "mqtt_lightweight.c"
   pRemainingLength != 
# 361 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 361 "mqtt_lightweight.c"
   pRemainingLength != 
# 361 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 361 "mqtt_lightweight.c"
   "pRemainingLength != NULL"
# 361 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 361, __extension__ __PRETTY_FUNCTION__); }))
# 361 "mqtt_lightweight.c"
                                     ;
    
# 362 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 362 "mqtt_lightweight.c"
   pPacketSize != 
# 362 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 362 "mqtt_lightweight.c"
   pPacketSize != 
# 362 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 362 "mqtt_lightweight.c"
   "pPacketSize != NULL"
# 362 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 362, __extension__ __PRETTY_FUNCTION__); }))
# 362 "mqtt_lightweight.c"
                                ;




    packetSize += pPublishInfo->topicNameLength + sizeof( uint16_t );



    if( pPublishInfo->qos > MQTTQoS0 )
    {
        packetSize += sizeof( uint16_t );
    }




    payloadLimit = ( 268435455UL ) - packetSize - 1U;


    if( pPublishInfo->payloadLength > payloadLimit )
    {
        LogError( ( "PUBLISH payload length of %lu cannot exceed "
                    "%lu so as not to exceed the maximum "
                    "remaining length of MQTT 3.1.1 packet( %lu ).",
                    pPublishInfo->payloadLength,
                    payloadLimit,
                    ( 268435455UL ) ) );
        status = false;
    }
    else
    {


        packetSize += pPublishInfo->payloadLength;



        payloadLimit -= remainingLengthEncodedSize( packetSize );


        if( pPublishInfo->payloadLength > payloadLimit )
        {
            LogError( ( "PUBLISH payload length of %lu cannot exceed "
                        "%lu so as not to exceed the maximum "
                        "remaining length of MQTT 3.1.1 packet( %lu ).",
                        pPublishInfo->payloadLength,
                        payloadLimit,
                        ( 268435455UL ) ) );
            status = false;
        }
        else
        {


            *pRemainingLength = packetSize;

            packetSize += 1U + remainingLengthEncodedSize( packetSize );
            *pPacketSize = packetSize;
        }
    }

    LogDebug( ( "PUBLISH packet remaining length=%lu and packet size=%lu.",
                *pRemainingLength,
                *pPacketSize ) );
    return status;
}



static void serializePublishCommon( const MQTTPublishInfo_t * pPublishInfo,
                                    size_t remainingLength,
                                    uint16_t packetIdentifier,
                                    const MQTTFixedBuffer_t * const pFixedBuffer,
                                    bool serializePayload )
{
    uint8_t * pIndex = 
# 438 "mqtt_lightweight.c" 3 4
                      ((void *)0)
# 438 "mqtt_lightweight.c"
                          ;
    const uint8_t * pPayloadBuffer = 
# 439 "mqtt_lightweight.c" 3 4
                                    ((void *)0)
# 439 "mqtt_lightweight.c"
                                        ;


    uint8_t publishFlags = ( ( uint8_t ) 0x30U );

    
# 444 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 444 "mqtt_lightweight.c"
   pPublishInfo != 
# 444 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 444 "mqtt_lightweight.c"
   pPublishInfo != 
# 444 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 444 "mqtt_lightweight.c"
   "pPublishInfo != NULL"
# 444 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 444, __extension__ __PRETTY_FUNCTION__); }))
# 444 "mqtt_lightweight.c"
                                 ;
    
# 445 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 445 "mqtt_lightweight.c"
   pFixedBuffer != 
# 445 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 445 "mqtt_lightweight.c"
   pFixedBuffer != 
# 445 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 445 "mqtt_lightweight.c"
   "pFixedBuffer != NULL"
# 445 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 445, __extension__ __PRETTY_FUNCTION__); }))
# 445 "mqtt_lightweight.c"
                                 ;

    
# 447 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 447 "mqtt_lightweight.c"
   pPublishInfo->qos == MQTTQoS0 || packetIdentifier != 0U
# 447 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 447 "mqtt_lightweight.c"
   pPublishInfo->qos == MQTTQoS0 || packetIdentifier != 0U
# 447 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 447 "mqtt_lightweight.c"
   "pPublishInfo->qos == MQTTQoS0 || packetIdentifier != 0U"
# 447 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 447, __extension__ __PRETTY_FUNCTION__); }))
# 447 "mqtt_lightweight.c"
                                                                    ;

    
# 449 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 449 "mqtt_lightweight.c"
   ( !pPublishInfo->dup ) || ( pPublishInfo->qos > MQTTQoS0 )
# 449 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 449 "mqtt_lightweight.c"
   ( !pPublishInfo->dup ) || ( pPublishInfo->qos > MQTTQoS0 )
# 449 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 449 "mqtt_lightweight.c"
   "( !pPublishInfo->dup ) || ( pPublishInfo->qos > MQTTQoS0 )"
# 449 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 449, __extension__ __PRETTY_FUNCTION__); }))
# 449 "mqtt_lightweight.c"
                                                                       ;


    pIndex = pFixedBuffer->pBuffer;

    if( pPublishInfo->qos == MQTTQoS1 )
    {
        LogDebug( ( "Adding QoS as QoS1 in PUBLISH flags." ) );
        ( ( publishFlags ) = ( uint8_t ) ( ( publishFlags ) | ( 0x01U << ( ( 1 ) ) ) ) );
    }
    else if( pPublishInfo->qos == MQTTQoS2 )
    {
        LogDebug( ( "Adding QoS as QoS2 in PUBLISH flags." ) );
        ( ( publishFlags ) = ( uint8_t ) ( ( publishFlags ) | ( 0x01U << ( ( 2 ) ) ) ) );
    }
    else
    {

    }

    if( pPublishInfo->retain )
    {
        LogDebug( ( "Adding retain bit in PUBLISH flags." ) );
        ( ( publishFlags ) = ( uint8_t ) ( ( publishFlags ) | ( 0x01U << ( ( 0 ) ) ) ) );
    }

    if( pPublishInfo->dup )
    {
        LogDebug( ( "Adding dup bit in PUBLISH flags." ) );
        ( ( publishFlags ) = ( uint8_t ) ( ( publishFlags ) | ( 0x01U << ( ( 3 ) ) ) ) );
    }

    *pIndex = publishFlags;
    pIndex++;


    pIndex = encodeRemainingLength( pIndex, remainingLength );


    pIndex = encodeString( pIndex,
                           pPublishInfo->pTopicName,
                           pPublishInfo->topicNameLength );


    if( pPublishInfo->qos > MQTTQoS0 )
    {
        LogDebug( ( "Adding packet Id in PUBLISH packet." ) );

        *pIndex = ( ( uint8_t ) ( ( packetIdentifier ) >> 8 ) );
        *( pIndex + 1 ) = ( ( uint8_t ) ( ( packetIdentifier ) & 0x00ffU ) );
        pIndex += 2;
    }





    if( ( pPublishInfo->payloadLength > 0U ) &&
        ( serializePayload ) )
    {
        LogDebug( ( "Copying PUBLISH payload of length =%lu to buffer",
                    pPublishInfo->payloadLength ) );



        pPayloadBuffer = ( const uint8_t * ) pPublishInfo->pPayload;

        ( void ) memcpy( pIndex, pPayloadBuffer, pPublishInfo->payloadLength );
        pIndex += pPublishInfo->payloadLength;
    }



    
# 522 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 522 "mqtt_lightweight.c"
   ( ( size_t ) ( pIndex - pFixedBuffer->pBuffer ) ) <= pFixedBuffer->size
# 522 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 522 "mqtt_lightweight.c"
   ( ( size_t ) ( pIndex - pFixedBuffer->pBuffer ) ) <= pFixedBuffer->size
# 522 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 522 "mqtt_lightweight.c"
   "( ( size_t ) ( pIndex - pFixedBuffer->pBuffer ) ) <= pFixedBuffer->size"
# 522 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 522, __extension__ __PRETTY_FUNCTION__); }))
# 522 "mqtt_lightweight.c"
                                                                                    ;
}

static size_t getRemainingLength( MQTTTransportRecvFunc_t recvFunc,
                                  MQTTNetworkContext_t networkContext )
{
    size_t remainingLength = 0, multiplier = 1, bytesDecoded = 0, expectedSize = 0;
    uint8_t encodedByte = 0;
    int32_t bytesReceived = 0;


    do
    {
        if( multiplier > 2097152U )
        {
            remainingLength = ( ( size_t ) 268435456 );
        }
        else
        {
            bytesReceived = recvFunc( networkContext, &encodedByte, 1U );

            if( bytesReceived == 1 )
            {
                remainingLength += ( ( size_t ) encodedByte & 0x7FU ) * multiplier;
                multiplier *= 128U;
                bytesDecoded++;
            }
            else
            {
                remainingLength = ( ( size_t ) 268435456 );
            }
        }

        if( remainingLength == ( ( size_t ) 268435456 ) )
        {
            break;
        }
    } while( ( encodedByte & 0x80U ) != 0U );


    if( remainingLength != ( ( size_t ) 268435456 ) )
    {
        expectedSize = remainingLengthEncodedSize( remainingLength );

        if( bytesDecoded != expectedSize )
        {
            remainingLength = ( ( size_t ) 268435456 );
        }
    }

    return remainingLength;
}



static bool incomingPacketValid( uint8_t packetType )
{
    bool status = false;


    switch( packetType & 0xF0U )
    {

        case ( ( uint8_t ) 0x20U ):
        case ( ( uint8_t ) 0x30U ):
        case ( ( uint8_t ) 0x40U ):
        case ( ( uint8_t ) 0x50U ):
        case ( ( uint8_t ) 0x70U ):
        case ( ( uint8_t ) 0x90U ):
        case ( ( uint8_t ) 0xB0U ):
        case ( ( uint8_t ) 0xD0U ):
            status = true;
            break;

        case ( ( ( uint8_t ) 0x62U ) & 0xF0U ):


            if( ( packetType & 0x02U ) > 0U )
            {
                status = true;
            }

            break;


        default:
            LogWarn( ( "Incoming packet invalid: Packet type=%u",
                       packetType ) );
            break;
    }

    return status;
}



static MQTTStatus_t checkPublishRemainingLength( size_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 size_t qos0Minimum )
{
    MQTTStatus_t status = MQTTSuccess;


    if( qos == MQTTQoS0 )
    {

        if( remainingLength < qos0Minimum )
        {
            LogDebug( ( "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                        qos0Minimum ) );

            status = MQTTBadResponse;
        }
    }
    else
    {



        if( remainingLength < ( qos0Minimum + 2U ) )
        {
            LogDebug( ( "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                        qos0Minimum + 2U ) );

            status = MQTTBadResponse;
        }
    }

    return status;
}



static MQTTStatus_t processPublishFlags( uint8_t publishFlags,
                                         MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 660 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 660 "mqtt_lightweight.c"
   pPublishInfo != 
# 660 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 660 "mqtt_lightweight.c"
   pPublishInfo != 
# 660 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 660 "mqtt_lightweight.c"
   "pPublishInfo != NULL"
# 660 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 660, __extension__ __PRETTY_FUNCTION__); }))
# 660 "mqtt_lightweight.c"
                                 ;


    if( ( ( ( publishFlags ) & ( 0x01U << ( ( 2 ) ) ) ) == ( 0x01U << ( ( 2 ) ) ) ) )
    {

        if( ( ( ( publishFlags ) & ( 0x01U << ( ( 1 ) ) ) ) == ( 0x01U << ( ( 1 ) ) ) ) )
        {
            LogDebug( ( "Bad QoS: 3." ) );

            status = MQTTBadResponse;
        }
        else
        {
            pPublishInfo->qos = MQTTQoS2;
        }
    }

    else if( ( ( ( publishFlags ) & ( 0x01U << ( ( 1 ) ) ) ) == ( 0x01U << ( ( 1 ) ) ) ) )
    {
        pPublishInfo->qos = MQTTQoS1;
    }

    else
    {
        pPublishInfo->qos = MQTTQoS0;
    }

    if( status == MQTTSuccess )
    {
        LogDebug( ( "QoS is %d.", pPublishInfo->qos ) );


        pPublishInfo->retain = ( ( ( publishFlags ) & ( 0x01U << ( ( 0 ) ) ) ) == ( 0x01U << ( ( 0 ) ) ) );

        LogDebug( ( "Retain bit is %d.", pPublishInfo->retain ) );


        if( ( ( ( publishFlags ) & ( 0x01U << ( ( 3 ) ) ) ) == ( 0x01U << ( ( 3 ) ) ) ) )
        {
            LogDebug( ( "DUP is 1." ) );
        }
        else
        {
            LogDebug( ( "DUP is 0." ) );
        }
    }

    return status;
}



static void logConnackResponse( uint8_t responseCode )
{
    const char * const pConnackResponses[ 6 ] =
    {
        "Connection accepted.",
        "Connection refused: unacceptable protocol version.",
        "Connection refused: identifier rejected.",
        "Connection refused: server unavailable",
        "Connection refused: bad user name or password.",
        "Connection refused: not authorized."
    };


    ( void ) responseCode;
    ( void ) pConnackResponses;

    
# 729 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 729 "mqtt_lightweight.c"
   responseCode <= 5
# 729 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 729 "mqtt_lightweight.c"
   responseCode <= 5
# 729 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 729 "mqtt_lightweight.c"
   "responseCode <= 5"
# 729 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 729, __extension__ __PRETTY_FUNCTION__); }))
# 729 "mqtt_lightweight.c"
                              ;


    LogError( ( "%s", pConnackResponses[ responseCode ] ) );
}



static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 742 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 742 "mqtt_lightweight.c"
   pConnack != 
# 742 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 742 "mqtt_lightweight.c"
   pConnack != 
# 742 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 742 "mqtt_lightweight.c"
   "pConnack != NULL"
# 742 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 742, __extension__ __PRETTY_FUNCTION__); }))
# 742 "mqtt_lightweight.c"
                             ;
    
# 743 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 743 "mqtt_lightweight.c"
   pSessionPresent != 
# 743 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 743 "mqtt_lightweight.c"
   pSessionPresent != 
# 743 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 743 "mqtt_lightweight.c"
   "pSessionPresent != NULL"
# 743 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 743, __extension__ __PRETTY_FUNCTION__); }))
# 743 "mqtt_lightweight.c"
                                    ;
    const uint8_t * pRemainingData = pConnack->pRemainingData;



    if( pConnack->remainingLength != ( ( uint8_t ) 2U ) )
    {
        LogError( ( "CONNACK does not have remaining length of %d.",
                    ( ( uint8_t ) 2U ) ) );

        status = MQTTBadResponse;
    }



    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        LogError( ( "Reserved bits in CONNACK incorrect." ) );

        status = MQTTBadResponse;
    }
    else
    {


        if( ( pRemainingData[ 0 ] & ( ( uint8_t ) 0x01U ) )
            == ( ( uint8_t ) 0x01U ) )
        {
            LogWarn( ( "CONNACK session present bit set." ) );
            *pSessionPresent = true;



            if( pRemainingData[ 1 ] != 0U )
            {
                status = MQTTBadResponse;
            }
        }
        else
        {
            LogInfo( ( "CONNACK session present bit not set." ) );
        }
    }

    if( status == MQTTSuccess )
    {

        if( pRemainingData[ 1 ] > 5U )
        {
            LogError( ( "CONNACK response %hhu is not valid.",
                        pRemainingData[ 1 ] ) );

            status = MQTTBadResponse;
        }
        else
        {


            logConnackResponse( pRemainingData[ 1 ] );


            if( pRemainingData[ 1 ] > 0U )
            {
                status = MQTTServerRefused;
            }
        }
    }

    return status;
}



static MQTTStatus_t calculateSubscriptionPacketSize( const MQTTSubscribeInfo_t * pSubscriptionList,
                                                     size_t subscriptionCount,
                                                     size_t * pRemainingLength,
                                                     size_t * pPacketSize,
                                                     MQTTSubscriptionType_t subscriptionType )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t i = 0, packetSize = 0;

    
# 825 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 825 "mqtt_lightweight.c"
   pSubscriptionList != 
# 825 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 825 "mqtt_lightweight.c"
   pSubscriptionList != 
# 825 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 825 "mqtt_lightweight.c"
   "pSubscriptionList != NULL"
# 825 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 825, __extension__ __PRETTY_FUNCTION__); }))
# 825 "mqtt_lightweight.c"
                                      ;
    
# 826 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 826 "mqtt_lightweight.c"
   subscriptionCount != 0U
# 826 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 826 "mqtt_lightweight.c"
   subscriptionCount != 0U
# 826 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 826 "mqtt_lightweight.c"
   "subscriptionCount != 0U"
# 826 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 826, __extension__ __PRETTY_FUNCTION__); }))
# 826 "mqtt_lightweight.c"
                                    ;
    
# 827 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 827 "mqtt_lightweight.c"
   pRemainingLength != 
# 827 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 827 "mqtt_lightweight.c"
   pRemainingLength != 
# 827 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 827 "mqtt_lightweight.c"
   "pRemainingLength != NULL"
# 827 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 827, __extension__ __PRETTY_FUNCTION__); }))
# 827 "mqtt_lightweight.c"
                                     ;
    
# 828 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 828 "mqtt_lightweight.c"
   pPacketSize != 
# 828 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 828 "mqtt_lightweight.c"
   pPacketSize != 
# 828 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 828 "mqtt_lightweight.c"
   "pPacketSize != NULL"
# 828 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 828, __extension__ __PRETTY_FUNCTION__); }))
# 828 "mqtt_lightweight.c"
                                ;



    packetSize += sizeof( uint16_t );



    for( i = 0; i < subscriptionCount; i++ )
    {


        packetSize += pSubscriptionList[ i ].topicFilterLength + sizeof( uint16_t );


        if( subscriptionType == MQTT_SUBSCRIBE )
        {
            packetSize += 1U;
        }
    }




    if( packetSize > ( 268435455UL ) )
    {
        LogError( ( "Subscription packet length of %lu exceeds"
                    "the MQTT 3.1.1 maximum packet length of %lu.",
                    packetSize,
                    ( 268435455UL ) ) );
        status = MQTTBadParameter;
    }
    else
    {
        *pRemainingLength = packetSize;




        packetSize += 1U + remainingLengthEncodedSize( packetSize );


        *pPacketSize = packetSize;
    }

    LogDebug( ( "Subscription packet remaining length=%lu and packet size=%lu.",
                *pRemainingLength,
                *pPacketSize ) );

    return status;
}



static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    
# 889 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 889 "mqtt_lightweight.c"
   pStatusStart != 
# 889 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 889 "mqtt_lightweight.c"
   pStatusStart != 
# 889 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 889 "mqtt_lightweight.c"
   "pStatusStart != NULL"
# 889 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 889, __extension__ __PRETTY_FUNCTION__); }))
# 889 "mqtt_lightweight.c"
                                 ;


    for( i = 0; i < statusCount; i++ )
    {

        subscriptionStatus = pStatusStart[ i ];


        switch( subscriptionStatus )
        {
            case 0x00:
            case 0x01:
            case 0x02:

                LogDebug( ( "Topic filter %lu accepted, max QoS %hhu.",
                            ( unsigned long ) i, subscriptionStatus ) );
                break;

            case 0x80:

                LogDebug( ( "Topic filter %lu refused.", ( unsigned long ) i ) );


                status = MQTTServerRefused;

                break;

            default:
                LogDebug( ( "Bad SUBSCRIBE status %hhu.", subscriptionStatus ) );

                status = MQTTBadResponse;

                break;
        }


        if( status == MQTTBadResponse )
        {
            break;
        }
    }

    return status;
}



static MQTTStatus_t deserializeSuback( const MQTTPacketInfo_t * const pSuback,
                                       uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 942 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 942 "mqtt_lightweight.c"
   pSuback != 
# 942 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 942 "mqtt_lightweight.c"
   pSuback != 
# 942 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 942 "mqtt_lightweight.c"
   "pSuback != NULL"
# 942 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 942, __extension__ __PRETTY_FUNCTION__); }))
# 942 "mqtt_lightweight.c"
                            ;
    
# 943 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 943 "mqtt_lightweight.c"
   pPacketIdentifier != 
# 943 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 943 "mqtt_lightweight.c"
   pPacketIdentifier != 
# 943 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 943 "mqtt_lightweight.c"
   "pPacketIdentifier != NULL"
# 943 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 943, __extension__ __PRETTY_FUNCTION__); }))
# 943 "mqtt_lightweight.c"
                                      ;

    size_t remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;



    if( remainingLength < 3U )
    {
        LogDebug( ( "SUBACK cannot have a remaining length less than 3." ) );
        status = MQTTBadResponse;
    }
    else
    {

        *pPacketIdentifier = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pVariableHeader ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pVariableHeader ) + 1 ) ) ) );

        LogDebug( ( "Packet identifier %hu.", *pPacketIdentifier ) );

        status = readSubackStatus( remainingLength - sizeof( uint16_t ),
                                   pVariableHeader + sizeof( uint16_t ) );
    }

    return status;
}



static MQTTStatus_t validateSubscriptionSerializeParams( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                         size_t subscriptionCount,
                                                         uint16_t packetId,
                                                         size_t remainingLength,
                                                         const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;




    size_t packetSize = 1U + remainingLengthEncodedSize( remainingLength )
                        + remainingLength;


    if( ( pBuffer == 
# 986 "mqtt_lightweight.c" 3 4
                    ((void *)0) 
# 986 "mqtt_lightweight.c"
                         ) || ( pSubscriptionList == 
# 986 "mqtt_lightweight.c" 3 4
                                                     ((void *)0) 
# 986 "mqtt_lightweight.c"
                                                          ) )
    {
        LogError( ( "Argument cannot be NULL: pBuffer=%p, "
                    "pSubscriptionList=%p.",
                    pBuffer,
                    pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetSize > pBuffer->size )
    {
        LogError( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized packet of size of %lu.",
                    pBuffer->size,
                    packetSize ) );
        status = MQTTNoMemory;
    }
    else
    {

    }

    return status;
}



static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                        uint16_t * const pPacketId,
                                        MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 1028 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1028 "mqtt_lightweight.c"
   pIncomingPacket != 
# 1028 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1028 "mqtt_lightweight.c"
   pIncomingPacket != 
# 1028 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1028 "mqtt_lightweight.c"
   "pIncomingPacket != NULL"
# 1028 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1028, __extension__ __PRETTY_FUNCTION__); }))
# 1028 "mqtt_lightweight.c"
                                    ;
    
# 1029 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1029 "mqtt_lightweight.c"
   pPacketId != 
# 1029 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1029 "mqtt_lightweight.c"
   pPacketId != 
# 1029 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1029 "mqtt_lightweight.c"
   "pPacketId != NULL"
# 1029 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1029, __extension__ __PRETTY_FUNCTION__); }))
# 1029 "mqtt_lightweight.c"
                              ;
    
# 1030 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1030 "mqtt_lightweight.c"
   pPublishInfo != 
# 1030 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1030 "mqtt_lightweight.c"
   pPublishInfo != 
# 1030 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1030 "mqtt_lightweight.c"
   "pPublishInfo != NULL"
# 1030 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1030, __extension__ __PRETTY_FUNCTION__); }))
# 1030 "mqtt_lightweight.c"
                                 ;
    const uint8_t * pVariableHeader = pIncomingPacket->pRemainingData, * pPacketIdentifierHigh;

    status = processPublishFlags( ( pIncomingPacket->type & 0x0FU ), pPublishInfo );

    if( status == MQTTSuccess )
    {





        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              ( 3U ) );
    }

    if( status == MQTTSuccess )
    {


        pPublishInfo->topicNameLength = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pVariableHeader ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pVariableHeader ) + 1 ) ) ) );



        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              pPublishInfo->topicNameLength + sizeof( uint16_t ) );
    }

    if( status == MQTTSuccess )
    {

        pPublishInfo->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );
        LogDebug( ( "Topic name length %hu: %.*s",
                    pPublishInfo->topicNameLength,
                    pPublishInfo->topicNameLength,
                    pPublishInfo->pTopicName ) );



        pPacketIdentifierHigh = ( const uint8_t * ) ( pPublishInfo->pTopicName + pPublishInfo->topicNameLength );

        if( pPublishInfo->qos > MQTTQoS0 )
        {
            *pPacketId = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pPacketIdentifierHigh ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pPacketIdentifierHigh ) + 1 ) ) ) );

            LogDebug( ( "Packet identifier %hu.", *pPacketId ) );


            if( *pPacketId == 0U )
            {
                status = MQTTBadResponse;
            }
        }
    }

    if( status == MQTTSuccess )
    {


        if( pPublishInfo->qos == MQTTQoS0 )
        {
            pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - sizeof( uint16_t ) );
            pPublishInfo->pPayload = pPacketIdentifierHigh;
        }
        else
        {
            pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - 2U * sizeof( uint16_t ) );
            pPublishInfo->pPayload = pPacketIdentifierHigh + sizeof( uint16_t );
        }

        LogDebug( ( "Payload length %hu.", pPublishInfo->payloadLength ) );
    }

    return status;
}



static MQTTStatus_t deserializeSimpleAck( const MQTTPacketInfo_t * const pAck,
                                          uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 1115 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1115 "mqtt_lightweight.c"
   pAck != 
# 1115 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1115 "mqtt_lightweight.c"
   pAck != 
# 1115 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1115 "mqtt_lightweight.c"
   "pAck != NULL"
# 1115 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1115, __extension__ __PRETTY_FUNCTION__); }))
# 1115 "mqtt_lightweight.c"
                         ;
    
# 1116 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1116 "mqtt_lightweight.c"
   pPacketIdentifier != 
# 1116 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1116 "mqtt_lightweight.c"
   pPacketIdentifier != 
# 1116 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1116 "mqtt_lightweight.c"
   "pPacketIdentifier != NULL"
# 1116 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1116, __extension__ __PRETTY_FUNCTION__); }))
# 1116 "mqtt_lightweight.c"
                                      ;


    if( pAck->remainingLength != ( ( uint8_t ) 2 ) )
    {
        LogError( ( "ACK does not have remaining length of %d.",
                    ( ( uint8_t ) 2 ) ) );

        status = MQTTBadResponse;
    }
    else
    {

        *pPacketIdentifier = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pAck->pRemainingData ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pAck->pRemainingData ) + 1 ) ) ) );

        LogDebug( ( "Packet identifier %hu.", *pPacketIdentifier ) );


        if( *pPacketIdentifier == 0U )
        {
            status = MQTTBadResponse;
        }
    }

    return status;
}



static MQTTStatus_t deserializePingresp( const MQTTPacketInfo_t * const pPingresp )
{
    MQTTStatus_t status = MQTTSuccess;

    
# 1149 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1149 "mqtt_lightweight.c"
   pPingresp != 
# 1149 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1149 "mqtt_lightweight.c"
   pPingresp != 
# 1149 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1149 "mqtt_lightweight.c"
   "pPingresp != NULL"
# 1149 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1149, __extension__ __PRETTY_FUNCTION__); }))
# 1149 "mqtt_lightweight.c"
                              ;


    if( pPingresp->remainingLength != ( 0U ) )
    {
        LogError( ( "PINGRESP does not have remaining length of %d.",
                    ( 0U ) ) );

        status = MQTTBadResponse;
    }

    return status;
}



static void serializeConnectPacket( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    uint8_t connectFlags = 0U;
    uint8_t * pIndex = 
# 1171 "mqtt_lightweight.c" 3 4
                      ((void *)0)
# 1171 "mqtt_lightweight.c"
                          ;

    
# 1173 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1173 "mqtt_lightweight.c"
   pConnectInfo != 
# 1173 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1173 "mqtt_lightweight.c"
   pConnectInfo != 
# 1173 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1173 "mqtt_lightweight.c"
   "pConnectInfo != NULL"
# 1173 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1173, __extension__ __PRETTY_FUNCTION__); }))
# 1173 "mqtt_lightweight.c"
                                 ;
    
# 1174 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1174 "mqtt_lightweight.c"
   pBuffer != 
# 1174 "mqtt_lightweight.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 1174 "mqtt_lightweight.c"
   pBuffer != 
# 1174 "mqtt_lightweight.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 1174 "mqtt_lightweight.c"
   "pBuffer != NULL"
# 1174 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1174, __extension__ __PRETTY_FUNCTION__); }))
# 1174 "mqtt_lightweight.c"
                            ;

    pIndex = pBuffer->pBuffer;

    *pIndex = ( ( uint8_t ) 0x10U );
    pIndex++;




    pIndex = encodeRemainingLength( pIndex, remainingLength );



    pIndex = encodeString( pIndex, "MQTT", 4 );


    *pIndex = ( ( uint8_t ) 4U );
    pIndex++;


    if( pConnectInfo->cleanSession == true )
    {
        ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 1 ) ) ) ) );
    }


    if( pConnectInfo->pUserName != 
# 1201 "mqtt_lightweight.c" 3 4
                                  ((void *)0) 
# 1201 "mqtt_lightweight.c"
                                       )
    {
        ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 7 ) ) ) ) );
    }

    if( pConnectInfo->pPassword != 
# 1206 "mqtt_lightweight.c" 3 4
                                  ((void *)0) 
# 1206 "mqtt_lightweight.c"
                                       )
    {
        ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 6 ) ) ) ) );
    }


    if( pWillInfo != 
# 1212 "mqtt_lightweight.c" 3 4
                    ((void *)0) 
# 1212 "mqtt_lightweight.c"
                         )
    {
        ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 2 ) ) ) ) );


        if( pWillInfo->qos == MQTTQoS1 )
        {
            ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 3 ) ) ) ) );
        }
        else if( pWillInfo->qos == MQTTQoS2 )
        {
            ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 4 ) ) ) ) );
        }
        else
        {

        }

        if( pWillInfo->retain == true )
        {
            ( ( connectFlags ) = ( uint8_t ) ( ( connectFlags ) | ( 0x01U << ( ( 5 ) ) ) ) );
        }
    }

    *pIndex = connectFlags;
    pIndex++;


    *pIndex = ( ( uint8_t ) ( ( pConnectInfo->keepAliveSeconds ) >> 8 ) );
    *( pIndex + 1 ) = ( ( uint8_t ) ( ( pConnectInfo->keepAliveSeconds ) & 0x00ffU ) );
    pIndex += 2;


    pIndex = encodeString( pIndex,
                           pConnectInfo->pClientIdentifier,
                           pConnectInfo->clientIdentifierLength );


    if( pWillInfo != 
# 1250 "mqtt_lightweight.c" 3 4
                    ((void *)0) 
# 1250 "mqtt_lightweight.c"
                         )
    {
        pIndex = encodeString( pIndex,
                               pWillInfo->pTopicName,
                               pWillInfo->topicNameLength );

        pIndex = encodeString( pIndex,
                               pWillInfo->pPayload,
                               ( uint16_t ) pWillInfo->payloadLength );
    }


    if( pConnectInfo->pUserName != 
# 1262 "mqtt_lightweight.c" 3 4
                                  ((void *)0) 
# 1262 "mqtt_lightweight.c"
                                       )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pUserName, pConnectInfo->userNameLength );
    }


    if( pConnectInfo->pPassword != 
# 1268 "mqtt_lightweight.c" 3 4
                                  ((void *)0) 
# 1268 "mqtt_lightweight.c"
                                       )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pPassword, pConnectInfo->passwordLength );
    }

    LogDebug( ( "Length of serialized CONNECT packet is %lu.",
                ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) ) );



    
# 1278 "mqtt_lightweight.c" 3 4
   ((void) sizeof ((
# 1278 "mqtt_lightweight.c"
   ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) <= pBuffer->size
# 1278 "mqtt_lightweight.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 1278 "mqtt_lightweight.c"
   ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) <= pBuffer->size
# 1278 "mqtt_lightweight.c" 3 4
   ) ; else __assert_fail (
# 1278 "mqtt_lightweight.c"
   "( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) <= pBuffer->size"
# 1278 "mqtt_lightweight.c" 3 4
   , "mqtt_lightweight.c", 1278, __extension__ __PRETTY_FUNCTION__); }))
# 1278 "mqtt_lightweight.c"
                                                                          ;
}



MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t remainingLength;


    size_t connectPacketSize = ( 10UL );


    if( ( pConnectInfo == 
# 1295 "mqtt_lightweight.c" 3 4
                         ((void *)0) 
# 1295 "mqtt_lightweight.c"
                              ) || ( pRemainingLength == 
# 1295 "mqtt_lightweight.c" 3 4
                                                         ((void *)0) 
# 1295 "mqtt_lightweight.c"
                                                              ) ||
        ( pPacketSize == 
# 1296 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 1296 "mqtt_lightweight.c"
                             ) )
    {
        LogError( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    pConnectInfo,
                    pRemainingLength,
                    pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( ( pConnectInfo->clientIdentifierLength == 0U ) || ( pConnectInfo->pClientIdentifier == 
# 1305 "mqtt_lightweight.c" 3 4
                                                                                                   ((void *)0) 
# 1305 "mqtt_lightweight.c"
                                                                                                        ) )
    {
        LogError( ( "Mqtt_GetConnectPacketSize() client identifier must be set." ) );
        status = MQTTBadParameter;
    }
    else
    {

        connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );


        if( pWillInfo != 
# 1316 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 1316 "mqtt_lightweight.c"
                             )
        {
            connectPacketSize += pWillInfo->topicNameLength + sizeof( uint16_t ) +
                                 pWillInfo->payloadLength + sizeof( uint16_t );
        }


        if( pConnectInfo->pUserName != 
# 1323 "mqtt_lightweight.c" 3 4
                                      ((void *)0) 
# 1323 "mqtt_lightweight.c"
                                           )
        {
            connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
        }

        if( pConnectInfo->pPassword != 
# 1328 "mqtt_lightweight.c" 3 4
                                      ((void *)0) 
# 1328 "mqtt_lightweight.c"
                                           )
        {
            connectPacketSize += pConnectInfo->passwordLength + sizeof( uint16_t );
        }



        remainingLength = connectPacketSize;



        connectPacketSize += 1U + remainingLengthEncodedSize( connectPacketSize );


        if( connectPacketSize > ( 327700UL ) )
        {
            status = MQTTBadParameter;
        }
        else
        {
            *pRemainingLength = remainingLength;
            *pPacketSize = connectPacketSize;
        }

        LogDebug( ( "CONNECT packet remaining length=%lu and packet size=%lu.",
                    *pRemainingLength,
                    *pPacketSize ) );
    }

    return status;
}



MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;


    size_t connectPacketSize = remainingLength + remainingLengthEncodedSize( remainingLength ) + 1U;


    if( ( pConnectInfo == 
# 1373 "mqtt_lightweight.c" 3 4
                         ((void *)0) 
# 1373 "mqtt_lightweight.c"
                              ) || ( pBuffer == 
# 1373 "mqtt_lightweight.c" 3 4
                                                ((void *)0) 
# 1373 "mqtt_lightweight.c"
                                                     ) )
    {
        LogError( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pBuffer=%p.",
                    pConnectInfo,
                    pBuffer ) );
        status = MQTTBadParameter;
    }

    else if( connectPacketSize > pBuffer->size )
    {
        LogError( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized CONNECT packet of size of %lu.",
                    pBuffer->size,
                    connectPacketSize ) );
        status = MQTTNoMemory;
    }
    else if( ( pWillInfo != 
# 1390 "mqtt_lightweight.c" 3 4
                           ((void *)0) 
# 1390 "mqtt_lightweight.c"
                                ) && ( pWillInfo->pTopicName == 
# 1390 "mqtt_lightweight.c" 3 4
                                                                ((void *)0) 
# 1390 "mqtt_lightweight.c"
                                                                     ) )
    {
        LogError( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
        status = MQTTBadParameter;
    }
    else
    {
        serializeConnectPacket( pConnectInfo,
                                pWillInfo,
                                remainingLength,
                                pBuffer );
    }

    return status;
}



MQTTStatus_t MQTT_GetSubscribePacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;


    if( ( pSubscriptionList == 
# 1416 "mqtt_lightweight.c" 3 4
                              ((void *)0) 
# 1416 "mqtt_lightweight.c"
                                   ) || ( pRemainingLength == 
# 1416 "mqtt_lightweight.c" 3 4
                                                              ((void *)0) 
# 1416 "mqtt_lightweight.c"
                                                                   ) ||
        ( pPacketSize == 
# 1417 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 1417 "mqtt_lightweight.c"
                             ) )
    {
        LogError( ( "Argument cannot be NULL: pSubscriptionList=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    pSubscriptionList,
                    pRemainingLength,
                    pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( " subscriptionCount is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {

        status = calculateSubscriptionPacketSize( pSubscriptionList,
                                                  subscriptionCount,
                                                  pRemainingLength,
                                                  pPacketSize,
                                                  MQTT_SUBSCRIBE );

        if( status == MQTTBadParameter )
        {
            LogError( ( "SUBSCRIBE packet remaining length exceeds %lu, which is the "
                        "maximum size allowed by MQTT 3.1.1.",
                        ( 268435455UL ) ) );
        }
    }

    return status;
}



MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      const MQTTFixedBuffer_t * const pBuffer )
{
    size_t i = 0;
    uint8_t * pIndex = 
# 1460 "mqtt_lightweight.c" 3 4
                      ((void *)0)
# 1460 "mqtt_lightweight.c"
                          ;


    MQTTStatus_t status =
        validateSubscriptionSerializeParams( pSubscriptionList,
                                             subscriptionCount,
                                             packetId,
                                             remainingLength,
                                             pBuffer );

    if( status == MQTTSuccess )
    {
        pIndex = pBuffer->pBuffer;


        *pIndex = ( ( uint8_t ) 0x82U );
        pIndex++;


        pIndex = encodeRemainingLength( pIndex, remainingLength );


        *pIndex = ( ( uint8_t ) ( ( packetId ) >> 8 ) );
        *( pIndex + 1 ) = ( ( uint8_t ) ( ( packetId ) & 0x00ffU ) );
        pIndex += 2;


        for( i = 0; i < subscriptionCount; i++ )
        {
            pIndex = encodeString( pIndex,
                                   pSubscriptionList[ i ].pTopicFilter,
                                   pSubscriptionList[ i ].topicFilterLength );


            *pIndex = ( uint8_t ) ( pSubscriptionList[ i ].qos );
            pIndex++;
        }

        LogDebug( ( "Length of serialized SUBSCRIBE packet is %lu.",
                    ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) ) );
    }

    return status;
}



MQTTStatus_t MQTT_GetUnsubscribePacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                            size_t subscriptionCount,
                                            size_t * pRemainingLength,
                                            size_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;


    if( ( pSubscriptionList == 
# 1515 "mqtt_lightweight.c" 3 4
                              ((void *)0) 
# 1515 "mqtt_lightweight.c"
                                   ) || ( pRemainingLength == 
# 1515 "mqtt_lightweight.c" 3 4
                                                              ((void *)0) 
# 1515 "mqtt_lightweight.c"
                                                                   ) ||
        ( pPacketSize == 
# 1516 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 1516 "mqtt_lightweight.c"
                             ) )
    {
        LogError( ( "Argument cannot be NULL: pSubscriptionList=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    pSubscriptionList,
                    pRemainingLength,
                    pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0U )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {

        status = calculateSubscriptionPacketSize( pSubscriptionList,
                                                  subscriptionCount,
                                                  pRemainingLength,
                                                  pPacketSize,
                                                  MQTT_UNSUBSCRIBE );

        if( status == MQTTBadParameter )
        {
            LogError( ( "UNSUBSCRIBE packet remaining length exceeds %lu, which is the "
                        "maximum size allowed by MQTT 3.1.1.",
                        ( 268435455UL ) ) );
        }
    }

    return status;
}



MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t i = 0;
    uint8_t * pIndex = 
# 1560 "mqtt_lightweight.c" 3 4
                      ((void *)0)
# 1560 "mqtt_lightweight.c"
                          ;


    status = validateSubscriptionSerializeParams( pSubscriptionList,
                                                  subscriptionCount,
                                                  packetId,
                                                  remainingLength,
                                                  pBuffer );

    if( status == MQTTSuccess )
    {

        pIndex = pBuffer->pBuffer;


        *pIndex = ( ( uint8_t ) 0xA2U );
        pIndex++;


        pIndex = encodeRemainingLength( pIndex, remainingLength );


        *pIndex = ( ( uint8_t ) ( ( packetId ) >> 8 ) );
        *( pIndex + 1 ) = ( ( uint8_t ) ( ( packetId ) & 0x00ffU ) );
        pIndex += 2;


        for( i = 0; i < subscriptionCount; i++ )
        {
            pIndex = encodeString( pIndex,
                                   pSubscriptionList[ i ].pTopicFilter,
                                   pSubscriptionList[ i ].topicFilterLength );
        }

        LogDebug( ( "Length of serialized UNSUBSCRIBE packet is %lu.",
                    ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) ) );
    }

    return status;
}



MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pPublishInfo == 
# 1609 "mqtt_lightweight.c" 3 4
                         ((void *)0) 
# 1609 "mqtt_lightweight.c"
                              ) || ( pRemainingLength == 
# 1609 "mqtt_lightweight.c" 3 4
                                                         ((void *)0) 
# 1609 "mqtt_lightweight.c"
                                                              ) || ( pPacketSize == 
# 1609 "mqtt_lightweight.c" 3 4
                                                                                    ((void *)0) 
# 1609 "mqtt_lightweight.c"
                                                                                         ) )
    {
        LogError( ( "Argument cannot be NULL: pPublishInfo=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    pPublishInfo,
                    pRemainingLength,
                    pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == 
# 1618 "mqtt_lightweight.c" 3 4
                                          ((void *)0) 
# 1618 "mqtt_lightweight.c"
                                               ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for PUBLISH: pTopicName=%p, "
                    "topicNameLength=%u.",
                    pPublishInfo->pTopicName,
                    pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else
    {


        if( calculatePublishPacketSize( pPublishInfo, pRemainingLength, pPacketSize ) == false )
        {
            LogError( ( "PUBLISH packet remaining length exceeds %lu, which is the "
                        "maximum size allowed by MQTT 3.1.1.",
                        ( 268435455UL ) ) );
            status = MQTTBadParameter;
        }
    }

    return status;
}



MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;




    size_t packetSize = 1U + remainingLengthEncodedSize( remainingLength )
                        + remainingLength;

    if( ( pBuffer == 
# 1657 "mqtt_lightweight.c" 3 4
                    ((void *)0) 
# 1657 "mqtt_lightweight.c"
                         ) || ( pPublishInfo == 
# 1657 "mqtt_lightweight.c" 3 4
                                                ((void *)0) 
# 1657 "mqtt_lightweight.c"
                                                     ) )
    {
        LogError( ( "Argument cannot be NULL: pBuffer=%p, "
                    "pPublishInfo=%p.",
                    pBuffer,
                    pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == 
# 1665 "mqtt_lightweight.c" 3 4
                                          ((void *)0) 
# 1665 "mqtt_lightweight.c"
                                               ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for PUBLISH: pTopicName=%p, "
                    "topicNameLength=%u.",
                    pPublishInfo->pTopicName,
                    pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for PUBLISH with QoS=%u.",
                    pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else if( packetSize > pBuffer->size )
    {
        LogError( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized PUBLISH packet of size of %lu.",
                    pBuffer->size,
                    packetSize ) );
        status = MQTTNoMemory;
    }
    else
    {

        serializePublishCommon( pPublishInfo,
                                remainingLength,
                                packetId,
                                pBuffer,
                                true );
    }

    return status;
}



MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize )
{
    MQTTStatus_t status = MQTTSuccess;







    size_t packetSize = 1U + remainingLengthEncodedSize( remainingLength )
                        + remainingLength;

    if( ( pBuffer == 
# 1719 "mqtt_lightweight.c" 3 4
                    ((void *)0) 
# 1719 "mqtt_lightweight.c"
                         ) || ( pPublishInfo == 
# 1719 "mqtt_lightweight.c" 3 4
                                                ((void *)0) 
# 1719 "mqtt_lightweight.c"
                                                     ) ||
        ( pHeaderSize == 
# 1720 "mqtt_lightweight.c" 3 4
                        ((void *)0) 
# 1720 "mqtt_lightweight.c"
                             ) )
    {
        LogError( ( "Argument cannot be NULL: pBuffer=%p, "
                    "pPublishInfo=%p, pHeaderSize=%p.",
                    pBuffer,
                    pPublishInfo,
                    pHeaderSize ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->pTopicName == 
# 1729 "mqtt_lightweight.c" 3 4
                                          ((void *)0) 
# 1729 "mqtt_lightweight.c"
                                               ) || ( pPublishInfo->topicNameLength == 0U ) )
    {
        LogError( ( "Invalid topic name for publish: pTopicName=%p, "
                    "topicNameLength=%u.",
                    pPublishInfo->pTopicName,
                    pPublishInfo->topicNameLength ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for publish with QoS=%u.",
                    pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }


    else if( ( packetSize - pPublishInfo->payloadLength ) > pBuffer->size )
    {
        LogError( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized PUBLISH header packet of size of %lu.",
                    pBuffer->size,
                    ( packetSize - pPublishInfo->payloadLength ) ) );
        status = MQTTNoMemory;
    }
    else
    {

        serializePublishCommon( pPublishInfo,
                                remainingLength,
                                packetId,
                                pBuffer,
                                false );


        *pHeaderSize = ( packetSize - pPublishInfo->payloadLength );
    }

    return status;
}



MQTTStatus_t MQTT_SerializeAck( const MQTTFixedBuffer_t * const pBuffer,
                                uint8_t packetType,
                                uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pBuffer == 
# 1777 "mqtt_lightweight.c" 3 4
                  ((void *)0) 
# 1777 "mqtt_lightweight.c"
                       )
    {
        LogError( ( "Provided buffer is NULL." ) );
        status = MQTTBadParameter;
    }

    else if( pBuffer->size < ( 4UL ) )
    {
        LogError( ( "Insufficient memory for packet." ) );
        status = MQTTNoMemory;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet ID cannot be 0." ) );
        status = MQTTBadParameter;
    }
    else
    {
        switch( packetType )
        {

            case ( ( uint8_t ) 0x40U ):
            case ( ( uint8_t ) 0x50U ):
            case ( ( uint8_t ) 0x62U ):
            case ( ( uint8_t ) 0x70U ):
                pBuffer->pBuffer[ 0 ] = packetType;
                pBuffer->pBuffer[ 1 ] = ( ( uint8_t ) 2 );
                pBuffer->pBuffer[ 2 ] = ( ( uint8_t ) ( ( packetId ) >> 8 ) );
                pBuffer->pBuffer[ 3 ] = ( ( uint8_t ) ( ( packetId ) & 0x00ffU ) );
                break;

            default:
                LogError( ( "Packet type is not a publish ACK: Packet type=%02x",
                            packetType ) );
                status = MQTTBadParameter;
                break;
        }
    }

    return status;
}



MQTTStatus_t MQTT_GetDisconnectPacketSize( size_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pPacketSize == 
# 1825 "mqtt_lightweight.c" 3 4
                      ((void *)0) 
# 1825 "mqtt_lightweight.c"
                           )
    {
        LogError( ( "pPacketSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {

        *pPacketSize = ( 2UL );
    }

    return status;
}



MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;


    if( pBuffer == 
# 1846 "mqtt_lightweight.c" 3 4
                  ((void *)0) 
# 1846 "mqtt_lightweight.c"
                       )
    {
        LogError( ( "pBuffer cannot be NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        if( pBuffer->size < ( 2UL ) )
        {
            LogError( ( "Buffer size of %lu is not sufficient to hold "
                        "serialized DISCONNECT packet of size of %lu.",
                        pBuffer->size,
                        ( 2UL ) ) );
            status = MQTTNoMemory;
        }
    }

    if( status == MQTTSuccess )
    {
        pBuffer->pBuffer[ 0 ] = ( ( uint8_t ) 0xE0U );
        pBuffer->pBuffer[ 1 ] = ( ( uint8_t ) 0 );
    }

    return status;
}



MQTTStatus_t MQTT_GetPingreqPacketSize( size_t * pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pPacketSize == 
# 1879 "mqtt_lightweight.c" 3 4
                      ((void *)0) 
# 1879 "mqtt_lightweight.c"
                           )
    {
        LogError( ( "pPacketSize is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {

        *pPacketSize = ( 2U );
    }

    return status;
}



MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    if( pBuffer == 
# 1899 "mqtt_lightweight.c" 3 4
                  ((void *)0) 
# 1899 "mqtt_lightweight.c"
                       )
    {
        LogError( ( "pBuffer is NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        if( pBuffer->size < ( 2U ) )
        {
            LogError( ( "Buffer size of %lu is not sufficient to hold "
                        "serialized PINGREQ packet of size of %u.",
                        pBuffer->size,
                        ( 2U ) ) );
            status = MQTTNoMemory;
        }
    }

    if( status == MQTTSuccess )
    {

        pBuffer->pBuffer[ 0 ] = ( ( uint8_t ) 0xC0U );
        pBuffer->pBuffer[ 1 ] = 0x00;
    }

    return status;
}



MQTTStatus_t MQTT_GetIncomingPacket( MQTTTransportRecvFunc_t recvFunc,
                                     MQTTNetworkContext_t networkContext,
                                     MQTTPacketInfo_t * const pIncomingPacket )
{
    return MQTTSuccess;
}



MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == 
# 1944 "mqtt_lightweight.c" 3 4
                            ((void *)0) 
# 1944 "mqtt_lightweight.c"
                                 ) || ( pPacketId == 
# 1944 "mqtt_lightweight.c" 3 4
                                                     ((void *)0) 
# 1944 "mqtt_lightweight.c"
                                                          ) || ( pPublishInfo == 
# 1944 "mqtt_lightweight.c" 3 4
                                                                                 ((void *)0) 
# 1944 "mqtt_lightweight.c"
                                                                                      ) )
    {
        LogError( ( "Argument cannot be NULL: pIncomingPacket=%p, "
                    "pPacketId=%p, pPublishInfo=%p",
                    pIncomingPacket,
                    pPacketId,
                    pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->type & 0xF0U ) != ( ( uint8_t ) 0x30U ) )
    {
        LogError( ( "Packet is not publish. Packet type: %hu.",
                    pIncomingPacket->type ) );
        status = MQTTBadParameter;
    }
    else
    {
        status = deserializePublish( pIncomingPacket, pPacketId, pPublishInfo );
    }

    return status;
}



MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == 
# 1975 "mqtt_lightweight.c" 3 4
                            ((void *)0) 
# 1975 "mqtt_lightweight.c"
                                 ) )
    {
        LogError( ( "pIncomingPacket cannot be NULL." ) );
        status = MQTTBadParameter;
    }



    else if( ( pPacketId == 
# 1983 "mqtt_lightweight.c" 3 4
                           ((void *)0) 
# 1983 "mqtt_lightweight.c"
                                ) &&
             ( ( pIncomingPacket->type != ( ( uint8_t ) 0x20U ) ) &&
               ( pIncomingPacket->type != ( ( uint8_t ) 0xD0U ) ) ) )
    {
        LogError( ( "pPacketId cannot be NULL for packet type %02x.",
                    pIncomingPacket->type ) );
        status = MQTTBadParameter;
    }

    else if( ( pSessionPresent == 
# 1992 "mqtt_lightweight.c" 3 4
                                 ((void *)0) 
# 1992 "mqtt_lightweight.c"
                                      ) &&
             ( pIncomingPacket->type == ( ( uint8_t ) 0x20U ) ) )
    {
        LogError( ( "pSessionPresent cannot be NULL for CONNACK packet." ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->pRemainingData == 
# 1998 "mqtt_lightweight.c" 3 4
                                               ((void *)0) 
# 1998 "mqtt_lightweight.c"
                                                    )
    {
        LogError( ( "Remaining data of incoming packet is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {

        switch( pIncomingPacket->type )
        {
            case ( ( uint8_t ) 0x20U ):
                status = deserializeConnack( pIncomingPacket, pSessionPresent );
                break;

            case ( ( uint8_t ) 0x90U ):
                status = deserializeSuback( pIncomingPacket, pPacketId );
                break;

            case ( ( uint8_t ) 0xD0U ):
                status = deserializePingresp( pIncomingPacket );
                break;

            case ( ( uint8_t ) 0xB0U ):
            case ( ( uint8_t ) 0x40U ):
            case ( ( uint8_t ) 0x50U ):
            case ( ( uint8_t ) 0x62U ):
            case ( ( uint8_t ) 0x70U ):
                status = deserializeSimpleAck( pIncomingPacket, pPacketId );
                break;


            default:
                LogError( ( "IotMqtt_DeserializeResponse() called with unknown packet type:(%02x).", pIncomingPacket->type ) );
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}



MQTTStatus_t MQTT_GetIncomingPacketTypeAndLength( MQTTTransportRecvFunc_t readFunc,
                                                  MQTTNetworkContext_t networkContext,
                                                  MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTSuccess;

    int32_t bytesReceived = readFunc( networkContext, &( pIncomingPacket->type ), 1U );

    if( bytesReceived == 1 )
    {

        if( incomingPacketValid( pIncomingPacket->type ) )
        {
            pIncomingPacket->remainingLength = getRemainingLength( readFunc, networkContext );

            if( pIncomingPacket->remainingLength == ( ( size_t ) 268435456 ) )
            {
                status = MQTTBadResponse;
            }
        }
        else
        {
            LogError( ( "Incoming packet invalid: Packet type=%u",
                        pIncomingPacket->type ) );
            status = MQTTBadResponse;
        }
    }
    else if( bytesReceived == 0 )
    {
        status = MQTTNoDataAvailable;
    }
    else
    {
        status = MQTTRecvFailed;
    }

    return status;
}
