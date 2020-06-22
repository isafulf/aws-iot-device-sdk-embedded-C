# 1 "mqtt.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 31 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 32 "<command-line>" 2
# 1 "mqtt.c"
# 22 "mqtt.c"
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

# 23 "mqtt.c" 2
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



# 24 "mqtt.c" 2

# 1 "mqtt.h" 1
# 26 "mqtt.h"
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
# 27 "mqtt.h" 2



struct MQTTApplicationCallbacks;
typedef struct MQTTApplicationCallbacks MQTTApplicationCallbacks_t;

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext MQTTContext_t;

struct MQTTTransportInterface;
typedef struct MQTTTransportInterface MQTTTransportInterface_t;

typedef int32_t (* MQTTTransportSendFunc_t )( MQTTNetworkContext_t context,
                                              const void * pMessage,
                                              size_t bytesToSend );

typedef uint32_t (* MQTTGetCurrentTimeFunc_t )( void );

typedef void (* MQTTEventCallback_t )( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pPacketInfo,
                                       uint16_t packetIdentifier,
                                       MQTTPublishInfo_t * pPublishInfo );

typedef enum MQTTConnectionStatus
{
    MQTTNotConnected,
    MQTTConnected
} MQTTConnectionStatus_t;

typedef enum MQTTPublishState
{
    MQTTStateNull = 0,
    MQTTPublishSend,
    MQTTPubAckSend,
    MQTTPubRecSend,
    MQTTPubRelSend,
    MQTTPubCompSend,
    MQTTPubAckPending,
    MQTTPubRelPending,
    MQTTPubRecPending,
    MQTTPubCompPending,
    MQTTPublishDone
} MQTTPublishState_t;

typedef enum MQTTPubAckType
{
    MQTTPuback,
    MQTTPubrec,
    MQTTPubrel,
    MQTTPubcomp
} MQTTPubAckType_t;

struct MQTTTransportInterface
{
    MQTTTransportSendFunc_t send;
    MQTTTransportRecvFunc_t recv;
    MQTTNetworkContext_t networkContext;
};

struct MQTTApplicationCallbacks
{
    MQTTGetCurrentTimeFunc_t getTime;
    MQTTEventCallback_t appCallback;
};

struct MQTTPubAckInfo
{
    uint16_t packetId;
    MQTTQoS_t qos;
    MQTTPublishState_t publishState;
};

struct MQTTContext
{
    MQTTPubAckInfo_t outgoingPublishRecords[ 10U ];
    size_t outgoingPublishCount;
    MQTTPubAckInfo_t incomingPublishRecords[ 10U ];
    size_t incomingPublishCount;

    MQTTTransportInterface_t transportInterface;
    MQTTFixedBuffer_t networkBuffer;

    uint16_t nextPacketId;
    MQTTConnectionStatus_t connectStatus;
    MQTTApplicationCallbacks_t callbacks;
    uint32_t lastPacketTime;
    bool controlPacketSent;


    uint16_t keepAliveIntervalSec;
    uint32_t pingReqSendTimeMs;
    uint32_t pingRespTimeoutMs;
    bool waitingForPingResp;
};
# 173 "mqtt.h"
MQTTStatus_t MQTT_Init( MQTTContext_t * const pContext,
                        const MQTTTransportInterface_t * const pTransportInterface,
                        const MQTTApplicationCallbacks_t * const pCallbacks,
                        const MQTTFixedBuffer_t * const pNetworkBuffer );
# 198 "mqtt.h"
MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           uint32_t timeoutMs,
                           bool * const pSessionPresent );
# 219 "mqtt.h"
MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId );
# 236 "mqtt.h"
MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo,
                           uint16_t packetId );
# 250 "mqtt.h"
MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext );
# 267 "mqtt.h"
MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId );
# 283 "mqtt.h"
MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext );
# 302 "mqtt.h"
MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * const pContext,
                               uint32_t timeoutMs );
# 324 "mqtt.h"
uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext );
# 26 "mqtt.c" 2
# 1 "mqtt_state.h" 1
# 33 "mqtt_state.h"
typedef enum MQTTStateOperation
{
    MQTT_SEND,
    MQTT_RECEIVE,
} MQTTStateOperation_t;




typedef size_t MQTTStateCursor_t;
# 53 "mqtt_state.h"
MQTTStatus_t MQTT_ReserveState( MQTTContext_t * pMqttContext,
                                uint16_t packetId,
                                MQTTQoS_t qos );
# 65 "mqtt_state.h"
MQTTPublishState_t MQTT_CalculateStatePublish( MQTTStateOperation_t opType,
                                               MQTTQoS_t qos );
# 78 "mqtt_state.h"
MQTTPublishState_t MQTT_UpdateStatePublish( MQTTContext_t * pMqttContext,
                                            uint16_t packetId,
                                            MQTTStateOperation_t opType,
                                            MQTTQoS_t qos );
# 92 "mqtt_state.h"
MQTTPublishState_t MQTT_CalculateStateAck( MQTTPubAckType_t packetType,
                                           MQTTStateOperation_t opType,
                                           MQTTQoS_t qos );
# 106 "mqtt_state.h"
MQTTPublishState_t MQTT_UpdateStateAck( MQTTContext_t * pMqttContext,
                                        uint16_t packetId,
                                        MQTTPubAckType_t packetType,
                                        MQTTStateOperation_t opType );
# 118 "mqtt_state.h"
uint16_t MQTT_StateSelect( const MQTTContext_t * pMqttContext,
                           MQTTPublishState_t searchState,
                           MQTTStateCursor_t * pCursor );
# 27 "mqtt.c" 2
# 40 "mqtt.c"
static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );
# 57 "mqtt.c"
static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start );
# 67 "mqtt.c"
static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType );
# 78 "mqtt.c"
static int32_t recvExact( const MQTTContext_t * const pContext,
                          size_t bytesToRecv,
                          uint32_t timeoutMs );
# 91 "mqtt.c"
static MQTTStatus_t discardPacket( MQTTContext_t * const pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs );
# 104 "mqtt.c"
static MQTTStatus_t receivePacket( MQTTContext_t * const pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs );
# 117 "mqtt.c"
static MQTTStatus_t sendPublishAcks( MQTTContext_t * const pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t * pPublishState );
# 129 "mqtt.c"
static MQTTStatus_t handleKeepAlive( MQTTContext_t * const pContext );
# 139 "mqtt.c"
static MQTTStatus_t handleIncomingPublish( MQTTContext_t * const pContext,
                                           MQTTPacketInfo_t * pIncomingPacket );
# 150 "mqtt.c"
static MQTTStatus_t handleIncomingAck( MQTTContext_t * const pContext,
                                       MQTTPacketInfo_t * pIncomingPacket );
# 164 "mqtt.c"
static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * const pContext,
                                                        const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId );
# 179 "mqtt.c"
static MQTTStatus_t sendPublish( MQTTContext_t * const pContext,
                                 const MQTTPublishInfo_t * const pPublishInfo,
                                 size_t headerSize );
# 197 "mqtt.c"
static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const pIncomingPacket,
                                    bool * const pSessionPresent );



static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    const uint8_t * pIndex = pBufferToSend;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0, bytesSent;
    uint32_t sendTime = 0U;

    
# 213 "mqtt.c" 3 4
   ((void) sizeof ((
# 213 "mqtt.c"
   pContext != 
# 213 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 213 "mqtt.c"
   pContext != 
# 213 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 213 "mqtt.c"
   "pContext != NULL"
# 213 "mqtt.c" 3 4
   , "mqtt.c", 213, __extension__ __PRETTY_FUNCTION__); }))
# 213 "mqtt.c"
                             ;
    
# 214 "mqtt.c" 3 4
   ((void) sizeof ((
# 214 "mqtt.c"
   bytesToSend != 0
# 214 "mqtt.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 214 "mqtt.c"
   bytesToSend != 0
# 214 "mqtt.c" 3 4
   ) ; else __assert_fail (
# 214 "mqtt.c"
   "bytesToSend != 0"
# 214 "mqtt.c" 3 4
   , "mqtt.c", 214, __extension__ __PRETTY_FUNCTION__); }))
# 214 "mqtt.c"
                             ;


    sendTime = pContext->callbacks.getTime();
    bytesRemaining = bytesToSend;


    while( bytesRemaining > 0UL )
    {
        bytesSent = pContext->transportInterface.send( pContext->transportInterface.networkContext,
                                                       pIndex,
                                                       bytesRemaining );

        if( bytesSent > 0 )
        {
            bytesRemaining -= ( size_t ) bytesSent;
            totalBytesSent += bytesSent;
            pIndex += bytesSent;
            LogDebug( ( "Bytes sent=%d, bytes remaining=%ul,"
                        "total bytes sent=%d.",
                        bytesSent,
                        bytesRemaining,
                        totalBytesSent ) );
        }
        else
        {
            LogError( ( "Transport send failed." ) );
            totalBytesSent = -1;
            break;
        }
    }


    if( totalBytesSent > -1 )
    {
        pContext->lastPacketTime = sendTime;
        LogDebug( ( "Successfully sent packet at time %u.",
                    sendTime ) );
    }

    return totalBytesSent;
}



static uint32_t calculateElapsedTime( uint32_t later,
                                      uint32_t start )
{
    return later - start;
}



static MQTTPubAckType_t getAckFromPacketType( uint8_t packetType )
{
    MQTTPubAckType_t ackType = MQTTPuback;

    switch( packetType )
    {
        case ( ( uint8_t ) 0x40U ):
            ackType = MQTTPuback;
            break;

        case ( ( uint8_t ) 0x50U ):
            ackType = MQTTPubrec;
            break;

        case ( ( uint8_t ) 0x62U ):
            ackType = MQTTPubrel;
            break;

        case ( ( uint8_t ) 0x70U ):
            ackType = MQTTPubcomp;
            break;

        default:



            
# 293 "mqtt.c" 3 4
           ((void) sizeof ((
# 293 "mqtt.c"
           0
# 293 "mqtt.c" 3 4
           ) ? 1 : 0), __extension__ ({ if (
# 293 "mqtt.c"
           0
# 293 "mqtt.c" 3 4
           ) ; else __assert_fail (
# 293 "mqtt.c"
           "0"
# 293 "mqtt.c" 3 4
           , "mqtt.c", 293, __extension__ __PRETTY_FUNCTION__); }))
# 293 "mqtt.c"
                      ;
            break;
    }

    return ackType;
}



static int32_t recvExact( const MQTTContext_t * const pContext,
                          size_t bytesToRecv,
                          uint32_t timeoutMs )
{
    uint8_t * pIndex = 
# 306 "mqtt.c" 3 4
                      ((void *)0)
# 306 "mqtt.c"
                          ;
    size_t bytesRemaining = bytesToRecv;
    int32_t totalBytesRecvd = 0, bytesRecvd;
    uint32_t entryTimeMs = 0U;
    MQTTTransportRecvFunc_t recvFunc = 
# 310 "mqtt.c" 3 4
                                      ((void *)0)
# 310 "mqtt.c"
                                          ;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = 
# 311 "mqtt.c" 3 4
                                             ((void *)0)
# 311 "mqtt.c"
                                                 ;
    bool receiveError = false;

    
# 314 "mqtt.c" 3 4
   ((void) sizeof ((
# 314 "mqtt.c"
   pContext != 
# 314 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 314 "mqtt.c"
   pContext != 
# 314 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 314 "mqtt.c"
   "pContext != NULL"
# 314 "mqtt.c" 3 4
   , "mqtt.c", 314, __extension__ __PRETTY_FUNCTION__); }))
# 314 "mqtt.c"
                             ;
    
# 315 "mqtt.c" 3 4
   ((void) sizeof ((
# 315 "mqtt.c"
   bytesToRecv <= pContext->networkBuffer.size
# 315 "mqtt.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 315 "mqtt.c"
   bytesToRecv <= pContext->networkBuffer.size
# 315 "mqtt.c" 3 4
   ) ; else __assert_fail (
# 315 "mqtt.c"
   "bytesToRecv <= pContext->networkBuffer.size"
# 315 "mqtt.c" 3 4
   , "mqtt.c", 315, __extension__ __PRETTY_FUNCTION__); }))
# 315 "mqtt.c"
                                                        ;
    pIndex = pContext->networkBuffer.pBuffer;
    recvFunc = pContext->transportInterface.recv;
    getTimeStampMs = pContext->callbacks.getTime;
    entryTimeMs = getTimeStampMs();

    while( ( bytesRemaining > 0U ) && ( receiveError == false ) )
    {
        bytesRecvd = recvFunc( pContext->transportInterface.networkContext,
                               pIndex,
                               bytesRemaining );

        if( bytesRecvd >= 0 )
        {
            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += ( int32_t ) bytesRecvd;
            pIndex += bytesRecvd;
        }
        else
        {
            LogError( ( "Network error while receiving packet: ReturnCode=%d",
                        bytesRecvd ) );
            totalBytesRecvd = bytesRecvd;
            receiveError = true;
        }

        if( ( bytesRemaining > 0U ) &&
            ( calculateElapsedTime( getTimeStampMs(), entryTimeMs ) > timeoutMs ) )
        {
            LogError( ( "Time expired while receiving packet." ) );
            receiveError = true;
        }
    }

    return totalBytesRecvd;
}



static MQTTStatus_t discardPacket( MQTTContext_t * const pContext,
                                   size_t remainingLength,
                                   uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTRecvFailed;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;
    uint32_t totalBytesReceived = 0U, entryTimeMs, elapsedTimeMs;
    uint32_t remainingTimeMs = timeoutMs;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = 
# 363 "mqtt.c" 3 4
                                             ((void *)0)
# 363 "mqtt.c"
                                                 ;
    bool receiveError = false;

    
# 366 "mqtt.c" 3 4
   ((void) sizeof ((
# 366 "mqtt.c"
   pContext != 
# 366 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 366 "mqtt.c"
   pContext != 
# 366 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 366 "mqtt.c"
   "pContext != NULL"
# 366 "mqtt.c" 3 4
   , "mqtt.c", 366, __extension__ __PRETTY_FUNCTION__); }))
# 366 "mqtt.c"
                             ;
    bytesToReceive = pContext->networkBuffer.size;
    getTimeStampMs = pContext->callbacks.getTime;
    entryTimeMs = getTimeStampMs();

    while( ( totalBytesReceived < remainingLength ) && ( receiveError == false ) )
    {
        if( ( remainingLength - totalBytesReceived ) < bytesToReceive )
        {
            bytesToReceive = remainingLength - totalBytesReceived;
        }

        bytesReceived = recvExact( pContext, bytesToReceive, remainingTimeMs );

        if( bytesReceived != ( int32_t ) bytesToReceive )
        {
            LogError( ( "Receive error while discarding packet."
                        "ReceivedBytes=%d, ExpectedBytes=%lu.",
                        bytesReceived,
                        bytesToReceive ) );
            receiveError = true;
        }
        else
        {
            totalBytesReceived += ( uint32_t ) bytesReceived;

            elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

            if( elapsedTimeMs < timeoutMs )
            {
                remainingTimeMs = timeoutMs - elapsedTimeMs;
            }
            else
            {
                LogError( ( "Time expired while discarding packet." ) );
                receiveError = true;
            }
        }
    }

    if( totalBytesReceived == remainingLength )
    {
        LogError( ( "Dumped packet. DumpedBytes=%d.",
                    totalBytesReceived ) );

        status = MQTTNoDataAvailable;
    }

    return status;
}



static MQTTStatus_t receivePacket( MQTTContext_t * const pContext,
                                   MQTTPacketInfo_t incomingPacket,
                                   uint32_t remainingTimeMs )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesReceived = 0;
    size_t bytesToReceive = 0U;

    
# 427 "mqtt.c" 3 4
   ((void) sizeof ((
# 427 "mqtt.c"
   pContext != 
# 427 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 427 "mqtt.c"
   pContext != 
# 427 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 427 "mqtt.c"
   "pContext != NULL"
# 427 "mqtt.c" 3 4
   , "mqtt.c", 427, __extension__ __PRETTY_FUNCTION__); }))
# 427 "mqtt.c"
                             ;

    if( incomingPacket.remainingLength > pContext->networkBuffer.size )
    {
        LogError( ( "Incoming packet will be dumped: "
                    "Packet length exceeds network buffer size."
                    "PacketSize=%lu, NetworkBufferSize=%lu",
                    incomingPacket.remainingLength,
                    pContext->networkBuffer.size ) );
        status = discardPacket( pContext,
                                incomingPacket.remainingLength,
                                remainingTimeMs );
    }
    else
    {
        bytesToReceive = incomingPacket.remainingLength;
        bytesReceived = recvExact( pContext, bytesToReceive, remainingTimeMs );

        if( bytesReceived == ( int32_t ) bytesToReceive )
        {

            LogInfo( ( "Packet received. ReceivedBytes=%d.",
                       bytesReceived ) );
        }
        else
        {
            LogError( ( "Packet reception failed. ReceivedBytes=%d, "
                        "ExpectedBytes=%lu.",
                        bytesReceived,
                        bytesToReceive ) );
            status = MQTTRecvFailed;
        }
    }

    return status;
}



static MQTTStatus_t sendPublishAcks( MQTTContext_t * const pContext,
                                     uint16_t packetId,
                                     MQTTPublishState_t * pPublishState )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t newState = MQTTStateNull;
    int32_t bytesSent = 0;
    uint8_t packetTypeByte = 0U;
    MQTTPubAckType_t packetType;

    
# 476 "mqtt.c" 3 4
   ((void) sizeof ((
# 476 "mqtt.c"
   pContext != 
# 476 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 476 "mqtt.c"
   pContext != 
# 476 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 476 "mqtt.c"
   "pContext != NULL"
# 476 "mqtt.c" 3 4
   , "mqtt.c", 476, __extension__ __PRETTY_FUNCTION__); }))
# 476 "mqtt.c"
                             ;
    
# 477 "mqtt.c" 3 4
   ((void) sizeof ((
# 477 "mqtt.c"
   pPublishState != 
# 477 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 477 "mqtt.c"
   pPublishState != 
# 477 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 477 "mqtt.c"
   "pPublishState != NULL"
# 477 "mqtt.c" 3 4
   , "mqtt.c", 477, __extension__ __PRETTY_FUNCTION__); }))
# 477 "mqtt.c"
                                  ;

    switch( *pPublishState )
    {
        case MQTTPubAckSend:
            packetTypeByte = ( ( uint8_t ) 0x40U );
            packetType = MQTTPuback;
            break;

        case MQTTPubRecSend:
            packetTypeByte = ( ( uint8_t ) 0x50U );
            packetType = MQTTPubrec;
            break;

        case MQTTPubRelSend:
            packetTypeByte = ( ( uint8_t ) 0x62U );
            packetType = MQTTPubrel;
            break;

        case MQTTPubCompSend:
            packetTypeByte = ( ( uint8_t ) 0x70U );
            packetType = MQTTPubcomp;
            break;

        default:

            break;
    }

    if( packetTypeByte != 0U )
    {
        status = MQTT_SerializeAck( &( pContext->networkBuffer ),
                                    packetTypeByte,
                                    packetId );

        if( status == MQTTSuccess )
        {
            bytesSent = sendPacket( pContext,
                                    pContext->networkBuffer.pBuffer,
                                    ( 4UL ) );
        }

        if( bytesSent == ( int32_t ) ( 4UL ) )
        {
            pContext->controlPacketSent = true;
            newState = MQTT_UpdateStateAck( pContext,
                                            packetId,
                                            packetType,
                                            MQTT_SEND );

            if( newState == MQTTStateNull )
            {
                LogError( ( "Failed to update state of publish %u.",
                            packetId ) );
                status = MQTTIllegalState;
            }
        }
        else
        {
            LogError( ( "Failed to send ACK packet: PacketType=%02x, "
                        "SentBytes=%d, "
                        "PacketSize=%lu",
                        packetTypeByte,
                        bytesSent,
                        ( 4UL ) ) );
            status = MQTTSendFailed;
        }
    }

    if( ( status == MQTTSuccess ) && ( newState != MQTTStateNull ) )
    {
        *pPublishState = newState;
    }

    return status;
}



static MQTTStatus_t handleKeepAlive( MQTTContext_t * const pContext )
{
    MQTTStatus_t status = MQTTSuccess;
    uint32_t now = 0U, keepAliveMs = 0U;

    
# 561 "mqtt.c" 3 4
   ((void) sizeof ((
# 561 "mqtt.c"
   pContext != 
# 561 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 561 "mqtt.c"
   pContext != 
# 561 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 561 "mqtt.c"
   "pContext != NULL"
# 561 "mqtt.c" 3 4
   , "mqtt.c", 561, __extension__ __PRETTY_FUNCTION__); }))
# 561 "mqtt.c"
                             ;
    now = pContext->callbacks.getTime();
    keepAliveMs = 1000U * ( uint32_t ) pContext->keepAliveIntervalSec;


    if( ( keepAliveMs != 0U ) &&
        ( calculateElapsedTime( now, pContext->lastPacketTime ) > keepAliveMs ) )
    {
        if( pContext->waitingForPingResp )
        {

            if( calculateElapsedTime( now, pContext->pingReqSendTimeMs ) >
                pContext->pingRespTimeoutMs )
            {
                status = MQTTKeepAliveTimeout;
            }
        }
        else
        {
            status = MQTT_Ping( pContext );
        }
    }

    return status;
}



static MQTTStatus_t handleIncomingPublish( MQTTContext_t * const pContext,
                                           MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier;
    MQTTPublishInfo_t publishInfo;

    
# 597 "mqtt.c" 3 4
   ((void) sizeof ((
# 597 "mqtt.c"
   pContext != 
# 597 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 597 "mqtt.c"
   pContext != 
# 597 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 597 "mqtt.c"
   "pContext != NULL"
# 597 "mqtt.c" 3 4
   , "mqtt.c", 597, __extension__ __PRETTY_FUNCTION__); }))
# 597 "mqtt.c"
                             ;
    
# 598 "mqtt.c" 3 4
   ((void) sizeof ((
# 598 "mqtt.c"
   pIncomingPacket != 
# 598 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 598 "mqtt.c"
   pIncomingPacket != 
# 598 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 598 "mqtt.c"
   "pIncomingPacket != NULL"
# 598 "mqtt.c" 3 4
   , "mqtt.c", 598, __extension__ __PRETTY_FUNCTION__); }))
# 598 "mqtt.c"
                                    ;

    status = MQTT_DeserializePublish( pIncomingPacket, &packetIdentifier, &publishInfo );
    LogInfo( ( "De-serialized incoming PUBLISH packet: DeserializerResult=%d", status ) );

    if( status == MQTTSuccess )
    {
        publishRecordState = MQTT_UpdateStatePublish( pContext,
                                                      packetIdentifier,
                                                      MQTT_RECEIVE,
                                                      publishInfo.qos );
        LogInfo( ( "State record updated. New state=%d.",
                   publishRecordState ) );


        status = sendPublishAcks( pContext,
                                  packetIdentifier,
                                  &publishRecordState );
    }

    if( status == MQTTSuccess )
    {

        pContext->callbacks.appCallback( pContext,
                                         pIncomingPacket,
                                         packetIdentifier,
                                         &publishInfo );
    }

    return status;
}



static MQTTStatus_t handleIncomingAck( MQTTContext_t * const pContext,
                                       MQTTPacketInfo_t * pIncomingPacket )
{
    MQTTStatus_t status = MQTTBadResponse;
    MQTTPublishState_t publishRecordState = MQTTStateNull;
    uint16_t packetIdentifier;

    bool sessionPresent = false;
    MQTTPubAckType_t ackType;

    
# 642 "mqtt.c" 3 4
   ((void) sizeof ((
# 642 "mqtt.c"
   pContext != 
# 642 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 642 "mqtt.c"
   pContext != 
# 642 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 642 "mqtt.c"
   "pContext != NULL"
# 642 "mqtt.c" 3 4
   , "mqtt.c", 642, __extension__ __PRETTY_FUNCTION__); }))
# 642 "mqtt.c"
                             ;
    
# 643 "mqtt.c" 3 4
   ((void) sizeof ((
# 643 "mqtt.c"
   pIncomingPacket != 
# 643 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 643 "mqtt.c"
   pIncomingPacket != 
# 643 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 643 "mqtt.c"
   "pIncomingPacket != NULL"
# 643 "mqtt.c" 3 4
   , "mqtt.c", 643, __extension__ __PRETTY_FUNCTION__); }))
# 643 "mqtt.c"
                                    ;

    switch( pIncomingPacket->type )
    {
        case ( ( uint8_t ) 0x40U ):
        case ( ( uint8_t ) 0x50U ):
        case ( ( uint8_t ) 0x62U ):
        case ( ( uint8_t ) 0x70U ):
            ackType = getAckFromPacketType( pIncomingPacket->type );
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, &sessionPresent );
            LogInfo( ( "Ack packet deserialized with result: %d.", status ) );

            if( status == MQTTSuccess )
            {
                publishRecordState = MQTT_UpdateStateAck( pContext,
                                                          packetIdentifier,
                                                          ackType,
                                                          MQTT_RECEIVE );
                LogInfo( ( "State record updated. New state=%d.",
                           publishRecordState ) );


                status = sendPublishAcks( pContext,
                                          packetIdentifier,
                                          &publishRecordState );

                if( status == MQTTSuccess )
                {
                    pContext->callbacks.appCallback( pContext,
                                                     pIncomingPacket,
                                                     packetIdentifier,
                                                     
# 674 "mqtt.c" 3 4
                                                    ((void *)0) 
# 674 "mqtt.c"
                                                         );
                }
            }

            break;

        case ( ( uint8_t ) 0xD0U ):
            pContext->waitingForPingResp = false;
            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, &sessionPresent );

            if( status == MQTTSuccess )
            {
                pContext->callbacks.appCallback( pContext,
                                                 pIncomingPacket,
                                                 packetIdentifier,
                                                 
# 689 "mqtt.c" 3 4
                                                ((void *)0) 
# 689 "mqtt.c"
                                                     );
            }

            break;

        case ( ( uint8_t ) 0x90U ):
        case ( ( uint8_t ) 0xB0U ):

            status = MQTT_DeserializeAck( pIncomingPacket, &packetIdentifier, &sessionPresent );

            if( status == MQTTSuccess )
            {
                pContext->callbacks.appCallback( pContext,
                                                 pIncomingPacket,
                                                 packetIdentifier,
                                                 
# 704 "mqtt.c" 3 4
                                                ((void *)0) 
# 704 "mqtt.c"
                                                     );
            }

            break;

        default:

            LogError( ( "Unexpected packet type from server: PacketType=%02x.",
                        pIncomingPacket->type ) );
            status = MQTTBadResponse;
            break;
    }

    return status;
}



static MQTTStatus_t validateSubscribeUnsubscribeParams( const MQTTContext_t * const pContext,
                                                        const MQTTSubscribeInfo_t * const pSubscriptionList,
                                                        size_t subscriptionCount,
                                                        uint16_t packetId )
{
    MQTTStatus_t status = MQTTSuccess;


    if( ( pContext == 
# 730 "mqtt.c" 3 4
                     ((void *)0) 
# 730 "mqtt.c"
                          ) || ( pSubscriptionList == 
# 730 "mqtt.c" 3 4
                                                      ((void *)0) 
# 730 "mqtt.c"
                                                           ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pSubscriptionList=%p.",
                    pContext,
                    pSubscriptionList ) );
        status = MQTTBadParameter;
    }
    else if( subscriptionCount == 0UL )
    {
        LogError( ( "Subscription count is 0." ) );
        status = MQTTBadParameter;
    }
    else if( packetId == 0U )
    {
        LogError( ( "Packet Id for subscription packet is 0." ) );
        status = MQTTBadParameter;
    }
    else
    {

    }

    return status;
}



static MQTTStatus_t sendPublish( MQTTContext_t * const pContext,
                                 const MQTTPublishInfo_t * const pPublishInfo,
                                 size_t headerSize )
{
    MQTTStatus_t status = MQTTSuccess;
    int32_t bytesSent = 0;

    
# 765 "mqtt.c" 3 4
   ((void) sizeof ((
# 765 "mqtt.c"
   pContext != 
# 765 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 765 "mqtt.c"
   pContext != 
# 765 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 765 "mqtt.c"
   "pContext != NULL"
# 765 "mqtt.c" 3 4
   , "mqtt.c", 765, __extension__ __PRETTY_FUNCTION__); }))
# 765 "mqtt.c"
                             ;
    
# 766 "mqtt.c" 3 4
   ((void) sizeof ((
# 766 "mqtt.c"
   pPublishInfo != 
# 766 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 766 "mqtt.c"
   pPublishInfo != 
# 766 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 766 "mqtt.c"
   "pPublishInfo != NULL"
# 766 "mqtt.c" 3 4
   , "mqtt.c", 766, __extension__ __PRETTY_FUNCTION__); }))
# 766 "mqtt.c"
                                 ;
    
# 767 "mqtt.c" 3 4
   ((void) sizeof ((
# 767 "mqtt.c"
   headerSize > 0
# 767 "mqtt.c" 3 4
   ) ? 1 : 0), __extension__ ({ if (
# 767 "mqtt.c"
   headerSize > 0
# 767 "mqtt.c" 3 4
   ) ; else __assert_fail (
# 767 "mqtt.c"
   "headerSize > 0"
# 767 "mqtt.c" 3 4
   , "mqtt.c", 767, __extension__ __PRETTY_FUNCTION__); }))
# 767 "mqtt.c"
                           ;


    bytesSent = sendPacket( pContext,
                            pContext->networkBuffer.pBuffer,
                            headerSize );

    if( bytesSent < 0 )
    {
        LogError( ( "Transport send failed for PUBLISH header." ) );
        status = MQTTSendFailed;
    }
    else
    {
        LogDebug( ( "Sent %d bytes of PUBLISH header.",
                    bytesSent ) );


        bytesSent = sendPacket( pContext,
                                pPublishInfo->pPayload,
                                pPublishInfo->payloadLength );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for PUBLISH payload." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of PUBLISH payload.",
                        bytesSent ) );
        }
    }

    return status;
}



static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const pIncomingPacket,
                                    bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = 
# 812 "mqtt.c" 3 4
                                           ((void *)0)
# 812 "mqtt.c"
                                               ;
    uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;

    
# 815 "mqtt.c" 3 4
   ((void) sizeof ((
# 815 "mqtt.c"
   pContext != 
# 815 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 815 "mqtt.c"
   pContext != 
# 815 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 815 "mqtt.c"
   "pContext != NULL"
# 815 "mqtt.c" 3 4
   , "mqtt.c", 815, __extension__ __PRETTY_FUNCTION__); }))
# 815 "mqtt.c"
                             ;
    
# 816 "mqtt.c" 3 4
   ((void) sizeof ((
# 816 "mqtt.c"
   pIncomingPacket != 
# 816 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 816 "mqtt.c"
   pIncomingPacket != 
# 816 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 816 "mqtt.c"
   "pIncomingPacket != NULL"
# 816 "mqtt.c" 3 4
   , "mqtt.c", 816, __extension__ __PRETTY_FUNCTION__); }))
# 816 "mqtt.c"
                                    ;
    
# 817 "mqtt.c" 3 4
   ((void) sizeof ((
# 817 "mqtt.c"
   pContext->callbacks.getTime != 
# 817 "mqtt.c" 3 4
   ((void *)0)) ? 1 : 0), __extension__ ({ if (
# 817 "mqtt.c"
   pContext->callbacks.getTime != 
# 817 "mqtt.c" 3 4
   ((void *)0)) ; else __assert_fail (
# 817 "mqtt.c"
   "pContext->callbacks.getTime != NULL"
# 817 "mqtt.c" 3 4
   , "mqtt.c", 817, __extension__ __PRETTY_FUNCTION__); }))
# 817 "mqtt.c"
                                                ;

    getTimeStamp = pContext->callbacks.getTime;

    entryTimeMs = getTimeStamp();

    do
    {




        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.networkContext,
                                                      pIncomingPacket );


    } while( ( status == MQTTNoDataAvailable ) &&
             ( calculateElapsedTime( getTimeStamp(), entryTimeMs ) < timeoutMs ) );

    if( status == MQTTSuccess )
    {

        timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

        if( timeTakenMs < timeoutMs )
        {


            remainingTimeMs = timeoutMs - timeTakenMs;
        }





        if( pIncomingPacket->type == ( ( uint8_t ) 0x20U ) )
        {
            status = receivePacket( pContext,
                                    *pIncomingPacket,
                                    remainingTimeMs );
        }
        else
        {
            LogError( ( "Incorrect packet type %X received while expecting"
                        " CONNACK(%X).",
                        pIncomingPacket->type,
                        ( ( uint8_t ) 0x20U ) ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {

        pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;


        status = MQTT_DeserializeAck( pIncomingPacket, 
# 875 "mqtt.c" 3 4
                                                      ((void *)0)
# 875 "mqtt.c"
                                                          , pSessionPresent );
    }

    if( status != MQTTSuccess )
    {
        LogError( ( "CONNACK recv failed with status = %u.",
                    status ) );
    }
    else
    {
        LogInfo( ( "Received MQTT CONNACK successfully from broker." ) );
    }

    return status;
}



MQTTStatus_t MQTT_Init( MQTTContext_t * const pContext,
                        const MQTTTransportInterface_t * const pTransportInterface,
                        const MQTTApplicationCallbacks_t * const pCallbacks,
                        const MQTTFixedBuffer_t * const pNetworkBuffer )
{
    MQTTStatus_t status = MQTTSuccess;


    if( ( pContext == 
# 901 "mqtt.c" 3 4
                     ((void *)0) 
# 901 "mqtt.c"
                          ) || ( pTransportInterface == 
# 901 "mqtt.c" 3 4
                                                        ((void *)0) 
# 901 "mqtt.c"
                                                             ) ||
        ( pCallbacks == 
# 902 "mqtt.c" 3 4
                       ((void *)0) 
# 902 "mqtt.c"
                            ) || ( pNetworkBuffer == 
# 902 "mqtt.c" 3 4
                                                     ((void *)0) 
# 902 "mqtt.c"
                                                          ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pTransportInterface=%p "
                    "pCallbacks=%p "
                    "pNetworkBuffer=%p.",
                    pContext,
                    pTransportInterface,
                    pCallbacks,
                    pNetworkBuffer ) );
        status = MQTTBadParameter;
    }
    else
    {
        ( void ) memset( pContext, 0x00, sizeof( MQTTContext_t ) );

        pContext->connectStatus = MQTTNotConnected;
        pContext->transportInterface = *pTransportInterface;
        pContext->callbacks = *pCallbacks;
        pContext->networkBuffer = *pNetworkBuffer;


        pContext->nextPacketId = 1;
    }

    return status;
}



MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           uint32_t timeoutMs,
                           bool * const pSessionPresent )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPacketInfo_t incomingPacket = { .type = ( ( uint8_t ) 0 ) };

    if( ( pContext == 
# 943 "mqtt.c" 3 4
                     ((void *)0) 
# 943 "mqtt.c"
                          ) || ( pConnectInfo == 
# 943 "mqtt.c" 3 4
                                                 ((void *)0) 
# 943 "mqtt.c"
                                                      ) || ( pSessionPresent == 
# 943 "mqtt.c" 3 4
                                                                                ((void *)0) 
# 943 "mqtt.c"
                                                                                     ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pConnectInfo=%p, pSessionPresent=%p.",
                    pContext,
                    pConnectInfo,
                    pSessionPresent ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebug( ( "CONNECT packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeConnect( pConnectInfo,
                                        pWillInfo,
                                        remainingLength,
                                        &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for CONNECT packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of CONNECT packet.",
                        bytesSent ) );
        }
    }


    if( status == MQTTSuccess )
    {
        status = receiveConnack( pContext,
                                 timeoutMs,
                                 &incomingPacket,
                                 pSessionPresent );
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "MQTT connection established with the broker." ) );
        pContext->connectStatus = MQTTConnected;
    }
    else
    {
        LogError( ( "MQTT connection failed with status = %u.",
                    status ) );
    }

    return status;
}



MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;


    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {

        status = MQTT_GetSubscribePacketSize( pSubscriptionList,
                                              subscriptionCount,
                                              &remainingLength,
                                              &packetSize );
        LogDebug( ( "SUBSCRIBE packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_SerializeSubscribe( pSubscriptionList,
                                          subscriptionCount,
                                          packetId,
                                          remainingLength,
                                          &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {

        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for SUBSCRIBE packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of SUBSCRIBE packet.",
                        bytesSent ) );
        }
    }

    return status;
}



MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo,
                           uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL, headerSize = 0UL;
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;
    MQTTPublishState_t publishStatus = MQTTStateNull;


    if( ( pContext == 
# 1086 "mqtt.c" 3 4
                     ((void *)0) 
# 1086 "mqtt.c"
                          ) || ( pPublishInfo == 
# 1086 "mqtt.c" 3 4
                                                 ((void *)0) 
# 1086 "mqtt.c"
                                                      ) )
    {
        LogError( ( "Argument cannot be NULL: pContext=%p, "
                    "pPublishInfo=%p.",
                    pContext,
                    pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pPublishInfo->qos != MQTTQoS0 ) && ( packetId == 0U ) )
    {
        LogError( ( "Packet Id is 0 for PUBLISH with QoS=%u.",
                    pPublishInfo->qos ) );
        status = MQTTBadParameter;
    }
    else
    {

    }

    if( status == MQTTSuccess )
    {

        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            &remainingLength,
                                            &packetSize );
        LogDebug( ( "PUBLISH packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeader( pPublishInfo,
                                              packetId,
                                              remainingLength,
                                              &( pContext->networkBuffer ),
                                              &headerSize );
        LogDebug( ( "Serialized PUBLISH header size is %lu.",
                    headerSize ) );
    }

    if( status == MQTTSuccess )
    {

        if( pPublishInfo->qos > MQTTQoS0 )
        {
            status = MQTT_ReserveState( pContext,
                                        packetId,
                                        pPublishInfo->qos );
        }
    }

    if( status == MQTTSuccess )
    {

        status = sendPublish( pContext,
                              pPublishInfo,
                              headerSize );




    }

    if( status == MQTTSuccess )
    {


        if( pPublishInfo->qos > MQTTQoS0 )
        {



            publishStatus = MQTT_UpdateStatePublish( pContext,
                                                     packetId,
                                                     MQTT_SEND,
                                                     pPublishInfo->qos );

            if( publishStatus == MQTTStateNull )
            {
                LogError( ( "Update state for publish failed with status =%u."
                            " However PUBLISH packet is sent to the broker."
                            " Any further handling of ACKs for the packet Id"
                            " will fail.",
                            publishStatus ) );



                status = MQTTBadParameter;
            }
        }
    }

    if( status != MQTTSuccess )
    {
        LogError( ( "MQTT PUBLISH failed with status=%u.",
                    status ) );
    }

    return status;
}



MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext )
{
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;
    size_t packetSize;

    if( pContext == 
# 1196 "mqtt.c" 3 4
                   ((void *)0) 
# 1196 "mqtt.c"
                        )
    {
        LogError( ( "pContext is NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_GetPingreqPacketSize( &packetSize );

        if( status == MQTTSuccess )
        {
            LogDebug( ( "MQTT PINGREQ packet size is %lu.",
                        packetSize ) );
        }
        else
        {
            LogError( ( "Failed to get the PINGREQ packet size." ) );
        }
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_SerializePingreq( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {

        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for PINGREQ packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            pContext->pingReqSendTimeMs = pContext->lastPacketTime;
            pContext->waitingForPingResp = true;
            LogDebug( ( "Sent %d bytes of PINGREQ packet.",
                        bytesSent ) );
        }
    }

    return status;
}



MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId )
{
    size_t remainingLength = 0UL, packetSize = 0UL;
    int32_t bytesSent = 0;


    MQTTStatus_t status = validateSubscribeUnsubscribeParams( pContext,
                                                              pSubscriptionList,
                                                              subscriptionCount,
                                                              packetId );

    if( status == MQTTSuccess )
    {

        status = MQTT_GetUnsubscribePacketSize( pSubscriptionList,
                                                subscriptionCount,
                                                &remainingLength,
                                                &packetSize );
        LogDebug( ( "UNSUBSCRIBE packet size is %lu and remaining length is %lu.",
                    packetSize,
                    remainingLength ) );
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_SerializeUnsubscribe( pSubscriptionList,
                                            subscriptionCount,
                                            packetId,
                                            remainingLength,
                                            &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {

        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for UNSUBSCRIBE packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of UNSUBSCRIBE packet.",
                        bytesSent ) );
        }
    }

    return status;
}



MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext )
{
    size_t packetSize;
    int32_t bytesSent;
    MQTTStatus_t status = MQTTSuccess;


    if( pContext == 
# 1317 "mqtt.c" 3 4
                   ((void *)0) 
# 1317 "mqtt.c"
                        )
    {
        LogError( ( "pContext cannot be NULL." ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_GetDisconnectPacketSize( &packetSize );
        LogDebug( ( "MQTT DISCONNECT packet size is %lu.",
                    packetSize ) );
    }

    if( status == MQTTSuccess )
    {

        status = MQTT_SerializeDisconnect( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext,
                                pContext->networkBuffer.pBuffer,
                                packetSize );

        if( bytesSent < 0 )
        {
            LogError( ( "Transport send failed for DISCONNECT packet." ) );
            status = MQTTSendFailed;
        }
        else
        {
            LogDebug( ( "Sent %d bytes of DISCONNECT packet.",
                        bytesSent ) );
        }
    }

    if( status == MQTTSuccess )
    {
        LogInfo( ( "Disconnected from the broker." ) );
        pContext->connectStatus = MQTTNotConnected;
    }

    return status;
}



MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * const pContext,
                               uint32_t timeoutMs )
{
    MQTTStatus_t status = MQTTBadParameter;
    MQTTGetCurrentTimeFunc_t getTimeStampMs = 
# 1370 "mqtt.c" 3 4
                                             ((void *)0)
# 1370 "mqtt.c"
                                                 ;
    uint32_t entryTimeMs = 0U, remainingTimeMs = timeoutMs, elapsedTimeMs = 0U;
    MQTTPacketInfo_t incomingPacket;

    if( pContext != 
# 1374 "mqtt.c" 3 4
                   ((void *)0) 
# 1374 "mqtt.c"
                        )
    {
        getTimeStampMs = pContext->callbacks.getTime;
        entryTimeMs = getTimeStampMs();
        status = MQTTSuccess;
    }
    else
    {
        LogError( ( "MQTT Context cannot be NULL." ) );
    }

    while( status == MQTTSuccess )
    {
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.networkContext,
                                                      &incomingPacket );

        if( status == MQTTNoDataAvailable )
        {


            status = handleKeepAlive( pContext );

            if( status == MQTTSuccess )
            {


                status = MQTTNoDataAvailable;
            }
        }
        else if( status != MQTTSuccess )
        {
            LogError( ( "Receiving incoming packet length failed. Status=%d",
                        status ) );
        }
        else
        {

            status = receivePacket( pContext, incomingPacket, remainingTimeMs );
        }


        if( status == MQTTSuccess )
        {
            incomingPacket.pRemainingData = pContext->networkBuffer.pBuffer;



            if( ( incomingPacket.type & 0xF0U ) == ( ( uint8_t ) 0x30U ) )
            {
                status = handleIncomingPublish( pContext, &incomingPacket );
            }
            else
            {
                status = handleIncomingAck( pContext, &incomingPacket );
            }
        }

        if( status == MQTTNoDataAvailable )
        {


            status = MQTTSuccess;
        }

        if( status != MQTTSuccess )
        {
            LogError( ( "Exiting receive loop. Error status=%d", status ) );
        }


        elapsedTimeMs = calculateElapsedTime( getTimeStampMs(), entryTimeMs );

        if( elapsedTimeMs > timeoutMs )
        {
            break;
        }

        remainingTimeMs = timeoutMs - elapsedTimeMs;
    }

    return status;
}



uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext )
{
    uint16_t packetId = 0U;

    if( pContext != 
# 1464 "mqtt.c" 3 4
                   ((void *)0) 
# 1464 "mqtt.c"
                        )
    {
        packetId = pContext->nextPacketId++;

        if( pContext->nextPacketId == 0U )
        {
            pContext->nextPacketId++;
        }
    }

    return packetId;
}
