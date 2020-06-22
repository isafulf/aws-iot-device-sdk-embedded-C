#ifndef MQTT_DESERIALIZECONNACK_H
#define MQTT_DESERIALIZECONNACK_H

#include "mqtt.h"
#include "mqtt_lightweight.h"

extern int printf(const char *__restrict __format, ...);

/*@
 assigns \nothing;
*/
static void logConnackResponse( uint8_t responseCode );

/*@
 assigns \nothing;
*/
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent );

static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                        uint16_t * const pPacketId,
                                        MQTTPublishInfo_t * const pPublishInfo );

#endif                                    