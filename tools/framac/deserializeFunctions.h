#ifndef MQTT_DESERIALIZEFUNCTIONS_H
#define MQTT_DESERIALIZEFUNCTIONS_H

#include "mqtt.h"
#include "mqtt_lightweight.h"

// Main function
MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent );    

// Helper functions 
static MQTTStatus_t deserializePingresp( const MQTTPacketInfo_t * const pPingresp );

static MQTTStatus_t deserializeSimpleAck( const MQTTPacketInfo_t * const pAck,
                                          uint16_t * pPacketIdentifier );

static MQTTStatus_t deserializeSuback( const MQTTPacketInfo_t * const pSuback,
                                       uint16_t * pPacketIdentifier );

static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent );

static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart);       

#define LogDebug( message )
#define LogError( message )
#define LogWarn( message )
#define LogInfo( message )

#define MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH     ( ( uint8_t ) 2 ) /**< @brief PUBACK, PUBREC, PUBREl, PUBCOMP, UNSUBACK Remaining length. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0U )            /**< @brief A PINGRESP packet always has a "Remaining length" of 0. */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01U ) /**< @brief The "Session Present" bit is always the lowest bit. */
#define MQTT_PACKET_CONNACK_REMAINING_LENGTH        ( ( uint8_t ) 2U )    /**< @brief A CONNACK packet always has a "Remaining length" of 2. */
#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )

#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ( ptr ) + 1 ) ) ) )

/*@
 assigns \nothing;
*/
static void logConnackResponse( uint8_t responseCode );

#endif                                    
