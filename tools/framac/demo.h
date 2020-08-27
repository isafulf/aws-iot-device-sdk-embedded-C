#ifndef MQTT_DESERIALIZEFUNCTIONS_H
#define MQTT_DESERIALIZEFUNCTIONS_H

#include "mqtt.h"
#include "mqtt_lightweight.h"
#include <limits.h>

#define MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH     ( ( uint8_t ) 2 ) /**< @brief PUBACK, PUBREC, PUBREl, PUBCOMP, UNSUBACK Remaining length. */
#define MQTT_PACKET_PINGRESP_REMAINING_LENGTH       ( 0U )            /**< @brief A PINGRESP packet always has a "Remaining length" of 0. */
#define MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK    ( ( uint8_t ) 0x01U ) /**< @brief The "Session Present" bit is always the lowest bit. */
#define MQTT_PACKET_CONNACK_REMAINING_LENGTH        ( ( uint8_t ) 2U )    /**< @brief A CONNACK packet always has a "Remaining length" of 2. */
#define MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0    ( 3U )
#define MQTT_PUBLISH_FLAG_QOS1                      ( 1 ) /**< @brief MQTT PUBLISH QoS1 flag. */
#define MQTT_PUBLISH_FLAG_QOS2                      ( 2 ) /**< @brief MQTT PUBLISH QoS2 flag. */
#define MQTT_PUBLISH_FLAG_RETAIN                    ( 0 ) /**< @brief MQTT PUBLISH retain flag. */
#define MQTT_PUBLISH_FLAG_DUP                       ( 3 ) /**< @brief MQTT PUBLISH duplicate flag. */


#define UINT8_CHECK_BIT( x, position )    ( ( ( x ) & ( 0x01U << ( position ) ) ) == ( 0x01U << ( position ) ) )
#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ( ptr ) + 1 ) ) ) )

#define assert(ignore) ((void)0)

/*@
    predicate is_uint8(integer n) =
    0 <= n < 1 << 8;

    predicate is_uint16(integer n) =
    0 <= n < 1 << 16;

    predicate is_uint8_array(uint8_t* t, size_t length) =
        \valid(t + (0 .. length -  1));

    predicate is_char_array(char* t, size_t length) =
        \valid(t + (0 .. length - 1));

    predicate valid_qos(MQTTQoS_t qos) = 
        qos == MQTTQoS0 || qos == MQTTQoS1 || qos == MQTTQoS2;

    predicate is_size_t(size_t n) = 
        0 <= n <= UINT_MAX;
*/                   

// Main function
/*@
    requires \valid(pIncomingPacket);
    requires \valid(pPacketId);
    requires \valid(pSessionPresent);
    requires is_size_t(pIncomingPacket->remainingLength);
    requires is_uint16(*pIncomingPacket->pRemainingData << 8);
    requires is_uint8_array(pIncomingPacket->pRemainingData, pIncomingPacket->remainingLength);
    requires \separated(pIncomingPacket, pPacketId, pSessionPresent);
   
    assigns *pPacketId;
    assigns *pSessionPresent;

    behavior badInput:
        assumes pIncomingPacket == NULL ||
            ( ( pPacketId == NULL ) &&
            ( ( pIncomingPacket->type != MQTT_PACKET_TYPE_CONNACK ) &&
            ( pIncomingPacket->type != MQTT_PACKET_TYPE_PINGRESP ) ) ) ||
            ( ( pSessionPresent == NULL ) &&
            ( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK ) ) ||
            ( pIncomingPacket->pRemainingData == NULL );
        ensures *pPacketId == \old(*pPacketId);
        ensures *pSessionPresent == \old(*pSessionPresent); 
        ensures \result == MQTTBadParameter;

    disjoint behaviors;
*/

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent );    

// Helper functions 
/*@
    requires \valid(pPingresp);
    requires is_size_t(pPingresp->remainingLength);
    requires is_uint8_array(pPingresp->pRemainingData, pPingresp->remainingLength);

    assigns \nothing;
    
    ensures pPingresp->remainingLength != ( 0U ) ==> \result == MQTTBadResponse;
    ensures pPingresp->remainingLength == ( 0U ) ==> \result == MQTTSuccess;
*/
static MQTTStatus_t deserializePingresp( const MQTTPacketInfo_t * const pPingresp );

/*@
    requires \valid(pAck);
    requires \valid(pPacketIdentifier);
    requires is_size_t(pAck->remainingLength);
    requires is_uint8_array(pAck->pRemainingData, pAck->remainingLength);
    requires is_uint16(*pAck->pRemainingData << 8);
    requires \separated(pAck, pPacketIdentifier);
  
    assigns *pPacketIdentifier;
  
    ensures pAck->remainingLength != ( ( uint8_t ) 2 ) ==> *pPacketIdentifier == \old(*pPacketIdentifier) && \result == MQTTBadResponse;
    ensures pAck->remainingLength == ( ( uint8_t ) 2 ) ==> *pPacketIdentifier == UINT16_DECODE(pAck->pRemainingData);
    ensures pAck->remainingLength == ( ( uint8_t ) 2 ) && *pPacketIdentifier == 0U ==> \result == MQTTBadResponse;
    ensures pAck->remainingLength == ( ( uint8_t ) 2 ) && *pPacketIdentifier != 0U ==> \result == MQTTSuccess;
*/
static MQTTStatus_t deserializeSimpleAck( const MQTTPacketInfo_t * const pAck,
                                          uint16_t * pPacketIdentifier );

/*@
    requires \valid(pSuback);
    requires is_size_t(pSuback->remainingLength);
    requires is_uint8_array(pSuback->pRemainingData, pSuback->remainingLength);
    requires \valid(pPacketIdentifier);
    requires is_uint16(*pSuback->pRemainingData << 8);
    requires is_uint16(*pPacketIdentifier);
    requires \separated(pSuback, pPacketIdentifier);
  
    assigns *pPacketIdentifier;

    behavior badInput:
        assumes pSuback->remainingLength < 3U;
        ensures *pPacketIdentifier == \old(*pPacketIdentifier);
        ensures \result == MQTTBadResponse;
    
    behavior goodInput:
        assumes pSuback->remainingLength >= 3U;
        ensures *pPacketIdentifier == UINT16_DECODE(pSuback->pRemainingData);
    
    complete behaviors;
    disjoint behaviors;
*/
static MQTTStatus_t deserializeSuback( const MQTTPacketInfo_t * const pSuback,
                                       uint16_t * pPacketIdentifier );

/*@
    requires \valid(pConnack);
    requires \valid(pSessionPresent);
    requires is_size_t(pConnack->remainingLength);
    requires is_uint8_array(pConnack->pRemainingData, pConnack->remainingLength);
    requires \separated(pConnack, pSessionPresent);
  
    assigns *pSessionPresent;

    behavior badInputA:
        assumes pConnack->remainingLength != ( uint8_t ) 2U;
        ensures *pSessionPresent == \old(*pSessionPresent);
        ensures \result == MQTTBadResponse;
    
    behavior badInputB:
        assumes pConnack->remainingLength == ( uint8_t ) 2U && (pConnack->pRemainingData[0] | 0x01U ) != 0x01U;
        ensures *pSessionPresent == \old(*pSessionPresent);
        ensures \result == MQTTBadResponse;

    behavior other: 
        assumes pConnack->remainingLength == ( uint8_t ) 2U && (pConnack->pRemainingData[0] | 0x01U ) == 0x01U;
        ensures (pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U  ==> *pSessionPresent == true;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] != 0U) ==> \result == MQTTBadResponse;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (pConnack->pRemainingData[ 1 ] > 5U) ==> \result == MQTTBadResponse;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (0U < pConnack->pRemainingData[ 1 ] <= 5U) ==> \result == MQTTServerRefused;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (pConnack->pRemainingData[ 1 ] == 0U) ==> \result == MQTTSuccess;
    
    complete behaviors;
    disjoint behaviors;
*/
static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent );

/*@
    requires is_size_t(statusCount);
    requires is_uint8_array(pStatusStart, statusCount);
 
    assigns \nothing;
*/
static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart);       

static void logConnackResponse( uint8_t responseCode );

#endif                                    
