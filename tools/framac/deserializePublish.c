#include "deserializeFunctions.h"
#include <stdint.h>

// typedef enum MQTTQoS
// {
//     MQTTQoS0 = 0,
//     MQTTQoS1 = 1,
//     MQTTQoS2 = 2
// } MQTTQoS_t;

static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                        uint16_t * const pPacketId,
                                        MQTTPublishInfo_t * const pPublishInfo );

static MQTTStatus_t checkPublishRemainingLength( size_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 size_t qos0Minimum );

/*@
    requires qos == 0 || qos == 1 || qos == 2;
    requires 0 <= remainingLength <= SIZE_MAX; 
    requires 0 <= qos0Minimum <= SIZE_MAX; 
    assigns \nothing;
    ensures qos == 0 && remainingLength < qos0Minimum ==> \result == MQTTBadResponse;
    ensures qos == 0 && remainingLength >= qos0Minimum ==> \result == MQTTSuccess;
    ensures qos != 0 && remainingLength < ( qos0Minimum + 2U ) ==> \result == MQTTBadResponse;
    ensures qos != 0 && remainingLength >= ( qos0Minimum + 2U ) ==> \result == MQTTSuccess;
*/
static MQTTStatus_t checkPublishRemainingLength( size_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 size_t qos0Minimum )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Sanity checks for "Remaining length". */
    if( qos == 0 )
    {
        /* Check that the "Remaining length" is greater than the minimum. */
        if( remainingLength < qos0Minimum )
        {
            LogDebug( ( "QoS 0 PUBLISH cannot have a remaining length less than %lu.",
                        qos0Minimum ) );

            status = MQTTBadResponse;
        }
    }
    else
    {
        /* Check that the "Remaining length" is greater than the minimum. For
         * QoS 1 or 2, this will be two bytes greater than for QoS 0 due to the
         * packet identifier. */
        if( remainingLength < ( qos0Minimum + 2U ) )
        {
            LogDebug( ( "QoS 1 or 2 PUBLISH cannot have a remaining length less than %lu.",
                        qos0Minimum + 2U ) );

            status = MQTTBadResponse;
        }
    }

    return status;
}

// // struct MQTTPacketInfo
// // {
// //     /**
// //      * @brief Type of incoming MQTT packet.
// //      */
// //     uint8_t type;

// //     /**
// //      * @brief Remaining serialized data in the MQTT packet.
// //      */
// //     uint8_t * pRemainingData;

// //     /**
// //      * @brief Length of remaining serialized data.
// //      */
// //     size_t remainingLength;
// // };

// /*@
//     requires \valid(pIncomingPacket);
//     requires \valid(pPacketId);
//     requires \valid(pPublishInfo);


// */
// static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
//                                         uint16_t * const pPacketId,
//                                         MQTTPublishInfo_t * const pPublishInfo )
// {
//     MQTTStatus_t status = MQTTSuccess;

//     // assert( pIncomingPacket != NULL );
//    ((void) sizeof ((pIncomingPacket != ((void *)0)) ? 1 : 0), __extension__ ({ if (
//     pIncomingPacket != ((void *)0)) ; else __assert_fail (
//     "pIncomingPacket != NULL", "mqtt_lightweight.c", 1028, __extension__ __PRETTY_FUNCTION__); }));
//     // assert( pPacketId != NULL );
//     ((void) sizeof ((pPacketId != ((void *)0)) ? 1 : 0), __extension__ ({ if (
//     pPacketId != ((void *)0)) ; else __assert_fail (
//     "pPacketId != NULL", "mqtt_lightweight.c", 1029, __extension__ __PRETTY_FUNCTION__); }));
    
//     // assert( pPublishInfo != NULL );
//     ((void) sizeof ((pPublishInfo != ((void *)0)) ? 1 : 0), __extension__ ({ if (
//     pPublishInfo != ((void *)0)) ; else __assert_fail (
//     "pPublishInfo != NULL", "mqtt_lightweight.c", 1030, __extension__ __PRETTY_FUNCTION__); }));

//     const uint8_t * pVariableHeader = pIncomingPacket->pRemainingData, * pPacketIdentifierHigh;

//     /* The flags are the lower 4 bits of the first byte in PUBLISH. */
//     status = processPublishFlags( ( pIncomingPacket->type & 0x0FU ), pPublishInfo );

//     if( status == MQTTSuccess )
//     {
//         /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
//          * length of at least 3 to accommodate topic name length (2 bytes) and topic
//          * name (at least 1 byte). A QoS 1 or 2 PUBLISH must have a remaining length of
//          * at least 5 for the packet identifier in addition to the topic name length and
//          * topic name. */
//         status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
//                                               pPublishInfo->qos,
//                                               ( 3U ) );
//     }

//     if( status == MQTTSuccess )
//     {

//         /* Extract the topic name starting from the first byte of the variable header.
//          * The topic name string starts at byte 3 in the variable header. */
//         pPublishInfo->topicNameLength = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pVariableHeader ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pVariableHeader ) + 1 ) ) ) );

//         /* Sanity checks for topic name length and "Remaining length". The remaining
//          * length must be at least as large as the variable length header. */
//         status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
//                                               pPublishInfo->qos,
//                                               pPublishInfo->topicNameLength + sizeof( uint16_t ) );
//     }

//     if( status == MQTTSuccess )
//     {
//         /* Parse the topic. */
//         pPublishInfo->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );
        
//         // LogDebug( ( "Topic name length %hu: %.*s",
//         //             pPublishInfo->topicNameLength,
//         //             pPublishInfo->topicNameLength,
//         //             pPublishInfo->pTopicName ) );


//         /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
//          * identifier starts immediately after the topic name. */
//         pPacketIdentifierHigh = ( const uint8_t * ) ( pPublishInfo->pTopicName + pPublishInfo->topicNameLength );

//         if( pPublishInfo->qos > MQTTQoS0 )
//         {
//             *pPacketId = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pPacketIdentifierHigh ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pPacketIdentifierHigh ) + 1 ) ) ) );

//             // LogDebug( ( "Packet identifier %hu.", *pPacketId ) );

//             /* Packet identifier cannot be 0. */
//             if( *pPacketId == 0U )
//             {
//                 status = MQTTBadResponse;
//             }
//         }
//     }

//     if( status == MQTTSuccess )
//     {
//         /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
//          * a packet identifier, but QoS 0 PUBLISH packets do not. */
//         if( pPublishInfo->qos == MQTTQoS0 )
//         {
//             pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - sizeof( uint16_t ) );
//             pPublishInfo->pPayload = pPacketIdentifierHigh;
//         }
//         else
//         {
//             pPublishInfo->payloadLength = ( pIncomingPacket->remainingLength - pPublishInfo->topicNameLength - 2U * sizeof( uint16_t ) );
//             pPublishInfo->pPayload = pPacketIdentifierHigh + sizeof( uint16_t );
//         }

//         // LogDebug( ( "Payload length %hu.", pPublishInfo->payloadLength ) );
//     }

//     return status;
// }
