#include "deserializeFunctions.h"

static MQTTStatus_t deserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                        uint16_t * const pPacketId,
                                        MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pIncomingPacket != NULL );
    assert( pPacketId != NULL );
    assert( pPublishInfo != NULL );
    const uint8_t * pVariableHeader = pIncomingPacket->pRemainingData, * pPacketIdentifierHigh;
    /* The flags are the lower 4 bits of the first byte in PUBLISH. */
    status = processPublishFlags( ( pIncomingPacket->type & 0x0FU ), pPublishInfo );

    if( status == MQTTSuccess )
    {
        /* Sanity checks for "Remaining length". A QoS 0 PUBLISH  must have a remaining
         * length of at least 3 to accommodate topic name length (2 bytes) and topic
         * name (at least 1 byte). A QoS 1 or 2 PUBLISH must have a remaining length of
         * at least 5 for the packet identifier in addition to the topic name length and
         * topic name. */
        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              MQTT_MIN_PUBLISH_REMAINING_LENGTH_QOS0 );
    }

    if( status == MQTTSuccess )
    {
        /* Extract the topic name starting from the first byte of the variable header.
         * The topic name string starts at byte 3 in the variable header. */
        pPublishInfo->topicNameLength = UINT16_DECODE( pVariableHeader );

        /* Sanity checks for topic name length and "Remaining length". The remaining
         * length must be at least as large as the variable length header. */
        status = checkPublishRemainingLength( pIncomingPacket->remainingLength,
                                              pPublishInfo->qos,
                                              pPublishInfo->topicNameLength + sizeof( uint16_t ) );
    }

    if( status == MQTTSuccess )
    {
        /* Parse the topic. */
        pPublishInfo->pTopicName = ( const char * ) ( pVariableHeader + sizeof( uint16_t ) );
        LogDebug( ( "Topic name length %hu: %.*s",
                    pPublishInfo->topicNameLength,
                    pPublishInfo->topicNameLength,
                    pPublishInfo->pTopicName ) );

        /* Extract the packet identifier for QoS 1 or 2 PUBLISH packets. Packet
         * identifier starts immediately after the topic name. */
        pPacketIdentifierHigh = ( const uint8_t * ) ( pPublishInfo->pTopicName + pPublishInfo->topicNameLength );

        if( pPublishInfo->qos > MQTTQoS0 )
        {
           // *pPacketId = UINT16_DECODE( pPacketIdentifierHigh );

            LogDebug( ( "Packet identifier %hu.", *pPacketId ) );

            /* Packet identifier cannot be 0. */
            if( *pPacketId == 0U )
            {
                status = MQTTBadResponse;
            }
        }
    }

    if( status == MQTTSuccess )
    {
        /* Calculate the length of the payload. QoS 1 or 2 PUBLISH packets contain
         * a packet identifier, but QoS 0 PUBLISH packets do not. */
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
