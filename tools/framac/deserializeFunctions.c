#include "deserializeFunctions.h"

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == NULL ) || ( pPacketId == NULL ) || ( pPublishInfo == NULL ) )
    {
        LogError( ( "Argument cannot be NULL: pIncomingPacket=%p, "
                    "pPacketId=%p, pPublishInfo=%p",
                    pIncomingPacket,
                    pPacketId,
                    pPublishInfo ) );
        status = MQTTBadParameter;
    }
    else if( ( pIncomingPacket->type & 0xF0U ) != MQTT_PACKET_TYPE_PUBLISH )
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
            //*pPacketId = UINT16_DECODE( pPacketIdentifierHigh );

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

static MQTTStatus_t processPublishFlags( uint8_t publishFlags,
                                         MQTTPublishInfo_t * const pPublishInfo )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pPublishInfo != NULL );

    /* Check for QoS 2. */
    if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS2 ) )
    {
        /* PUBLISH packet is invalid if both QoS 1 and QoS 2 bits are set. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
        {
            LogDebug( ( "Bad QoS: 3." ) );

            status = MQTTBadResponse;
        }
        else
        {
            pPublishInfo->qos = MQTTQoS2;
        }
    }
    /* Check for QoS 1. */
    else if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_QOS1 ) )
    {
        pPublishInfo->qos = MQTTQoS1;
    }
    /* If the PUBLISH isn't QoS 1 or 2, then it's QoS 0. */
    else
    {
        pPublishInfo->qos = MQTTQoS0;
    }

    if( status == MQTTSuccess )
    {
        LogDebug( ( "QoS is %d.", pPublishInfo->qos ) );

        /* Parse the Retain bit. */
        pPublishInfo->retain = UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_RETAIN );

        LogDebug( ( "Retain bit is %d.", pPublishInfo->retain ) );

        /* Parse the DUP bit. */
        if( UINT8_CHECK_BIT( publishFlags, MQTT_PUBLISH_FLAG_DUP ) )
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

static MQTTStatus_t checkPublishRemainingLength( size_t remainingLength,
                                                 MQTTQoS_t qos,
                                                 size_t qos0Minimum )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Sanity checks for "Remaining length". */
    if( qos == MQTTQoS0 )
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

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    if( ( pIncomingPacket == NULL ) )
    {
        LogError( ( "pIncomingPacket cannot be NULL." ) );
        status = MQTTBadParameter;
    }

    /* Pointer for packet identifier cannot be NULL for packets other than
     * CONNACK and PINGRESP. */
    else if( ( pPacketId == NULL ) &&
             ( ( pIncomingPacket->type != MQTT_PACKET_TYPE_CONNACK ) &&
               ( pIncomingPacket->type != MQTT_PACKET_TYPE_PINGRESP ) ) )
    {
        LogError( ( "pPacketId cannot be NULL for packet type %02x.",
                    pIncomingPacket->type ) );
        status = MQTTBadParameter;
    }
    /* Pointer for session present cannot be NULL for CONNACK. */
    else if( ( pSessionPresent == NULL ) &&
             ( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK ) )
    {
        LogError( ( "pSessionPresent cannot be NULL for CONNACK packet." ) );
        status = MQTTBadParameter;
    }
    else if( pIncomingPacket->pRemainingData == NULL )
    {
        LogError( ( "Remaining data of incoming packet is NULL." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Make sure response packet is a valid ack. */
        switch( pIncomingPacket->type )
        {
            case MQTT_PACKET_TYPE_CONNACK:
                status = deserializeConnack( pIncomingPacket, pSessionPresent );
                break;

            case MQTT_PACKET_TYPE_SUBACK:
                status = deserializeSuback( pIncomingPacket, pPacketId );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:
                status = deserializePingresp( pIncomingPacket );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
            case MQTT_PACKET_TYPE_PUBACK:
            case MQTT_PACKET_TYPE_PUBREC:
            case MQTT_PACKET_TYPE_PUBREL:
            case MQTT_PACKET_TYPE_PUBCOMP:
                status = deserializeSimpleAck( pIncomingPacket, pPacketId );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "IotMqtt_DeserializeResponse() called with unknown packet type:(%02x).", pIncomingPacket->type ) );
                status = MQTTBadResponse;
                break;
        }
    }

    return status;
}

static MQTTStatus_t deserializeSimpleAck( const MQTTPacketInfo_t * const pAck,
                                          uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pAck != NULL );
    assert( pPacketIdentifier != NULL );

    /* Check that the "Remaining length" of the received ACK is 2. */
    if( pAck->remainingLength != MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH )
    {
        LogError( ( "ACK does not have remaining length of %d.",
                    MQTT_PACKET_SIMPLE_ACK_REMAINING_LENGTH ) );

        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (third and fourth bytes) from ACK. */
        *pPacketIdentifier = UINT16_DECODE( pAck->pRemainingData );

        LogDebug( ( "Packet identifier %hu.", *pPacketIdentifier ) );

        /* Packet identifier cannot be 0. */
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

    assert( pPingresp != NULL );

    /* Check the "Remaining length" (second byte) of the received PINGRESP is 0. */
    if( pPingresp->remainingLength != MQTT_PACKET_PINGRESP_REMAINING_LENGTH )
    {
        LogError( ( "PINGRESP does not have remaining length of %d.",
                    MQTT_PACKET_PINGRESP_REMAINING_LENGTH ) );

        status = MQTTBadResponse;
    }

    return status;
}

static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    assert( pStatusStart != NULL );

    /* Iterate through each status byte in the SUBACK packet. */
    /*@
        loop invariant 0 <= i <= statusCount;
        loop assigns i, subscriptionStatus, status;
        loop variant statusCount - i;
    */
    for( i = 0; i < statusCount; i++ )
    {
        /* Read a single status byte in SUBACK. */
        subscriptionStatus = pStatusStart[ i ];

        /* MQTT 3.1.1 defines the following values as status codes. */
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

                /* Application should remove subscription from the list */
                status = MQTTServerRefused;

                break;

            default:
                LogDebug( ( "Bad SUBSCRIBE status %hhu.", subscriptionStatus ) );

                status = MQTTBadResponse;

                break;
        }

        /* Stop parsing the subscription statuses if a bad response was received. */
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

    assert( pSuback != NULL );
    assert( pPacketIdentifier != NULL );

    size_t remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;

    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    if( remainingLength < 3U )
    {
        LogDebug( ( "SUBACK cannot have a remaining length less than 3." ) );
        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (first 2 bytes of variable header) from SUBACK. */
        *pPacketIdentifier = UINT16_DECODE( pVariableHeader );

        LogDebug( ( "Packet identifier %hu.", *pPacketIdentifier ) );

        status = readSubackStatus( remainingLength - sizeof( uint16_t ),
                                   pVariableHeader + sizeof( uint16_t ) );
    }

    return status;
}

static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    assert( pConnack != NULL );
    assert( pSessionPresent != NULL );
    const uint8_t * pRemainingData = pConnack->pRemainingData;

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    if( pConnack->remainingLength != MQTT_PACKET_CONNACK_REMAINING_LENGTH )
    {
        LogError( ( "CONNACK does not have remaining length of %d.",
                    MQTT_PACKET_CONNACK_REMAINING_LENGTH ) );

        status = MQTTBadResponse;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        LogError( ( "Reserved bits in CONNACK incorrect." ) );

        status = MQTTBadResponse;
    }
    else
    {
        /* Determine if the "Session Present" bit is set. This is the lowest bit of
         * the second byte in CONNACK. */
        if( ( pRemainingData[ 0 ] & MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
            == MQTT_PACKET_CONNACK_SESSION_PRESENT_MASK )
        {
            LogWarn( ( "CONNACK session present bit set." ) );
            *pSessionPresent = true;

            /* MQTT 3.1.1 specifies that the fourth byte in CONNACK must be 0 if the
             * "Session Present" bit is set. */
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
        /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
        if( pRemainingData[ 1 ] > 5U )
        {
            LogError( ( "CONNACK response %hhu is not valid.",
                        pRemainingData[ 1 ] ) );

            status = MQTTBadResponse;
        }
        else
        {
            /* Print the appropriate message for the CONNACK response code if logs are
             * enabled. */
            logConnackResponse( pRemainingData[ 1 ] );

            /* A nonzero CONNACK response code means the connection was refused. */
            if( pRemainingData[ 1 ] > 0U )
            {
                status = MQTTServerRefused;
            }
        }
    }

    return status;
}
