#include "mqtt.h"

#define size_t MQTT_PACKET_CONNECT_HEADER_SIZE = 0

/*
MQTT_Connect:
From mqtt_lightweight.c:
MQTT_GetConnectPacketSize 
MQTT_SerializeConnect

From mqtt.c:
sendPacket
receiveConnack

MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );
remainingLengthEncodedSize
serializeConnectPacket                                

static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const pIncomingPacket,
                                    bool * const pSessionPresent );
assert -- in MQTT_utils
MQTT_GetIncomingPacketTypeAndLength   
calculateElapsedTime  
getTimeStamp       
receivePacket               
MQTT_DeserializeAck

static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend );
assert -- in MQTT_utils
getTime
send

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           uint32_t timeoutMs,
                           bool * const pSessionPresent );                        

*/


/*@
  requires \valid(pConnectInfo);
  requires \valid(pWillInfo);
  requires \valid(pRemainingLength);
  requires \valid(pPacketSize);

  requires \separated(pConnectInfo, pWillInfo, pRemainingLength, pPacketSize);

  behavior nullInput:
    assumes pConnectInfo == NULL || pRemainingLength == NULL || pPacketSize == NULL || 
      pConnectInfo->clientIdentifierLength == 0U  || pConnectInfo->pClientIdentifier == NULL;
    assigns \nothing;
    ensures \result == MQTTBadParameter;

  behavior nonNullInput:
    assumes pConnectInfo != NULL && pRemainingLength != NULL && pPacketSize != NULL &&
      (pConnectInfo->clientIdentifierLength != 0U  && pConnectInfo->pClientIdentifier != NULL);

  complete behaviors;
  disjoint behaviors;

*/
MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize )
{
    MQTTStatus_t status = MQTTSuccess;
    size_t remainingLength;

    /* The CONNECT packet will always include a 10-byte variable header. */
    size_t connectPacketSize = MQTT_PACKET_CONNECT_HEADER_SIZE;

    /* Validate arguments. */
    if( ( pConnectInfo == NULL ) || ( pRemainingLength == NULL ) ||
        ( pPacketSize == NULL ) )
    {
        printf( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pRemainingLength=%p, pPacketSize=%p.",
                    pConnectInfo,
                    pRemainingLength,
                    pPacketSize ) );
        status = MQTTBadParameter;
    }
    else if( ( pConnectInfo->clientIdentifierLength == 0U ) || ( pConnectInfo->pClientIdentifier == NULL ) )
    {
        printf( ( "Mqtt_GetConnectPacketSize() client identifier must be set." ) );
        status = MQTTBadParameter;
    }
    else
    {
        /* Add the length of the client identifier. */
        connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );

        /* Add the lengths of the will message and topic name if provided. */
        if( pWillInfo != NULL )
        {
            connectPacketSize += pWillInfo->topicNameLength + sizeof( uint16_t ) +
                                 pWillInfo->payloadLength + sizeof( uint16_t );
        }

        /* Add the lengths of the user name and password if provided. */
        if( pConnectInfo->pUserName != NULL )
        {
            connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
        }

        if( pConnectInfo->pPassword != NULL )
        {
            connectPacketSize += pConnectInfo->passwordLength + sizeof( uint16_t );
        }

        /* At this point, the "Remaining Length" field of the MQTT CONNECT packet has
         * been calculated. */
        remainingLength = connectPacketSize;

        /* Calculate the full size of the MQTT CONNECT packet by adding the size of
         * the "Remaining Length" field plus 1 byte for the "Packet Type" field. */
        connectPacketSize += 1U + remainingLengthEncodedSize( connectPacketSize );

        /* Check that the CONNECT packet is within the bounds of the MQTT spec. */
        if( connectPacketSize > MQTT_PACKET_CONNECT_MAX_SIZE )
        {
            status = MQTTBadParameter;
        }
        else
        {
            *pRemainingLength = remainingLength;
            *pPacketSize = connectPacketSize;
        }

        printf( ( "CONNECT packet remaining length=%lu and packet size=%lu.",
                    *pRemainingLength,
                    *pPacketSize ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    MQTTStatus_t status = MQTTSuccess;

    /* Calculate CONNECT packet size. */
    size_t connectPacketSize = remainingLength + remainingLengthEncodedSize( remainingLength ) + 1U;

    /* Validate arguments. */
    if( ( pConnectInfo == NULL ) || ( pBuffer == NULL ) )
    {
        printf( ( "Argument cannot be NULL: pConnectInfo=%p, "
                    "pBuffer=%p.",
                    pConnectInfo,
                    pBuffer ) );
        status = MQTTBadParameter;
    }
    /* Check that the full packet size fits within the given buffer. */
    else if( connectPacketSize > pBuffer->size )
    {
        printf( ( "Buffer size of %lu is not sufficient to hold "
                    "serialized CONNECT packet of size of %lu.",
                    pBuffer->size,
                    connectPacketSize ) );
        status = MQTTNoMemory;
    }
    else if( ( pWillInfo != NULL ) && ( pWillInfo->pTopicName == NULL ) )
    {
        printf( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
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

/*-----------------------------------------------------------*/

static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
                                    uint32_t timeoutMs,
                                    MQTTPacketInfo_t * const pIncomingPacket,
                                    bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;
    MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
    uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;

    assert( pContext != NULL );
    assert( pIncomingPacket != NULL );
    assert( pContext->callbacks.getTime != NULL );

    getTimeStamp = pContext->callbacks.getTime;
    /* Get the entry time for the function. */
    entryTimeMs = getTimeStamp();

    do
    {
        /* Transport read for incoming CONNACK packet type and length.
         * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
         * returned after a transport receive timeout, an error, or a successful
         * receive of packet type and length. */
        status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
                                                      pContext->transportInterface.networkContext,
                                                      pIncomingPacket );

        /* Loop until there is data to read or if the timeout has not expired. */
    } while( ( status == MQTTNoDataAvailable ) &&
             ( calculateElapsedTime( getTimeStamp(), entryTimeMs ) < timeoutMs ) );

    if( status == MQTTSuccess )
    {
        /* Time taken in this function so far. */
        timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

        if( timeTakenMs < timeoutMs )
        {
            /* Calculate remaining time for receiving the remainder of
             * the packet. */
            remainingTimeMs = timeoutMs - timeTakenMs;
        }

        /* Reading the remainder of the packet by transport recv.
         * Attempt to read once even if the timeout has expired at this point.
         * Invoking receivePacket with remainingTime as 0 would attempt to
         * recv from network once.*/
        if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = receivePacket( pContext,
                                    *pIncomingPacket,
                                    remainingTimeMs );
        }
        else
        {
            printf( ( "Incorrect packet type %X received while expecting"
                        " CONNACK(%X).",
                        pIncomingPacket->type,
                        MQTT_PACKET_TYPE_CONNACK ) );
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        /* Update the packet info pointer to the buffer read. */
        pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

        /* Deserialize CONNACK. */
        status = MQTT_DeserializeAck( pIncomingPacket, NULL, pSessionPresent );
    }

    if( status != MQTTSuccess )
    {
        printf( ( "CONNACK recv failed with status = %u.",
                    status ) );
    }
    else
    {
        printf( ( "Received MQTT CONNACK successfully from broker." ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pBufferToSend,
                           size_t bytesToSend )
{
    const uint8_t * pIndex = pBufferToSend;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0, bytesSent;
    uint32_t sendTime = 0U;

    assert( pContext != NULL );
    assert( bytesToSend != 0 );

    /* Record the time of transmission. */
    sendTime = pContext->callbacks.getTime();
    bytesRemaining = bytesToSend;

    /* Loop until the entire packet is sent. */
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
            printf( ( "Bytes sent=%d, bytes remaining=%ul,"
                        "total bytes sent=%d.",
                        bytesSent,
                        bytesRemaining,
                        totalBytesSent ) );
        }
        else
        {
            printf( ( "Transport send failed." ) );
            totalBytesSent = -1;
            break;
        }
    }

    /* Update time of last transmission if the entire packet was successfully sent. */
    if( totalBytesSent > -1 )
    {
        pContext->lastPacketTime = sendTime;
        printf( ( "Successfully sent packet at time %u.",
                    sendTime ) );
    }

    return totalBytesSent;
}

/*-----------------------------------------------------------*/

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

    if( ( pContext == NULL ) || ( pConnectInfo == NULL ) || ( pSessionPresent == NULL ) )
    {
        printf( ( "Argument cannot be NULL: pContext=%p, "
                    "pConnectInfo=%p, pSessionPresent=%p.",
                    pContext,
                    pConnectInfo,
                    pSessionPresent ) );
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get MQTT connect packet size and remaining length. */
        status = MQTT_GetConnectPacketSize( pConnectInfo,
                                            pWillInfo,
                                            &remainingLength,
                                            &packetSize );
        printf( ( "CONNECT packet size is %lu and remaining length is %lu.",
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

    /* Read CONNACK from transport layer. */
    if( status == MQTTSuccess )
    {
        status = receiveConnack( pContext,
                                 timeoutMs,
                                 &incomingPacket,
                                 pSessionPresent );
    }

    if( status == MQTTSuccess )
    {
        printf( ( "MQTT connection established with the broker." ) );
        pContext->connectStatus = MQTTConnected;
    }
    else
    {
        printf( ( "MQTT connection failed with status = %u.",
                    status ) );
    }

    return status;
}
