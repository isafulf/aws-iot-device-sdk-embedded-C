#include "mqtt.h"
#include "mqtt_utils.h"
#include <stdint.h>

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
remainingLengthEncodedSize - proof done                                       

MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );
remainingLengthEncodedSize - proof done
serializeConnectPacket                                
    encodeString
    assert
    UINT8_SET_BIT
    encodeRemainingLength
    UINT16_HIGH_BYTE

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
  requires 0 <= length <= SIZE_MAX;
  assigns \nothing;

  behavior lengthA:
    assumes length < 128U;
    ensures \result == 1U;

  behavior lengthB:
    assumes 128U <= length < 16384U;
    ensures \result == 2U;

  behavior lengthC:
    assumes 16384U <= length < 2097152U;
    ensures \result == 3U;

  behavior lengthD:
    assumes length >= 2097152U;
    ensures \result == 4U;

  complete behaviors;
  disjoint behaviors;
*/
static size_t remainingLengthEncodedSize( size_t length )
{
    size_t encodedSize;

    /* Determine how many bytes are needed to encode length.
     * The values below are taken from the MQTT 3.1.1 spec. */

    /* 1 byte is needed to encode lengths between 0 and 127. */
    if( length < 128U )
    {
        encodedSize = 1U;
    }
    /* 2 bytes are needed to encode lengths between 128 and 16,383. */
    else if( length < 16384U )
    {
        encodedSize = 2U;
    }
    /* 3 bytes are needed to encode lengths between 16,384 and 2,097,151. */
    else if( length < 2097152U )
    {
        encodedSize = 3U;
    }
    /* 4 bytes are needed to encode lengths between 2,097,152 and 268,435,455. */
    else
    {
        encodedSize = 4U;
    }

    printf( "Encoded size for length =%ul is %ul.", length, encodedSize);

    return encodedSize;
}

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
    ensures 

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
    size_t connectPacketSize = 10UL;

    /* Validate arguments. */
    if( ( pConnectInfo == ((void *)0) ) || ( pRemainingLength == ((void *)0) ) ||
        ( pPacketSize == ((void *)0) ) )
    {
        printf("Argument cannot be NULL: pConnectInfo=%p, ", pConnectInfo);
        printf("pRemainingLength=%p, pPacketSize=%p.",  pRemainingLength, pPacketSize);
        printf("\r\n");
        status = MQTTBadParameter;
    }
    else if( ( pConnectInfo->clientIdentifierLength == 0U ) || ( pConnectInfo->pClientIdentifier == ((void *)0) ) )
    {
        printf( "Mqtt_GetConnectPacketSize() client identifier must be set.");
        status = MQTTBadParameter;
    }
    else
    {
        // 10UL + pConnectInfo->clientIdentifierLength + 
        // sizeof( uint16_t ) + 
        // ( pWillInfo != ((void *)0)) * (pWillInfo->topicNameLength + sizeof( uint16_t ) +
        //                          pWillInfo->payloadLength + sizeof( uint16_t )) + 
        // (pConnectInfo->pUserName != ((void *)0)) * (pConnectInfo->userNameLength + sizeof( uint16_t )) + 
        // (pConnectInfo->pPassword != ((void *)0)) * (pConnectInfo->passwordLength + sizeof( uint16_t )) 
        
        /* Add the length of the client identifier. */
        connectPacketSize += pConnectInfo->clientIdentifierLength + sizeof( uint16_t );

        /* Add the lengths of the will message and topic name if provided. */
        if( pWillInfo != ((void *)0) )
        {
            connectPacketSize += pWillInfo->topicNameLength + sizeof( uint16_t ) +
                                 pWillInfo->payloadLength + sizeof( uint16_t );
        }

        /* Add the lengths of the user name and password if provided. */
        if( pConnectInfo->pUserName != ((void *)0) )
        {
            connectPacketSize += pConnectInfo->userNameLength + sizeof( uint16_t );
        }

        if( pConnectInfo->pPassword != ((void *)0) )
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
        if( connectPacketSize > ( 327700UL ) )
        {
            status = MQTTBadParameter;
        }
        else
        {
            *pRemainingLength = remainingLength;
            *pPacketSize = connectPacketSize;
        }

        printf( "CONNECT packet remaining length=%lu and packet size=%lu.",
                    *pRemainingLength,
                    *pPacketSize);
    }

    return status;
}

/*-----------------------------------------------------------*/

static void serializeConnectPacket( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer )
{
    uint8_t connectFlags = 0U;
    uint8_t * pIndex = NULL;

    assert( pConnectInfo != NULL );
    assert( pBuffer != NULL );

    pIndex = pBuffer->pBuffer;
    /* The first byte in the CONNECT packet is the control packet type. */
    *pIndex = MQTT_PACKET_TYPE_CONNECT;
    pIndex++;

    /* The remaining length of the CONNECT packet is encoded starting from the
     * second byte. The remaining length does not include the length of the fixed
     * header or the encoding of the remaining length. */
    pIndex = encodeRemainingLength( pIndex, remainingLength );

    /* The string "MQTT" is placed at the beginning of the CONNECT packet's variable
     * header. This string is 4 bytes long. */
    pIndex = encodeString( pIndex, "MQTT", 4 );

    /* The MQTT protocol version is the second field of the variable header. */
    *pIndex = MQTT_VERSION_3_1_1;
    pIndex++;

    /* Set the clean session flag if needed. */
    if( pConnectInfo->cleanSession == true )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_CLEAN );
    }

    /* Set the flags for username and password if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_USERNAME );
    }

    if( pConnectInfo->pPassword != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_PASSWORD );
    }

    /* Set will flag if a Last Will and Testament is provided. */
    if( pWillInfo != NULL )
    {
        UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL );

        /* Flags only need to be changed for Will QoS 1 or 2. */
        if( pWillInfo->qos == MQTTQoS1 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS1 );
        }
        else if( pWillInfo->qos == MQTTQoS2 )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_QOS2 );
        }
        else
        {
            /* Empty else MISRA 15.7 */
        }

        if( pWillInfo->retain == true )
        {
            UINT8_SET_BIT( connectFlags, MQTT_CONNECT_FLAG_WILL_RETAIN );
        }
    }

    *pIndex = connectFlags;
    pIndex++;

    /* Write the 2 bytes of the keep alive interval into the CONNECT packet. */
    *pIndex = UINT16_HIGH_BYTE( pConnectInfo->keepAliveSeconds );
    *( pIndex + 1 ) = UINT16_LOW_BYTE( pConnectInfo->keepAliveSeconds );
    pIndex += 2;

    /* Write the client identifier into the CONNECT packet. */
    pIndex = encodeString( pIndex,
                           pConnectInfo->pClientIdentifier,
                           pConnectInfo->clientIdentifierLength );

    /* Write the will topic name and message into the CONNECT packet if provided. */
    if( pWillInfo != NULL )
    {
        pIndex = encodeString( pIndex,
                               pWillInfo->pTopicName,
                               pWillInfo->topicNameLength );

        pIndex = encodeString( pIndex,
                               pWillInfo->pPayload,
                               ( uint16_t ) pWillInfo->payloadLength );
    }

    /* Encode the user name if provided. */
    if( pConnectInfo->pUserName != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pUserName, pConnectInfo->userNameLength );
    }

    /* Encode the password if provided. */
    if( pConnectInfo->pPassword != NULL )
    {
        pIndex = encodeString( pIndex, pConnectInfo->pPassword, pConnectInfo->passwordLength );
    }

    printf( "Length of serialized CONNECT packet is %lu.",
                ( size_t ) ( pIndex - pBuffer->pBuffer ));

    /* Ensure that the difference between the end and beginning of the buffer
     * is less than the buffer size. */
    assert( ( ( size_t ) ( pIndex - pBuffer->pBuffer ) ) <= pBuffer->size );
}

// /*-----------------------------------------------------------*/

// MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
//                                     const MQTTPublishInfo_t * const pWillInfo,
//                                     size_t remainingLength,
//                                     const MQTTFixedBuffer_t * const pBuffer )
// {
//     MQTTStatus_t status = MQTTSuccess;

//     /* Calculate CONNECT packet size. */
//     size_t connectPacketSize = remainingLength + remainingLengthEncodedSize( remainingLength ) + 1U;

//     /* Validate arguments. */
//     if( ( pConnectInfo == NULL ) || ( pBuffer == NULL ) )
//     {
//         printf( ( "Argument cannot be NULL: pConnectInfo=%p, "
//                     "pBuffer=%p.",
//                     pConnectInfo,
//                     pBuffer ) );
//         status = MQTTBadParameter;
//     }
//     /* Check that the full packet size fits within the given buffer. */
//     else if( connectPacketSize > pBuffer->size )
//     {
//         printf( ( "Buffer size of %lu is not sufficient to hold "
//                     "serialized CONNECT packet of size of %lu.",
//                     pBuffer->size,
//                     connectPacketSize ) );
//         status = MQTTNoMemory;
//     }
//     else if( ( pWillInfo != NULL ) && ( pWillInfo->pTopicName == NULL ) )
//     {
//         printf( ( "pWillInfo->pTopicName cannot be NULL if Will is present." ) );
//         status = MQTTBadParameter;
//     }
//     else
//     {
//         serializeConnectPacket( pConnectInfo,
//                                 pWillInfo,
//                                 remainingLength,
//                                 pBuffer );
//     }

//     return status;
// }

// /*-----------------------------------------------------------*/

// static MQTTStatus_t receiveConnack( MQTTContext_t * const pContext,
//                                     uint32_t timeoutMs,
//                                     MQTTPacketInfo_t * const pIncomingPacket,
//                                     bool * const pSessionPresent )
// {
//     MQTTStatus_t status = MQTTSuccess;
//     MQTTGetCurrentTimeFunc_t getTimeStamp = NULL;
//     uint32_t entryTimeMs = 0U, remainingTimeMs = 0U, timeTakenMs = 0U;

//     assert( pContext != NULL );
//     assert( pIncomingPacket != NULL );
//     assert( pContext->callbacks.getTime != NULL );

//     getTimeStamp = pContext->callbacks.getTime;
//     /* Get the entry time for the function. */
//     entryTimeMs = getTimeStamp();

//     do
//     {
//         /* Transport read for incoming CONNACK packet type and length.
//          * MQTT_GetIncomingPacketTypeAndLength is a blocking call and it is
//          * returned after a transport receive timeout, an error, or a successful
//          * receive of packet type and length. */
//         status = MQTT_GetIncomingPacketTypeAndLength( pContext->transportInterface.recv,
//                                                       pContext->transportInterface.networkContext,
//                                                       pIncomingPacket );

//         /* Loop until there is data to read or if the timeout has not expired. */
//     } while( ( status == MQTTNoDataAvailable ) &&
//              ( calculateElapsedTime( getTimeStamp(), entryTimeMs ) < timeoutMs ) );

//     if( status == MQTTSuccess )
//     {
//         /* Time taken in this function so far. */
//         timeTakenMs = calculateElapsedTime( getTimeStamp(), entryTimeMs );

//         if( timeTakenMs < timeoutMs )
//         {
//             /* Calculate remaining time for receiving the remainder of
//              * the packet. */
//             remainingTimeMs = timeoutMs - timeTakenMs;
//         }

//         /* Reading the remainder of the packet by transport recv.
//          * Attempt to read once even if the timeout has expired at this point.
//          * Invoking receivePacket with remainingTime as 0 would attempt to
//          * recv from network once.*/
//         if( pIncomingPacket->type == MQTT_PACKET_TYPE_CONNACK )
//         {
//             status = receivePacket( pContext,
//                                     *pIncomingPacket,
//                                     remainingTimeMs );
//         }
//         else
//         {
//             printf( ( "Incorrect packet type %X received while expecting"
//                         " CONNACK(%X).",
//                         pIncomingPacket->type,
//                         MQTT_PACKET_TYPE_CONNACK ) );
//             status = MQTTBadResponse;
//         }
//     }

//     if( status == MQTTSuccess )
//     {
//         /* Update the packet info pointer to the buffer read. */
//         pIncomingPacket->pRemainingData = pContext->networkBuffer.pBuffer;

//         /* Deserialize CONNACK. */
//         status = MQTT_DeserializeAck( pIncomingPacket, NULL, pSessionPresent );
//     }

//     if( status != MQTTSuccess )
//     {
//         printf( ( "CONNACK recv failed with status = %u.",
//                     status ) );
//     }
//     else
//     {
//         printf( ( "Received MQTT CONNACK successfully from broker." ) );
//     }

//     return status;
// }

// /*-----------------------------------------------------------*/

// static int32_t sendPacket( MQTTContext_t * pContext,
//                            const uint8_t * pBufferToSend,
//                            size_t bytesToSend )
// {
//     const uint8_t * pIndex = pBufferToSend;
//     size_t bytesRemaining = bytesToSend;
//     int32_t totalBytesSent = 0, bytesSent;
//     uint32_t sendTime = 0U;

//     assert( pContext != NULL );
//     assert( bytesToSend != 0 );

//     /* Record the time of transmission. */
//     sendTime = pContext->callbacks.getTime();
//     bytesRemaining = bytesToSend;

//     /* Loop until the entire packet is sent. */
//     while( bytesRemaining > 0UL )
//     {
//         bytesSent = pContext->transportInterface.send( pContext->transportInterface.networkContext,
//                                                        pIndex,
//                                                        bytesRemaining );

//         if( bytesSent > 0 )
//         {
//             bytesRemaining -= ( size_t ) bytesSent;
//             totalBytesSent += bytesSent;
//             pIndex += bytesSent;
//             printf( ( "Bytes sent=%d, bytes remaining=%ul,"
//                         "total bytes sent=%d.",
//                         bytesSent,
//                         bytesRemaining,
//                         totalBytesSent ) );
//         }
//         else
//         {
//             printf( ( "Transport send failed." ) );
//             totalBytesSent = -1;
//             break;
//         }
//     }

//     /* Update time of last transmission if the entire packet was successfully sent. */
//     if( totalBytesSent > -1 )
//     {
//         pContext->lastPacketTime = sendTime;
//         printf( ( "Successfully sent packet at time %u.",
//                     sendTime ) );
//     }

//     return totalBytesSent;
// }

// /*-----------------------------------------------------------*/

// MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
//                            const MQTTConnectInfo_t * const pConnectInfo,
//                            const MQTTPublishInfo_t * const pWillInfo,
//                            uint32_t timeoutMs,
//                            bool * const pSessionPresent )
// {
//     size_t remainingLength = 0UL, packetSize = 0UL;
//     int32_t bytesSent;
//     MQTTStatus_t status = MQTTSuccess;
//     MQTTPacketInfo_t incomingPacket = { .type = ( ( uint8_t ) 0 ) };

//     if( ( pContext == NULL ) || ( pConnectInfo == NULL ) || ( pSessionPresent == NULL ) )
//     {
//         printf( ( "Argument cannot be NULL: pContext=%p, "
//                     "pConnectInfo=%p, pSessionPresent=%p.",
//                     pContext,
//                     pConnectInfo,
//                     pSessionPresent ) );
//         status = MQTTBadParameter;
//     }

//     if( status == MQTTSuccess )
//     {
//         /* Get MQTT connect packet size and remaining length. */
//         status = MQTT_GetConnectPacketSize( pConnectInfo,
//                                             pWillInfo,
//                                             &remainingLength,
//                                             &packetSize );
//         printf( ( "CONNECT packet size is %lu and remaining length is %lu.",
//                     packetSize,
//                     remainingLength ) );
//     }

//     if( status == MQTTSuccess )
//     {
//         status = MQTT_SerializeConnect( pConnectInfo,
//                                         pWillInfo,
//                                         remainingLength,
//                                         &( pContext->networkBuffer ) );
//     }

//     if( status == MQTTSuccess )
//     {
//         bytesSent = sendPacket( pContext,
//                                 pContext->networkBuffer.pBuffer,
//                                 packetSize );

//         if( bytesSent < 0 )
//         {
//             LogError( ( "Transport send failed for CONNECT packet." ) );
//             status = MQTTSendFailed;
//         }
//         else
//         {
//             LogDebug( ( "Sent %d bytes of CONNECT packet.",
//                         bytesSent ) );
//         }
//     }

//     /* Read CONNACK from transport layer. */
//     if( status == MQTTSuccess )
//     {
//         status = receiveConnack( pContext,
//                                  timeoutMs,
//                                  &incomingPacket,
//                                  pSessionPresent );
//     }

//     if( status == MQTTSuccess )
//     {
//         printf( ( "MQTT connection established with the broker." ) );
//         pContext->connectStatus = MQTTConnected;
//     }
//     else
//     {
//         printf( ( "MQTT connection failed with status = %u.",
//                     status ) );
//     }

//     return status;
// }
