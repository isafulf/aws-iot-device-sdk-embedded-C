#ifndef OTHER_FUNCTIONS_H
#define OTHER_FUNCTIONS_H

#include "mqtt_lightweight.h"

#define MQTT_STATE_ARRAY_MAX_COUNT          10U

struct MQTTApplicationCallbacks;
typedef struct MQTTApplicationCallbacks   MQTTApplicationCallbacks_t;

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo             MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext                MQTTContext_t;

struct MQTTTransportInterface;
typedef struct MQTTTransportInterface     MQTTTransportInterface_t;

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
    MQTTPubAckInfo_t outgoingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];
    size_t outgoingPublishCount;
    MQTTPubAckInfo_t incomingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];
    size_t incomingPublishCount;

    MQTTTransportInterface_t transportInterface;
    MQTTFixedBuffer_t networkBuffer;

    uint16_t nextPacketId;
    MQTTConnectionStatus_t connectStatus;
    MQTTApplicationCallbacks_t callbacks;
    uint32_t lastPacketTime;
    bool controlPacketSent;

    /* Keep alive members. */
    uint16_t keepAliveIntervalSec;
    uint32_t pingReqSendTimeMs;
    uint32_t pingRespTimeoutMs;
    bool waitingForPingResp;
};

/**
 * @brief Initialize an MQTT context.
 *
 * This function must be called on an MQTT context before any other function.
 *
 * @brief param[in] pContext The context to initialize.
 * @brief param[in] pTransportInterface The transport interface to use with the context.
 * @brief param[in] pCallbacks Callbacks to use with the context.
 * @brief param[in] pNetworkBuffer Network buffer provided for the context.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */

/*@
  requires \valid(pContext);
  requires \valid(pTransportInterface);
  requires \valid(pCallbacks);
  requires \valid(pNetworkBuffer);
  requires \separated(pContext, pTransportInterface, pCallbacks, pNetworkBuffer);

  assigns pContext->connectStatus;
  assigns pContext->transportInterface;
  assigns pContext->callbacks;
  assigns pContext->networkBuffer;
  assigns pContext->nextPacketId;
  
  behavior nullInput:
    assumes pContext == ((void *)0) || pTransportInterface == ((void *)0) || pCallbacks == ((void *)0) || pNetworkBuffer == ((void *)0); 
    ensures pContext->connectStatus == \old(pContext->connectStatus);
    ensures pContext->transportInterface == \old(pContext->transportInterface);
    ensures pContext->callbacks == \old(pContext->callbacks);
    ensures pContext->networkBuffer == \old(pContext->networkBuffer);
    ensures pContext->nextPacketId == \old(pContext->nextPacketId);
    ensures \result == MQTTBadParameter;

  behavior nonNullInput:
    assumes pContext != ((void *)0) && pTransportInterface != ((void *)0) && pCallbacks != ((void *)0) && pNetworkBuffer != ((void *)0);
    ensures pContext->connectStatus == MQTTNotConnected;
    ensures pContext->transportInterface == *pTransportInterface;
    ensures pContext->callbacks == *pCallbacks;
    ensures pContext->networkBuffer == *pNetworkBuffer;
    ensures pContext->nextPacketId == 1;
    ensures \result == MQTTSuccess;

  complete behaviors;
  disjoint behaviors;  
*/
MQTTStatus_t MQTT_Init( MQTTContext_t * const pContext,
                        const MQTTTransportInterface_t * const pTransportInterface,
                        const MQTTApplicationCallbacks_t * const pCallbacks,
                        const MQTTFixedBuffer_t * const pNetworkBuffer );

/*@
  requires \valid(pContext);
  requires 0U <= pContext->nextPacketId <= ~0U;

  assigns pContext->nextPacketId;  

  behavior nullpContext:
    assumes pContext == NULL; 
    ensures pContext->nextPacketId == \old(pContext->nextPacketId); 
    ensures \result == 0U;

  behavior nonNullpContext:
    assumes pContext != NULL; 
    ensures \result == \old(pContext->nextPacketId);
    ensures ((\old(pContext->nextPacketId) + 1) % (1<<16) != 0U) ==> (pContext->nextPacketId == (\old(pContext->nextPacketId) + 1) % (1<<16));
    ensures ((\old(pContext->nextPacketId) + 1) % (1<<16) == 0U) ==> (pContext->nextPacketId == (\old(pContext->nextPacketId) + 2) % (1<<16));

  complete behaviors;
  disjoint behaviors;  
*/
uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext );

#endif /* ifndef OTHER_FUNCTIONS_H */