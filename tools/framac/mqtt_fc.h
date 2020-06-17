#ifndef MQTT_FC_H
#define MQTT_FC_H

#include "mqtt.h"

/*@
 assigns \nothing;
*/
extern void *memset(void *__s, int __c, size_t __n)
    __attribute__((__nothrow__, __leaf__)) __attribute__((__nonnull__(1)));

extern int printf(const char *__restrict __format, ...);

/*@
  requires \valid(pContext);
  requires \valid(pTransportInterface);
  requires \valid(pCallbacks);
  requires \valid(pNetworkBuffer);

  requires \separated(pContext, pTransportInterface, pCallbacks, pNetworkBuffer);
  
  behavior nullInput:
    assumes pContext == ((void *)0) || pTransportInterface == ((void *)0) || pCallbacks == ((void *)0) || pNetworkBuffer == ((void *)0); 

    assigns \nothing;
    
    ensures \result == MQTTBadParameter;

  behavior nonNullInput:
    assumes pContext != ((void *)0) && pTransportInterface != ((void *)0) && pCallbacks != ((void *)0) && pNetworkBuffer != ((void *)0);

    assigns pContext->connectStatus;
    assigns pContext->transportInterface;
    assigns pContext->callbacks;
    assigns pContext->networkBuffer;
    assigns pContext->nextPacketId;

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


// NB:     ensures (\old(pContext->nextPacketId) + 1 != 0U) ==> (pContext->nextPacketId == \old(pContext->nextPacketId)) + 1;

/*@
  requires \valid(pContext);  

  behavior nullpContext:
    assumes pContext == NULL; 
    assigns \nothing; 
    ensures \result == 0U;

  behavior nonNullpContext:
    assumes pContext != NULL; 
    assigns pContext->nextPacketId;  
    ensures \result == \old(pContext->nextPacketId);
    ensures pContext->nextPacketId != 0;

  complete behaviors;
  disjoint behaviors;  
*/
uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext );


                        
#endif