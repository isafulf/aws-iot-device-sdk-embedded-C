#include "mqtt.h"

// NB: ensures (\old(pContext->nextPacketId) + 1 != 0U) ==> (pContext->nextPacketId == \old(pContext->nextPacketId)) + 1;

/*
  requires \valid(pContext);  

  behavior nullpContext:
    assumes pContext == NULL; 
    assigns \nothing; 
    ensures \result == 0U;

  behavior nonNullpContext:
    assumes pContext != NULL; 
    assigns pContext->nextPacketId;  
    ensures \result == \old(pContext->nextPacketId);
    ensures (\old(pContext)->nextPacketId + 1 == 0U) ==> (pContext->nextPacketId == \old(pContext)->nextPacketId + 2);

  complete behaviors;
  disjoint behaviors;  
*/
uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext )
{
    uint16_t packetId = 0U;

    if( pContext != NULL )
    {
        packetId = pContext->nextPacketId++;

        if( pContext->nextPacketId == 0U )
        {
            pContext->nextPacketId++;
        }
    }

    return packetId;
}