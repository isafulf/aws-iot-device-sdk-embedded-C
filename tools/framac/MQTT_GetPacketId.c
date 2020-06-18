#include "mqtt.h"

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