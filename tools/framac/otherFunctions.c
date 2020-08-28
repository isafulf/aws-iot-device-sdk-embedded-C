#include "otherFunctions.h"
#include "mqtt_utils.h"
    
MQTTStatus_t
MQTT_Init(MQTTContext_t *const pContext,
          const MQTTTransportInterface_t *const pTransportInterface,
          const MQTTApplicationCallbacks_t *const pCallbacks,
          const MQTTFixedBuffer_t *const pNetworkBuffer) {
  MQTTStatus_t status = MQTTSuccess;

  if ((pContext == ((void *)0)) || (pTransportInterface == ((void *)0)) ||
      (pCallbacks == ((void *)0)) || (pNetworkBuffer == ((void *)0))) {
    printf("[ERROR] [%s] "
           "[%s:%d] ",
           "MQTT", "init.c", 19);
    printf("Argument cannot be NULL: pContext=%p, "
           "pTransportInterface=%p "
           "pCallbacks=%p "
           "pNetworkBuffer=%p.",
           pContext, pTransportInterface, pCallbacks, pNetworkBuffer);
    printf("\r\n");
    
    status = MQTTBadParameter;
  } else {
        memset(pContext, 0x00, sizeof(*pContext));

    pContext->connectStatus = MQTTNotConnected;
    pContext->transportInterface = *pTransportInterface;
    pContext->callbacks = *pCallbacks;
    pContext->networkBuffer = *pNetworkBuffer;

    pContext->nextPacketId = 1;
  }

  return status;
}

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