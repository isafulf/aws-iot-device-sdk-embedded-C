#include "mqtt.h"
#include "mqtt_utils.h"
    
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
    printf("\r\n")

        ;
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
