#include <stddef.h>
#include <stdint.h>
#include <limits.h>

struct MQTTPacketInfo;
typedef struct MQTTPacketInfo      MQTTPacketInfo_t;

struct MQTTPacketInfo
{
    uint8_t type;

    /**
     * @brief Remaining serialized data in the MQTT packet.
     */
    uint8_t * pRemainingData;

    /**
     * @brief Length of remaining serialized data.
     */
    size_t remainingLength;
};

#define UINT16_DECODE( ptr )                                \
    ( uint16_t ) ( ( ( ( uint16_t ) ( *( ptr ) ) ) << 8 ) | \
                   ( ( uint16_t ) ( *( ( ptr ) + 1 ) ) ) )

/*@
    requires \valid(pIncomingPacket);
    requires  \valid(pIncomingPacket->pRemainingData + (0 .. pIncomingPacket->remainingLength -  1));
    requires 0 <= UINT16_DECODE(pIncomingPacket->pRemainingData ) + sizeof( uint16_t ) <= UINT_MAX  - 2U ;
*/
int MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket)
{
    return deserializePublish( pIncomingPacket, pPacketId, pPublishInfo );

}