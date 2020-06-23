#include "deserializeFunctions.h"
#include <limits.h>
#include <stdint.h>

// struct MQTTPacketInfo
// {
//     /**
//      * @brief Type of incoming MQTT packet.
//      */
//     uint8_t type;

//     /**
//      * @brief Remaining serialized data in the MQTT packet.
//      */
//     uint8_t * pRemainingData;

//     /**
//      * @brief Length of remaining serialized data.
//      */
//     size_t remainingLength;
// };

/*@
    requires 0 <= statusCount < SIZE_MAX;
    requires \valid(pStatusStart + (0 .. statusCount - 1));
    assigns \nothing;
*/
static MQTTStatus_t readSubackStatus( size_t statusCount,
                                      const uint8_t * pStatusStart )
{
    MQTTStatus_t status = MQTTSuccess;
    uint8_t subscriptionStatus = 0;
    size_t i = 0;

    //assert( pStatusStart != NULL );
   ((void) sizeof ((pStatusStart != ((void *)0)) ? 1 : 0), __extension__ ({ if (
   pStatusStart != ((void *)0)) ; else __assert_fail ("pStatusStart != NULL", "mqtt_lightweight.c", 889, __extension__ __PRETTY_FUNCTION__); }));


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

                printf( "Topic filter %lu accepted, max QoS %hhu.",
                            ( unsigned long ) i, subscriptionStatus);
                break;

            case 0x80:

                printf( "Topic filter %lu refused.", ( unsigned long ) i );

                /* Application should remove subscription from the list */
                status = MQTTServerRefused;

                break;

            default:
                printf( "Bad SUBSCRIBE status %hhu.", subscriptionStatus);

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

/*@
    requires \valid(pSuback);
    requires 0 <= pSuback->remainingLength <= SIZE_MAX;
    requires \valid(pSuback->pRemainingData + (0 .. pSuback->remainingLength - 1));
    requires \valid(pPacketIdentifier);
    requires 0 <= ( *( pSuback->pRemainingData ) ) << 8  <= 1<<16;
    requires 0 <= *( ( pSuback->pRemainingData ) + 1 ) <= 1<<16;
    requires 0 <= *pPacketIdentifier <= UINT_MAX;
    assigns *pPacketIdentifier;

    behavior badInput:
        assumes pSuback->remainingLength < 3U;
        ensures *pPacketIdentifier == \old(*pPacketIdentifier);
        ensures \result == MQTTBadResponse;
    
    behavior goodInput:
        assumes pSuback->remainingLength >= 3U;

*/
static MQTTStatus_t deserializeSuback( const MQTTPacketInfo_t * const pSuback,
                                       uint16_t * pPacketIdentifier )
{
    MQTTStatus_t status = MQTTSuccess;

    // assert( pSuback != NULL );
    ((void) sizeof ((pSuback != ((void *)0)) ? 1 : 0), __extension__ ({ if (
    pSuback != ((void *)0)) ; else __assert_fail ("pSuback != NULL", "mqtt_lightweight.c", 942, __extension__ __PRETTY_FUNCTION__); }));

    // assert( pPacketIdentifier != NULL );
    ((void) sizeof ((pPacketIdentifier != ((void *)0)) ? 1 : 0), __extension__ ({ if (
    pPacketIdentifier != ((void *)0)) ; else __assert_fail ("pPacketIdentifier != NULL", "mqtt_lightweight.c", 943, __extension__ __PRETTY_FUNCTION__); }));

    size_t remainingLength = pSuback->remainingLength;
    const uint8_t * pVariableHeader = pSuback->pRemainingData;


    /* A SUBACK must have a remaining length of at least 3 to accommodate the
     * packet identifier and at least 1 return code. */
    if( remainingLength < 3U )
    {
        printf("SUBACK cannot have a remaining length less than 3.");
        status = MQTTBadResponse;
    }
    else
    {
        /* Extract the packet identifier (first 2 bytes of variable header) from SUBACK. */
       *pPacketIdentifier = ( uint16_t ) ( ( ( ( uint16_t ) ( *( pVariableHeader ) ) ) << 8 ) | ( ( uint16_t ) ( *( ( pVariableHeader ) + 1 ) ) ) );

        printf( "Packet identifier %hu.", *pPacketIdentifier);

        status = readSubackStatus( remainingLength - sizeof( uint16_t ),
                                   pVariableHeader + sizeof( uint16_t ) );
    }

    return status;
}


/*@
    requires \valid(pConnack);
    requires \valid(pSessionPresent);
    requires 0 <= pConnack->remainingLength <= SIZE_MAX;
    requires \valid(pConnack->pRemainingData + (0 .. pConnack->remainingLength - 1));
    assigns *pSessionPresent;

    behavior badInputA:
        assumes pConnack->remainingLength != ( uint8_t ) 2U;
        ensures *pSessionPresent == \old(*pSessionPresent);
        ensures \result == MQTTBadResponse;
    
    behavior badInputB:
        assumes (pConnack->pRemainingData[0] | 0x01U ) != 0x01U;
        ensures *pSessionPresent == \old(*pSessionPresent);
        ensures \result == MQTTBadResponse;

    behavior other: 
        assumes pConnack->remainingLength == ( uint8_t ) 2U && (pConnack->pRemainingData[0] | 0x01U ) == 0x01U;
        ensures (pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U  ==> *pSessionPresent == true;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] != 0U) ==> \result == MQTTBadResponse;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (pConnack->pRemainingData[ 1 ] > 5U) ==> \result == MQTTBadResponse;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (0U < pConnack->pRemainingData[ 1 ] <= 5U) ==> \result == MQTTServerRefused;
        ensures ((pConnack->pRemainingData[ 0 ] & ( uint8_t ) 0x01U )  == ( uint8_t ) 0x01U) && (pConnack->pRemainingData[ 1 ] == 0U) && (pConnack->pRemainingData[ 1 ] == 0U) ==> \result == MQTTSuccess;
*/
static MQTTStatus_t deserializeConnack( const MQTTPacketInfo_t * const pConnack,
                                        bool * const pSessionPresent )
{
    MQTTStatus_t status = MQTTSuccess;

    // assert( pConnack != NULL );
   ((void) sizeof ((pConnack != ((void *)0)) ? 1 : 0), __extension__ ({ if (pConnack !=
   ((void *)0)) ; else __assert_fail ("pConnack != NULL", "mqtt_lightweight.c", 742, __extension__ __PRETTY_FUNCTION__); }));
    
    // assert( pSessionPresent != NULL );
   ((void) sizeof ((pSessionPresent != ((void *)0)) ? 1 : 0), __extension__ ({ if (
   pSessionPresent != ((void *)0)) ; else __assert_fail ("pSessionPresent != NULL", "mqtt_lightweight.c", 743, __extension__ __PRETTY_FUNCTION__); }));

    const uint8_t * pRemainingData = pConnack->pRemainingData;

    /* According to MQTT 3.1.1, the second byte of CONNACK must specify a
     * "Remaining length" of 2. */
    if( pConnack->remainingLength != ( ( uint8_t ) 2U ) )
    {
        printf("CONNACK does not have remaining length of %d.",
                   ( uint8_t ) 2U  );

        status = MQTTBadResponse;
    }

    /* Check the reserved bits in CONNACK. The high 7 bits of the second byte
     * in CONNACK must be 0. */
    else if( ( pRemainingData[ 0 ] | 0x01U ) != 0x01U )
    {
        printf("Reserved bits in CONNACK incorrect.");

        status = MQTTBadResponse;
    }
    else
    {
        /* Determine if the "Session Present" bit is set. This is the lowest bit of
         * the second byte in CONNACK. */
        if( ( pRemainingData[ 0 ] & ( ( uint8_t ) 0x01U ) )
            == ( ( uint8_t ) 0x01U ) )
        {
            printf("CONNACK session present bit set.");
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
            printf("CONNACK session present bit not set.");
        }
    }

    if( status == MQTTSuccess )
    {
        /* In MQTT 3.1.1, only values 0 through 5 are valid CONNACK response codes. */
        if( pRemainingData[ 1 ] > 5U )
        {
            printf( "CONNACK response %hhu is not valid.",
                        pRemainingData[ 1 ]);

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