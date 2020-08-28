MQTT=$(abspath ../..)

SOURCES = \
    $(MQTT)/libraries/standard/mqtt/src/mqtt.c \
    $(MQTT)/libraries/standard/mqtt/src/mqtt_state.c \
    $(MQTT)/libraries/standard/mqtt/src/mqtt_lightweight.c \

DEFINES = \
    -Dmqtt_EXPORTS \

INCLUDES = \
        -I. \
        -I/usr/include \
        -I/usr/include/x86_64-linux-gnu \
        -I$(MQTT)/libraries/standard/mqtt/include \
        -I$(MQTT)/libraries/standard/utilities/include \
        -I$(MQTT)/libraries/standard/mqtt/src \
        -I$(MQTT)/demos/logging-stack \
        -I$(MQTT)/demos/mqtt/mqtt_demo_basic_tls \
        -I$(MQTT)/demos/mqtt/mqtt_demo_lightweight \
        -I$(MQTT)/demos/mqtt/mqtt_demo_plaintext \

CFLAGS = \
    -fPIC \
    -std=gnu90 \

FRAMAC = \
    -cpp-extra-args="$(DEFINES) $(INCLUDES) $(CFLAGS)" \

otherFunctions:
	frama-c -wp -rte $(FRAMAC) otherFunctions.c -then -report

deserializeFunctions:
	frama-c -wp -rte $(FRAMAC) deserializeFunctions.c -then -report