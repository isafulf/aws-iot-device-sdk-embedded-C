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

default:
	frama-c -wp -wp-fct MQTT_Init $(FRAMAC) init.c -then -report

init-cpp.c: init.c
	gcc -E $(DEFINES) $(INCLUDES) $(CFLAGS) $< > $@

init-simple.c: init-cpp.c
	grep -v '^#' $< | clang-format  > $@

simple: 
	frama-c -wp -rte $(FRAMAC) init-simple.c -then -report

all: 
	frama-c -wp -rte $(FRAMAC) mqtt.h -then -report

mqtt_Init:
	frama-c -wp -rte $(FRAMAC) MQTT_Init.c -then -report

mqtt_GetPacketId:
	frama-c -wp -rte $(FRAMAC) MQTT_GetPacketId.c -then -report

mqtt_Connect:
	frama-c -wp -rte $(FRAMAC) MQTT_Connect.c -then -report

fc: 
	frama-c -wp -rte $(FRAMAC) mqtt_fc.h -then -report

callgraph:
	frama-c -users -main MQTT_Connect $(FRAMAC) ~/mqtt/libraries/standard/mqtt/src/mqtt.c
