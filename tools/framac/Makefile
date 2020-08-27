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
	
deserializePublish:
	frama-c -wp -rte $(FRAMAC) deserializePublish.c -then -report

deserializePublishScript:
	frama-c -wp -rte $(FRAMAC) MQTT_deserializePublish.c -then -report 
	frama-c -wp -rte $(FRAMAC) deserializePublish.c -then -report 
	frama-c -wp -rte $(FRAMAC) checkPublishRemainingLength.c -then -report 
	frama-c -wp -rte $(FRAMAC) processPublishFlags.c -then -report 

deserializePublishScriptParsed:
	frama-c -wp -rte $(FRAMAC) MQTT_deserializePublish.c -then -report > MQTT_DeserializePublish.txt
	python3 cleanFramacOutput.py MQTT_DeserializePublish /home/ubuntu/mqtt/tools/framac/MQTT_DeserializePublish.txt
	frama-c -wp -rte $(FRAMAC) deserializePublish.c -then -report > deserializePublish.txt
	python3 cleanFramacOutput.py deserializePublish /home/ubuntu/mqtt/tools/framac/deserializePublish.txt
	frama-c -wp -rte $(FRAMAC) checkPublishRemainingLength.c -then -report > checkPublishRemainingLength.txt
	python3 cleanFramacOutput.py checkPublishRemainingLength /home/ubuntu/mqtt/tools/framac/checkPublishRemainingLength.txt
	frama-c -wp -rte $(FRAMAC) processPublishFlags.c -then -report > processPublishFlags.txt
	python3 cleanFramacOutput.py processPublishFlags /home/ubuntu/mqtt/tools/framac/processPublishFlags.txt

readSubackStatus:
	frama-c -wp -rte $(FRAMAC) readSubackStatus.c -wp-timeout 40 -then -report 

deserializeSuback:
	frama-c -wp -rte $(FRAMAC) deserializeSuback.c -then -report  

MQTT_deserializeAck:
	frama-c -wp -rte $(FRAMAC) MQTT_DeserializeAck.c -then -report 

deserializeAckScript:
	frama-c -wp -rte $(FRAMAC) MQTT_DeserializeAck.c -then -report 
	frama-c -wp -rte $(FRAMAC) deserializeSuback.c -then -report 
	frama-c -wp -rte $(FRAMAC) readSubackStatus.c -then -report 

deserializeAckScriptParsed:
	frama-c -wp -rte $(FRAMAC) MQTT_DeserializeAck.c -then -report  > MQTT_DeserializeAck.txt
	python3 cleanFramacOutput.py MQTT_DeserializeAck /home/ubuntu/mqtt/tools/framac/MQTT_DeserializeAck.txt
	frama-c -wp -rte $(FRAMAC) deserializeSuback.c -then -report  > deserializeSuback.txt
	python3 cleanFramacOutput.py deserializeSuback /home/ubuntu/mqtt/tools/framac/deserializeSuback.txt
	frama-c -wp -rte $(FRAMAC) readSubackStatus.c -then -report  > readSubackStatus.txt
	python3 cleanFramacOutput.py readSubackStatus /home/ubuntu/mqtt/tools/framac/readSubackStatus.txt

fc: 
	frama-c -wp -rte $(FRAMAC) mqtt_fc.h -then -report

callgraph:
	frama-c -users -main MQTT_Connect $(FRAMAC) ~/mqtt/libraries/standard/mqtt/src/mqtt.c

otherFunctions:
	frama-c -wp -rte $(FRAMAC) otherFunctions.c -then -report

deserializeFunctions:
	frama-c -wp -rte $(FRAMAC) deserializeFunctions.c -then -report