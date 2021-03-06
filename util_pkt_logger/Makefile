### Application-specific constants

APP_NAME := util_pkt_logger

### Environment constants 

LGW_PATH ?= ../libloragw
ARCH ?=
CROSS_COMPILE ?=

### External constant definitions
# must get library build option to know if mpsse must be linked or not

include $(LGW_PATH)/library.cfg

### Constant symbols

CC := $(CROSS_COMPILE)gcc
AR := $(CROSS_COMPILE)ar

CFLAGS=-O2 -Wall -Wextra -std=c99 -Iinc -I.

### Constants for LoRa concentrator HAL library
# List the library sub-modules that are used by the application

LGW_INC = $(LGW_PATH)/inc/config.h
LGW_INC += $(LGW_PATH)/inc/loragw_hal.h

### Linking options

LIBS := -lloragw -lrt -lm

### General build targets

all: $(APP_NAME)

clean:
	rm -f obj/*.o
	rm -f $(APP_NAME)

### HAL library (do no force multiple library rebuild even with 'make -B')

$(LGW_PATH)/inc/config.h:
	@if test ! -f $@; then \
	$(MAKE) all -C $(LGW_PATH); \
	fi

$(LGW_PATH)/libloragw.a: $(LGW_INC)
	@if test ! -f $@; then \
	$(MAKE) all -C $(LGW_PATH); \
	fi

### Sub-modules compilation

obj/parson.o: src/parson.c inc/parson.h
	$(CC) -c $(CFLAGS) $< -o $@
obj/mqtt.o: src/mqtt.c inc/mqtt.h
	$(CC) -c $(CFLAGS) $< -o $@
obj/mqtt_pal.o: src/mqtt_pal.c inc/mqtt.h
	$(CC) -c $(CFLAGS) $< -o $@

### Main program compilation and assembly

obj/$(APP_NAME).o: src/$(APP_NAME).c $(LGW_INC) inc/parson.h inc/mqtt.h inc/posix_sockets.h
	$(CC) -c $(CFLAGS) -I$(LGW_PATH)/inc $< -pthread -o $@

$(APP_NAME): obj/$(APP_NAME).o $(LGW_PATH)/libloragw.a obj/parson.o obj/mqtt.o obj/mqtt_pal.o
	$(CC) -L$(LGW_PATH) $< obj/parson.o obj/mqtt.o obj/mqtt_pal.o -lpthread -o $@ $(LIBS)

### EOF
