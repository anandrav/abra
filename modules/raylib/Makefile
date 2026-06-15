UNAME_S := $(shell uname -s)

CC ?= cc
CFLAGS ?= -O2 -Wall -Wextra -std=c11
LDLIBS ?=

ifeq ($(OS),Windows_NT)
	LIB := build/abra_module_raylib.dll
	LDFLAGS ?= -shared
else ifeq ($(UNAME_S),Darwin)
	LIB := build/libabra_module_raylib.dylib
	CFLAGS += -fPIC
	LDFLAGS ?= -dynamiclib
else
	LIB := build/libabra_module_raylib.so
	CFLAGS += -fPIC
	LDFLAGS ?= -shared
	LDLIBS += -ldl
endif

.PHONY: all clean

all: $(LIB)

$(LIB): raylib.c | build
	$(CC) $(CFLAGS) $(LDFLAGS) $< -o $@ $(LDLIBS)

build:
	mkdir -p build

clean:
	rm -rf build
