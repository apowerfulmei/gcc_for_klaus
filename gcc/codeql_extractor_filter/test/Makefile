CC=gcc
CFLAGS=-Isrc

TARGET=program
SRC_DIR=src

all: $(TARGET)

$(TARGET): $(SRC_DIR)/main.o $(SRC_DIR)/calculate.o
	$(CC) -o $(TARGET) $(SRC_DIR)/main.o $(SRC_DIR)/calculate.o

$(SRC_DIR)/main.o: $(SRC_DIR)/main.c $(SRC_DIR)/calculate.h
	$(CC) -c $(SRC_DIR)/main.c -o $(SRC_DIR)/main.o $(CFLAGS)

$(SRC_DIR)/calculate.o: $(SRC_DIR)/calculate.c $(SRC_DIR)/calculate.h
	$(CC) -c $(SRC_DIR)/calculate.c -o $(SRC_DIR)/calculate.o $(CFLAGS)

clean:
	rm -f $(TARGET) $(SRC_DIR)/*.o

.PHONY: clean
