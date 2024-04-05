#include "stdio.h"
#include "stdint.h"

typedef struct OperandStack OperandStack;
typedef struct Bytecode Bytecode;
typedef struct BytecodeFunction BytecodeFunction;
typedef enum FunctionKind FunctionKind;
typedef struct Function Function;
typedef struct Frame Frame;
typedef struct CallStack CallStack;
typedef struct Handler Handler;
typedef struct HandlerVector HandlerVector;
typedef struct Context Context;
typedef struct Fiber Fiber;
typedef void (*Native) (Fiber*);


struct OperandStack {
    uint8_t* base;
    uint8_t* limit;
    uint8_t* sp;
};

struct Bytecode {
    uint8_t* base;
    uint8_t* limit;
    uint8_t* ep;
};

enum FunctionKind {
    BYTECODE_FN,
    NATIVE_FN,
};

struct Function {
    FunctionKind kind;
    union {
        Bytecode* bytecode;
        Native* native;
    };
    uint16_t input_size;
    uint16_t return_size;
    uint16_t return_align;
};

struct Frame {
    Function* function;
    uint8_t* stack_head;
    uint8_t* ip;
};

struct CallStack {
    Frame* base;
    Frame* limit;
    Frame* fp;
};

struct Handler {
    Function* base;
    Function* limit;
    Frame* frame;
};

struct HandlerVector {
    Handler* handlers;
    uint32_t size;
    uint32_t capacity;
};

struct Context {

};

struct Fiber {
    Context* context;
    OperandStack operand_stack;
    CallStack call_stack;
    HandlerVector handler_vector;
};


#define OP_UNREACHABLE 255 // 8xOP 0xNIL
#define OP_NONE 0          // 8xOP 0xNIL
#define OP_PUSH 1          // 8xOP 16xSIZE (SIZE%ALIGN)xIMM
#define OP_POP 2           // 8xOP 16xSIZE
#define OP_ADDR_OF 3       // 8xOP 32xDATA_OFFSET
#define OP_LOAD 4          // 8xOP 16xSIZE
#define OP_STORE 5         // 8xOP 16xSIZE 32xPTR_OFFSET 32xDATA_OFFSET
#define OP_CALL 6          // 8xOP 32xPTR_OFFSET
#define OP_RET 7           // 8xOP 0xNIL




int main() {
    printf("Howdy bitch\n");
    return 0;
}
