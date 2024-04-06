#include "stdio.h"
#include "stdint.h"
#include "string.h"

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

typedef enum {
    NATIVE_CTRL_RETURN,
    NATIVE_CTRL_CONTINUE,
    NATIVE_CTRL_PROMPT,
    NATIVE_CTRL_STEP,
    NATIVE_CTRL_TRAP,
} NATIVE_CTRL;

typedef NATIVE_CTRL (*Native) (Fiber*);


struct OperandStack {
    uint8_t* data;
    size_t size;
    size_t sp;
};

struct Bytecode {
    uint8_t* data;
    size_t size;
    size_t ep;
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
    size_t sp;
    size_t ip;
};

struct CallStack {
    Frame* data;
    size_t size;
    size_t fp;
};

struct Handler {
    Function* data;
    size_t size;
    size_t fp;
};

struct HandlerVector {
    Handler* data;
    size_t size;
    size_t capacity;
};

struct Context {

};

typedef enum {
    TRAP_NOTHING,
    TRAP_UNEXPECTED,
    TRAP_UNREACHABLE,
    TRAP_OPERAND_OVERFLOW,
    TRAP_OPERAND_UNDERFLOW,
    TRAP_CALL_OVERFLOW,
    TRAP_CALL_UNDERFLOW,
    TRAP_IP_OUT_OF_BOUNDS,
    TRAP_HANDLER_OVERFLOW,
    TRAP_HANDLER_MISSING,
} TrapKind;

typedef struct {
    TrapKind kind;
    void* trap_data;
} Trap;


struct Fiber {
    Context* context;
    OperandStack operand_stack;
    CallStack call_stack;
    HandlerVector handler_vector;
    Trap trap;
};


#define OP_UNREACHABLE 255 // 8xOP 0xNIL
#define OP_NONE 0          // 8xOP 0xNIL
#define OP_PUSH 1          // 8xOP 16xSIZE (SIZE%ALIGN)xIMM
#define OP_POP 2           // 8xOP 16xSIZE
#define OP_ADDR_OF 3       // 8xOP 32xDATA_OFFSET
#define OP_LOAD 4          // 8xOP 16xSIZE
#define OP_STORE 5         // 8xOP 16xSIZE 32xPTR_OFFSET 32xDATA_OFFSET
#define OP_CALL 6          // 8xOP 32xPTR_OFFSET
#define OP_RETURN 7           // 8xOP 0xNIL

typedef enum {
    CTRL_EXEC,
    CTRL_TRAP,
} CTRL;

uint8_t read8(uint8_t* data, size_t offset) {
    return data[offset];
}

uint16_t read16(uint8_t* data, size_t offset) {
    return (data[offset + 0] << 8)
         | (data[offset + 1] << 0)
         ;
}

uint32_t read32(uint8_t* data, size_t offset) {
    return (data[offset + 0] << 24)
         | (data[offset + 1] << 16)
         | (data[offset + 2] <<  8)
         | (data[offset + 3] <<  0)
         ;
}

uint64_t read64(uint8_t* data, size_t* offset) {
    return (data[*offset + 0] << 56)
         | (data[*offset + 1] << 48)
         | (data[*offset + 2] << 40)
         | (data[*offset + 3] << 32)
         | (data[*offset + 4] << 24)
         | (data[*offset + 5] << 16)
         | (data[*offset + 6] <<  8)
         | (data[*offset + 7] <<  0)
         ;
}

#define ctrl_trap(trap_kind, trap_data) { \
    fiber->trap = (Trap) { trap_kind, trap_data }; \
    return CTRL_TRAP; \
}

#define ctrl_assert(cond, trap_kind, trap_data) \
    if (!(cond)) ctrl_trap(trap_kind, trap_data)

size_t calc_offset(size_t addr, size_t align) {
    return (addr + align - 1) & ~(align - 1);
}

CTRL step(Fiber* fiber) {
    ctrl_assert(
        fiber->call_stack.fp < fiber->call_stack.size,
        TRAP_CALL_OVERFLOW, NULL
    );

    Frame* frame = &fiber->call_stack.data[fiber->call_stack.fp];
    Function* function = frame->function;

    switch (function->kind) {
        case NATIVE_FN: return step_native(fiber);

        case BYTECODE_FN: return step_bc(fiber);

        default: ctrl_trap(TRAP_UNEXPECTED, "invalid function kind");
    }
}

CTRL step_native(Fiber* fiber) {
    Native fn = *fiber->call_stack.data[fiber->call_stack.fp].function->native;

    switch (fn(fiber)) {
        case NATIVE_CTRL_RETURN: return CTRL_EXEC; // TODO: handle return

        case NATIVE_CTRL_CONTINUE: return CTRL_EXEC; // TODO: handle continue

        case NATIVE_CTRL_PROMPT: return CTRL_EXEC; // TODO: handle prompt

        case NATIVE_CTRL_STEP: return CTRL_EXEC;

        case NATIVE_CTRL_TRAP: return CTRL_TRAP;

        default: ctrl_trap(TRAP_UNEXPECTED, "invalid native control");
    }
}

CTRL step_bc(Fiber* fiber) {
    Frame* frame = &fiber->call_stack.data[fiber->call_stack.fp];
    Bytecode* bytecode = frame->function->bytecode;

    ctrl_assert(frame->ip < bytecode->size, TRAP_IP_OUT_OF_BOUNDS, NULL);

    switch (bytecode->data[frame->ip]) {
        case OP_UNREACHABLE: ctrl_trap(TRAP_UNREACHABLE, NULL);

        case OP_NONE:
            frame->ip++;
            return CTRL_EXEC;


        // So the problem here is we don't have alignment information on the stack
        // we align before pushing here, but when popping we only have the size
        // .. so we need to store the alignment information in the stack as well?
        // weird.
        case OP_PUSH:
            size_t offset = 1 + sizeof(uint16_t);
            ctrl_assert( frame->ip + offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing size parameter");
            uint16_t size = read16(bytecode->data, frame->ip + 1);

            offset += sizeof(uint16_t);
            ctrl_assert( frame->ip + offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing align parameter");
            uint16_t align = read16(bytecode->data, frame->ip + 1 + sizeof(uint16_t));

            offset += calc_offset(frame->ip + offset, align);
            uint8_t* source = &bytecode->data[frame->ip + offset];
            offset += size;
            ctrl_assert( frame->ip + offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing operand");

            size_t op_pad = calc_offset(fiber->operand_stack.sp, align);
            size_t op_offset = op_pad + size;
            ctrl_assert( fiber->operand_stack.sp + op_offset <= fiber->operand_stack.size
                       , TRAP_OPERAND_OVERFLOW, "PUSH operand is too large for the stack");
            uint8_t* destination = &fiber->operand_stack.data[fiber->operand_stack.sp + op_pad];

            memcpy(destination, source, size);
            fiber->operand_stack.sp += op_offset;
            frame->ip += offset;
            return CTRL_EXEC;

        case OP_POP: return exec_pop(fiber);

        case OP_ADDR_OF: return exec_addr_of(fiber);

        case OP_LOAD: return exec_load(fiber);

        case OP_STORE: return exec_store(fiber);

        case OP_CALL: return exec_call(fiber);

        case OP_RETURN: return exec_ret(fiber);

        default: ctrl_trap(TRAP_UNEXPECTED, "invalid opcode");
    }
}


int main() {
    printf("Howdy bitch\n");
    return 0;
}
