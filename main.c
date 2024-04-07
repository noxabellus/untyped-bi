#include "stdio.h"
#include "stdint.h"
#include "string.h"

typedef enum TrapKind TrapKind;
typedef enum FunctionKind FunctionKind;
typedef enum CTRL CTRL;
typedef enum NATIVE_CTRL NATIVE_CTRL;

typedef struct OperandStack OperandStack;
typedef struct LayoutStack LayoutStack;
typedef struct Bytecode Bytecode;
typedef struct BytecodeFunction BytecodeFunction;
typedef struct Function Function;
typedef struct Frame Frame;
typedef struct CallStack CallStack;
typedef struct Handler Handler;
typedef struct HandlerVector HandlerVector;
typedef struct Context Context;
typedef struct Fiber Fiber;
typedef struct Layout Layout;
typedef struct Trap Trap;

typedef NATIVE_CTRL (*Native) (Fiber*);


enum CTRL {
    CTRL_EXEC,
    CTRL_TRAP,
};

enum NATIVE_CTRL {
    NATIVE_CTRL_RETURN,
    NATIVE_CTRL_CONTINUE,
    NATIVE_CTRL_PROMPT,
    NATIVE_CTRL_STEP,
    NATIVE_CTRL_TRAP,
};

enum FunctionKind {
    BYTECODE_FN,
    NATIVE_FN,
};

enum TrapKind {
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
};


struct Layout {
    uint16_t size;
    uint16_t align;
};

struct OperandStack {
    uint8_t* data;
    size_t size;
    size_t sp;
};

struct LayoutStack {
    size_t* offsets;
    Layout* layouts;
    size_t size;
    size_t sp
};

struct Bytecode {
    uint8_t* data;
    size_t size;
    size_t ep;
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

struct Trap {
    TrapKind kind;
    void* trap_data;
};


struct Fiber {
    Context* context;
    OperandStack operand_stack;
    LayoutStack layout_stack;
    CallStack call_stack;
    HandlerVector handler_vector;
    Trap trap;
};


#define OP_UNREACHABLE 255 // 8xOP 0xNIL
#define OP_NONE 0          // 8xOP 0xNIL
#define OP_PUSH 1          // 8xOP 16xSIZE 16xALIGN (SIZE%ALIGN)xIMM
#define OP_POP 2           // 8xOP 16xCOUNT
#define OP_ADDR_OF 3       // 8xOP 16xDATA_INDEX
#define OP_LOAD 4          // 8xOP 16xSIZE 16xALIGN
#define OP_STORE 5         // 8xOP
#define OP_CALL 6          // 8xOP 16xFN_INDEX
#define OP_RETURN 7        // 8xOP 0xNIL


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

        case OP_NONE: {
            frame->ip++;
        } break;

        case OP_PUSH: {
            ctrl_assert( fiber->layout_stack.sp < fiber->layout_stack.size
                       , TRAP_OPERAND_OVERFLOW, "PUSH would overflow layout stack");

            size_t bc_offset = 1 + sizeof(uint16_t);
            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing size parameter");
            uint16_t size = read16(bytecode->data, frame->ip + 1);

            bc_offset += sizeof(uint16_t);
            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing align parameter");
            uint16_t align = read16(bytecode->data, frame->ip + 1 + sizeof(uint16_t));

            bc_offset += calc_offset(frame->ip + bc_offset, align);
            uint8_t* source = &bytecode->data[frame->ip + bc_offset];
            bc_offset += size;
            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "PUSH missing operand");

            size_t op_pad = calc_offset(fiber->operand_stack.sp, align);
            size_t op_offset = op_pad + size;
            ctrl_assert( fiber->operand_stack.sp + op_offset <= fiber->operand_stack.size
                       , TRAP_OPERAND_OVERFLOW, "PUSH operand is too large for the operand stack");
            size_t destination_offset = fiber->operand_stack.sp + op_pad;
            uint8_t* destination = &fiber->operand_stack.data[destination_offset];

            memcpy(destination, source, size);
            fiber->layout_stack.offsets[fiber->layout_stack.sp] = destination_offset;
            fiber->layout_stack.layouts[fiber->layout_stack.sp] = (Layout) { size, align };
            fiber->layout_stack.sp++;
            fiber->operand_stack.sp += op_offset;
            frame->ip += bc_offset;
        } break;

        case OP_POP: {
            size_t bc_offset = 1 + sizeof(uint16_t);
            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "POP missing count parameter");

            uint16_t count = read16(bytecode->data, frame->ip + 1);
            ctrl_assert( count <= fiber->layout_stack.sp
                       , TRAP_OPERAND_UNDERFLOW, "POP would underflow layout stack");

            fiber->layout_stack.sp -= count;
            fiber->operand_stack.sp = fiber->layout_stack.offsets[fiber->layout_stack.sp];
            frame->ip += bc_offset;
        } break;

        case OP_ADDR_OF: {
            ctrl_assert( fiber->layout_stack.sp < fiber->layout_stack.size
                       , TRAP_OPERAND_OVERFLOW, "ADDR_OF would overflow layout stack");

            ctrl_assert( fiber->operand_stack.sp + sizeof(void*) <= fiber->operand_stack.size
                       , TRAP_OPERAND_OVERFLOW, "ADDR_OF would overflow operand stack")

            size_t bc_offset = 1 + sizeof(uint16_t);
            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "ADDR_OF missing data index");

            uint16_t data_index = read16(bytecode->data, frame->ip + 1);
            ctrl_assert( data_index < fiber->layout_stack.sp
                       , TRAP_OPERAND_UNDERFLOW, "ADDR_OF data index out of bounds");

            void* ptr = &fiber->operand_stack.data[fiber->layout_stack.offsets[fiber->layout_stack.sp - data_index]];

            memcpy(&fiber->operand_stack.data[fiber->operand_stack.sp], &ptr, sizeof(void*));
            fiber->layout_stack.offsets[fiber->layout_stack.sp] = fiber->operand_stack.sp;
            fiber->layout_stack.layouts[fiber->layout_stack.sp] = (Layout) { sizeof(void*), 8 };
            fiber->layout_stack.sp++;
            fiber->operand_stack.sp += sizeof(void*);
            frame->ip += bc_offset;
        } break;

        case OP_LOAD: {
            ctrl_assert( fiber->layout_stack.sp < fiber->layout_stack.size
                       , TRAP_OPERAND_OVERFLOW, "LOAD would overflow layout stack");

            ctrl_assert( fiber->layout_stack.sp >= 1
                       , TRAP_OPERAND_UNDERFLOW, "LOAD requires one stack operand [ptr]");

            ctrl_assert( fiber->operand_stack.sp + sizeof(void*) <= fiber->operand_stack.size
                       , TRAP_OPERAND_OVERFLOW, "LOAD would overflow operand stack");

            size_t bc_offset = 1 + sizeof(uint16_t) + sizeof(uint16_t);

            ctrl_assert( frame->ip + bc_offset <= bytecode->size
                       , TRAP_IP_OUT_OF_BOUNDS, "LOAD missing size or align parameter/s");
            uint16_t size = read16(bytecode->data, frame->ip + 1);
            uint16_t align = read16(bytecode->data, frame->ip + 1 + sizeof(uint16_t));

            uint8_t** ptr = &fiber->operand_stack.data[fiber->layout_stack.offsets[fiber->layout_stack.sp - 1]];
            size_t op_pad = calc_offset(fiber->operand_stack.sp, align);
            size_t op_offset = op_pad + size;
            size_t destination_offset = fiber->operand_stack.sp + op_pad;

            ctrl_assert( fiber->operand_stack.sp + op_offset <= fiber->operand_stack.size
                       , TRAP_OPERAND_OVERFLOW, "LOAD operand is too large for the operand stack");

            memcpy(&fiber->operand_stack.data[destination_offset], *ptr, size);
            fiber->layout_stack.offsets[fiber->layout_stack.sp] = destination_offset;
            fiber->layout_stack.layouts[fiber->layout_stack.sp] = (Layout) { size, align };
            fiber->layout_stack.sp++;
            fiber->operand_stack.sp += op_offset;
            frame->ip += bc_offset;
        } break;

        case OP_STORE: {
            ctrl_assert( fiber->layout_stack.sp >= 2
                       , TRAP_OPERAND_UNDERFLOW, "STORE requires two stack operands [ptr, val]");

            size_t bc_offset = 1;

            uint8_t** ptr = &fiber->operand_stack.data[fiber->layout_stack.offsets[fiber->layout_stack.sp - 2]];
            uint8_t* val = &fiber->operand_stack.data[fiber->layout_stack.offsets[fiber->layout_stack.sp - 1]];

            memcpy(*ptr, val, fiber->layout_stack.layouts[fiber->layout_stack.sp - 1].size);
            fiber->layout_stack.sp -= 2;
            fiber->operand_stack.sp = fiber->layout_stack.offsets[fiber->layout_stack.sp];
            frame->ip += bc_offset;
        } break;

        case OP_CALL: return exec_call(fiber);

        case OP_RETURN: return exec_ret(fiber);

        default: ctrl_trap(TRAP_UNEXPECTED, "invalid opcode");
    }

    return CTRL_EXEC;
}


int main() {
    printf("Howdy bitch\n");
    return 0;
}
