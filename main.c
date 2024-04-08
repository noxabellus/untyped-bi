#include "stdio.h"
#include "stdint.h"
#include "string.h"


typedef enum TrapKind TrapKind;
typedef enum FunctionKind FunctionKind;
typedef enum CTRL CTRL;
typedef enum NATIVE_CTRL NATIVE_CTRL;

typedef struct DataStack DataStack;
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
typedef struct LayoutTable LayoutTable;
typedef struct Trap Trap;

typedef NATIVE_CTRL (*Native) (Fiber*);


#define SLICE_T(T) struct { T* data; size_t size; }
#define Slice(T) Slice_ ## T

typedef SLICE_T(uint8_t)  Slice(uint8_t);
typedef SLICE_T(Layout)   Slice(Layout);
typedef SLICE_T(Frame)    Slice(Frame);
typedef SLICE_T(Function) Slice(Function);
typedef SLICE_T(Handler)  Slice(Handler);


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
    uint16_t offset;
};

struct LayoutTable {
    Slice(Layout) layouts;
    uint8_t num_params;
    uint8_t num_locals;
};

struct Bytecode {
    Slice(uint8_t) ops;
    size_t ep;
};

struct Function {
    LayoutTable table;
    FunctionKind kind;
    union {
        Bytecode* bytecode;
        Native* native;
    };
};

struct Frame {
    Function* function;
    size_t sp;
    size_t ip;
};

struct DataStack {
    Slice(uint8_t) mem;
    size_t sp;
};

struct CallStack {
    Slice(Frame) frames;
    size_t fp;
};

struct Handler {
    Slice(Function) cases;
    size_t fp;
};

struct HandlerVector {
    Slice(Handler) handlers;
    size_t hp;
};

struct Trap {
    TrapKind kind;
    char const* message;
};

struct Context {

};

struct Fiber {
    Context* context;
    DataStack data_stack;
    CallStack call_stack;
    HandlerVector handler_vector;
    Trap trap;
};


// triggers a trap if executed
// 1xOP
#define OP_UNREACHABLE  255

// does nothing
// 1xOP
#define OP_NOP            0


// call the function who's address is stored in FUN_REG
// 1xOP + 8xFUN_REG
#define OP_CALL           1

// return from the current function
// 1xOP
#define OP_RET            2


// copy the address of DATA_REG into ADDR_REG, optionally offsetting the address
// 1xOP + 8xADDR_REG + 8xDATA_REG + 16xOFFSET
#define OP_ADDR_OF       10

// store the immediate value into the address pointed to by ADDR_REG
// 1xOP + 8xADDR_REG + 16xSIZE + SIZExIMM
#define OP_STORE_IMM     11

// copy the value from DATA_REG to the address in ADDR_REG
// 1xOP + 8xADDR_REG + 8xDATA_REG
#define OP_STORE         12

// copy the value from the address in ADDR_REG to DATA_REG
// 1xOP + 8xADDR_REG + 8xDATA_REG
#define OP_LOAD          13


uint8_t read8 (uint8_t const* mem, size_t ip) {
    return mem[ip];
}

uint16_t read16 (uint8_t const* mem, size_t ip) {
    return (((uint16_t) mem[ip + 0]) << 8)
         | (((uint16_t) mem[ip + 1]) << 0)
         ;
}

uint32_t read32 (uint8_t const* mem, size_t ip) {
    return (((uint32_t) mem[ip + 0]) << 24)
         | (((uint32_t) mem[ip + 1]) << 16)
         | (((uint32_t) mem[ip + 2]) <<  8)
         | (((uint32_t) mem[ip + 3]) <<  0)
         ;
}

uint64_t read64 (uint8_t const* mem, size_t ip) {
    return (((uint64_t) mem[ip + 0]) << 56)
         | (((uint64_t) mem[ip + 1]) << 48)
         | (((uint64_t) mem[ip + 2]) << 40)
         | (((uint64_t) mem[ip + 3]) << 32)
         | (((uint64_t) mem[ip + 4]) << 24)
         | (((uint64_t) mem[ip + 5]) << 16)
         | (((uint64_t) mem[ip + 6]) <<  8)
         | (((uint64_t) mem[ip + 7]) <<  0)
         ;
}


#define ctrl_trap(trap_kind, trap_message) { \
    fiber->trap.kind = trap_kind; \
    fiber->trap.message = trap_message; \
    return CTRL_TRAP; \
}

#define ctrl_assert(cond, trap_kind, trap_message) \
    if (!(cond)) ctrl_trap(trap_kind, trap_message)


size_t calc_offset(size_t addr, size_t align) {
    return (addr + align - 1) & ~(align - 1);
}


CTRL step_bc (Fiber* fiber) {
    Frame* frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
    LayoutTable* table = &frame->function->table;
    Bytecode* bytecode = frame->function->bytecode;

    uint8_t* locals = &fiber->data_stack.mem.data[frame->sp];

    switch (bytecode->ops.data[frame->ip]) {
        case OP_UNREACHABLE:
            ctrl_trap(TRAP_UNREACHABLE, "unreachable code executed");

        case OP_NOP: {
            frame->ip += 1;
        } break;

        case OP_ADDR_OF: {
            uint8_t addr_idx =  read8(bytecode->ops.data, frame->ip + 1);
            uint8_t data_idx =  read8(bytecode->ops.data, frame->ip + 2);
            uint16_t  offset = read16(bytecode->ops.data, frame->ip + 3);

            uint8_t* addr_reg = &locals[table->layouts.data[addr_idx].offset];
            uint8_t* data_reg = &locals[table->layouts.data[data_idx].offset];

            *(uint8_t**) addr_reg = data_reg + offset;

            frame->ip += 1 + 1 + 1 + 2;
        } break;

        case OP_STORE_IMM: {
            uint8_t addr_idx =  read8(bytecode->ops.data, frame->ip + 1);
            uint8_t     size =  read8(bytecode->ops.data, frame->ip + 2);

            uint8_t* addr_reg = &locals[table->layouts.data[addr_idx].offset];

            // TODO: read immediate value into addr_reg

            frame->ip += 1 + 1 + 1 + size;
        } break;
    }

    return CTRL_EXEC;
}
