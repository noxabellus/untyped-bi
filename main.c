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
typedef SLICE_T(uint16_t) Slice(uint16_t);
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
};

struct LayoutTable {
    Slice(Layout) layouts;
    uint32_t size;
    uint16_t align;
    uint8_t num_params;
    uint8_t num_locals;
};


struct Function {
    LayoutTable table;
    FunctionKind kind;
    size_t ep;
    union {
        Slice(uint8_t) bytecode;
        Native* native;
    };
};

struct Frame {
    Function* function;
    Slice(uint16_t) offsets;
    size_t old_sp;
    size_t bp;
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
// 1xOP + 8xFUN_REG + 8xRET_REG + 8xNUM_ARGS + (8*NUM_ARGS)xARG_REG
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


size_t calc_padding(size_t addr, size_t align) {
    return (addr + align - 1) & ~(align - 1);
}

size_t calc_relative_offset(Frame* frame, size_t new_bp, uint8_t idx) {
    return frame->offsets.data[idx] + (new_bp - frame->bp);
}

size_t alloca (size_t* sp, size_t size, size_t align) {
    size_t padding = calc_padding(*sp, align);

    size_t out = *sp + padding;
    *sp += size + padding;

    return out;
}


CTRL step_bc (Fiber* fiber) {
    Frame* frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
    Function* function = frame->function;
    uint8_t* bytecode = function->bytecode.data;
    LayoutTable* table = &function->table;

    uint8_t* locals = &fiber->data_stack.mem.data[frame->bp];

    switch (bytecode[frame->ip]) {
        case OP_UNREACHABLE:
            ctrl_trap(TRAP_UNREACHABLE, "unreachable code executed");

        case OP_NOP: {
            frame->ip += 1;
        } break;

        case OP_CALL: {
            uint8_t fun_idx  = read8(bytecode, frame->ip + 1);
            uint8_t ret_idx  = read8(bytecode, frame->ip + 2);
            uint8_t num_args = read8(bytecode, frame->ip + 3);

            uint8_t* arg_idxs = &bytecode[frame->ip + 4];

            uint8_t* fun_reg = &locals[frame->offsets.data[fun_idx]];
            uint8_t* ret_reg = &locals[frame->offsets.data[ret_idx]];

            Function* new_function = *(Function**) fun_reg;

            size_t num_offsets = new_function->table.num_locals + new_function->table.num_params + 1;

            size_t sp = fiber->data_stack.sp;

            size_t offsets_sp    = alloca(&sp, num_offsets * sizeof(uint16_t), _Alignof(uint16_t));
            size_t new_locals_sp = alloca(&sp, new_function->table.size, new_function->table.align);

            Frame new_frame = {
                .function = new_function,
                .offsets = {
                    .data = &fiber->data_stack.mem.data[offsets_sp],
                    .size = num_offsets
                },
                .old_sp = fiber->data_stack.sp,
                .bp = new_locals_sp,
                .ip = new_function->ep,
            };

            new_frame.offsets.data[0] = calc_relative_offset(frame, new_locals_sp, ret_idx);

            for (size_t i = 0; i < num_args; i++) {
                new_frame.offsets.data[i + 1] = calc_relative_offset(frame, new_locals_sp, arg_idxs[i]);
            }

            for (size_t i = 0; i < new_function->table.num_locals; i++) {
                size_t j = i + num_args + 1;
                new_locals_sp += calc_padding(new_locals_sp, new_function->table.layouts.data[j].align);
                new_frame.offsets.data[j] = new_locals_sp;
                new_locals_sp += new_function->table.layouts.data[j].size;
            }

            fiber->data_stack.sp = sp;

            fiber->call_stack.fp += 1;
            fiber->call_stack.frames.data[fiber->call_stack.fp] = new_frame;

            frame->ip += 1 + 1 + 1 + num_args;
        } break;

        case OP_RET: {
            fiber->data_stack.sp = frame->old_sp;
            fiber->call_stack.fp -= 1;
        } break;

        case OP_ADDR_OF: {
            uint8_t addr_idx =  read8(bytecode, frame->ip + 1);
            uint8_t data_idx =  read8(bytecode, frame->ip + 2);
            uint16_t  offset = read16(bytecode, frame->ip + 3);

            uint8_t* addr_reg = &locals[frame->offsets.data[addr_idx]];
            uint8_t* data_reg = &locals[frame->offsets.data[data_idx]];

            *(uint8_t**) addr_reg = data_reg + offset;

            frame->ip += 1 + 1 + 1 + 2;
        } break;

        case OP_STORE_IMM: {
            uint8_t addr_idx =  read8(bytecode, frame->ip + 1);
            uint16_t    size = read16(bytecode, frame->ip + 2);

            uint8_t* addr_reg = &locals[frame->offsets.data[addr_idx]];

            memcpy(*(uint8_t**) addr_reg, &bytecode[frame->ip + 4], size);

            frame->ip += 1 + 1 + 2 + size;
        } break;

        case OP_STORE: {
            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 2);

            uint8_t* addr_reg = &locals[frame->offsets.data[addr_idx]];
            uint8_t* data_reg = &locals[frame->offsets.data[data_idx]];

            memcpy(*(uint8_t**) addr_reg, data_reg, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;

        case OP_LOAD: {
            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 2);

            uint8_t* addr_reg = &locals[frame->offsets.data[addr_idx]];
            uint8_t* data_reg = &locals[frame->offsets.data[data_idx]];

            memcpy(data_reg, *(uint8_t**) addr_reg, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;
    }

    return CTRL_EXEC;
}
