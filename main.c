#include "stdio.h"
#include "stdint.h"
#include "stdbool.h"
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
    TRAP_OPERAND_OUT_OF_BOUNDS,
    TRAP_SEGMENTATION_FAULT,
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
    uint16_t* local_offsets;
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
    Slice(uint16_t) param_offsets;
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

uint16_t select_reg(Frame* frame, uint8_t idx) {
    uint16_t* a = frame->function->table.local_offsets + idx;
    uint16_t* b = frame->param_offsets.data + (idx - 128);
    return *(idx < 128? a : b); // cmovns https://godbolt.org/z/v6r6ThsWf
}

uint16_t calc_relative_offset(Frame* frame, size_t new_bp, uint8_t idx) {
    return select_reg(frame, idx) + (new_bp - frame->bp);
}

size_t alloca (size_t* sp, size_t size, size_t align) {
    size_t padding = calc_padding(*sp, align);

    size_t out = *sp + padding;
    *sp += size + padding;

    return out;
}

bool validate_data_pointer (Context* ctx, uint8_t* ptr, size_t size) {
    return ptr != NULL
       ; // && is_data_addr(ctx, ptr, size);
}

bool validate_function_pointer (Context* ctx, Function* fn) {
    return fn != NULL
       ; // && is_fun_addr(ctx, fn);
}


CTRL step_bc (Fiber* fiber) {
    Frame* frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
    Function* function = frame->function;
    uint8_t* bytecode = function->bytecode.data;
    LayoutTable* table = &function->table;

    uint8_t* locals = &fiber->data_stack.mem.data[frame->bp];

    ctrl_assert( frame->ip < function->bytecode.size
               , TRAP_IP_OUT_OF_BOUNDS, "IP out of bounds" );

    switch (bytecode[frame->ip]) {
        case OP_UNREACHABLE:
            ctrl_trap(TRAP_UNREACHABLE, "unreachable code executed");

        case OP_NOP: {
            frame->ip += 1;
        } break;

        case OP_CALL: {
            ctrl_assert( frame->ip + 4 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "CALL: missing variables" );

            uint8_t fun_idx  = read8(bytecode, frame->ip + 1);
            uint8_t ret_idx  = read8(bytecode, frame->ip + 2);
            uint8_t num_args = read8(bytecode, frame->ip + 3);

            ctrl_assert( frame->ip + 4 + num_args < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "CALL: missing arguments" );

            uint8_t* arg_idxs = &bytecode[frame->ip + 4];

            ctrl_assert( (fun_idx < table->num_locals) & (ret_idx < table->num_locals)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "CALL: register out of bounds" );

            uint8_t* fun_reg = &locals[select_reg(frame, fun_idx)];
            uint8_t* ret_reg = &locals[select_reg(frame, ret_idx)];

            ctrl_assert( table->layouts.data[fun_reg].size >= sizeof(Function*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "CALL: fun register too small" );

            Function* new_function = *(Function**) fun_reg;

            ctrl_assert( validate_function_pointer(fiber->context, new_function)
                       , TRAP_UNEXPECTED, "CALL: invalid function pointer" );

            size_t num_inputs = new_function->table.num_params + 1;

            size_t sp = fiber->data_stack.sp;

            size_t offsets_sp    = alloca(&sp, num_inputs * sizeof(uint16_t), _Alignof(uint16_t));
            size_t new_locals_sp = alloca(&sp, new_function->table.size, new_function->table.align);
            size_t new_locals_max = new_locals_sp + new_function->table.size;

            ctrl_assert( sp <= fiber->data_stack.mem.size
                       , TRAP_OPERAND_OVERFLOW, "CALL: operand stack overflow" );

            ctrl_assert( fiber->call_stack.fp + 1 < fiber->call_stack.frames.size
                       , TRAP_CALL_OVERFLOW, "CALL: call stack overflow" );

            fiber->call_stack.fp += 1;

            Frame* new_frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
            new_frame->function = new_function;
            new_frame->param_offsets.data = &fiber->data_stack.mem.data[offsets_sp],
            new_frame->param_offsets.size = num_inputs + new_function->table.num_locals,
            new_frame->old_sp = fiber->data_stack.sp,
            new_frame->bp = new_locals_sp,
            new_frame->ip = new_function->ep;

            new_frame->param_offsets.data[0] = calc_relative_offset(frame, new_locals_sp, ret_idx);

            switch (num_args) { // loop -> single branch optimization https://godbolt.org/z/6hebcGraz
                #define CASE(N) case N: new_frame->param_offsets.data[N] = calc_relative_offset(frame, new_locals_sp, arg_idxs[N - 1])
                    CASE(128); CASE(127); CASE(126); CASE(125); CASE(124); CASE(123); CASE(122); CASE(121); CASE(120);
                    CASE(119); CASE(118); CASE(117); CASE(116); CASE(115); CASE(114); CASE(113); CASE(112); CASE(111);
                    CASE(110); CASE(109); CASE(108); CASE(107); CASE(106); CASE(105); CASE(104); CASE(103); CASE(102);
                    CASE(101); CASE(100); CASE( 99); CASE( 98); CASE( 97); CASE( 96); CASE( 95); CASE( 94); CASE( 93);
                    CASE( 92); CASE( 91); CASE( 90); CASE( 89); CASE( 88); CASE( 87); CASE( 86); CASE( 85); CASE( 84);
                    CASE( 83); CASE( 82); CASE( 81); CASE( 80); CASE( 79); CASE( 78); CASE( 77); CASE( 76); CASE( 75);
                    CASE( 74); CASE( 73); CASE( 72); CASE( 71); CASE( 70); CASE( 69); CASE( 68); CASE( 67); CASE( 66);
                    CASE( 65); CASE( 64); CASE( 63); CASE( 62); CASE( 61); CASE( 60); CASE( 59); CASE( 58); CASE( 57);
                    CASE( 56); CASE( 55); CASE( 54); CASE( 53); CASE( 52); CASE( 51); CASE( 50); CASE( 49); CASE( 48);
                    CASE( 47); CASE( 46); CASE( 45); CASE( 44); CASE( 43); CASE( 42); CASE( 41); CASE( 40); CASE( 39);
                    CASE( 38); CASE( 37); CASE( 36); CASE( 35); CASE( 34); CASE( 33); CASE( 32); CASE( 31); CASE( 30);
                    CASE( 29); CASE( 28); CASE( 27); CASE( 26); CASE( 25); CASE( 24); CASE( 23); CASE( 22); CASE( 21);
                    CASE( 20); CASE( 19); CASE( 18); CASE( 17); CASE( 16); CASE( 15); CASE( 14); CASE( 13); CASE( 12);
                    CASE( 11); CASE( 10); CASE(  9); CASE(  8); CASE(  7); CASE(  6); CASE(  5); CASE(  4); CASE(  3);
                    CASE(  2); CASE(  1);
                #undef CASE
                case 0: break;
                default: ctrl_trap(TRAP_UNEXPECTED, "CALL: too many arguments");
            }

            fiber->data_stack.sp = sp;
            frame->ip += 1 + 1 + 1 + num_args;
        } break;

        case OP_RET: {
            fiber->data_stack.sp = frame->old_sp;
            fiber->call_stack.fp -= 1;
        } break;

        case OP_ADDR_OF: {
            ctrl_assert( frame->ip + 5 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "ADDR_OF: missing variables" );

            uint8_t addr_idx =  read8(bytecode, frame->ip + 1);
            uint8_t data_idx =  read8(bytecode, frame->ip + 2);
            uint16_t  offset = read16(bytecode, frame->ip + 3);

            ctrl_assert( (addr_idx < table->num_locals) & (data_idx < table->num_locals)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "ADDR_OF: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(addr_idx)];
            uint8_t* data_reg = &locals[select_reg(data_idx)];

            ctrl_assert( table->layouts.data[addr_reg].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "ADDR_OF: addr register too small" );

            ctrl_assert( table->layouts.data[data_idx].size > offset
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "ADDR_OF: offset out of bounds" );

            *(void**) addr_reg = data_reg + offset;

            frame->ip += 1 + 1 + 1 + 2;
        } break;

        case OP_STORE_IMM: {
            ctrl_assert( frame->ip + 4 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "STORE_IMM: missing variables" );

            uint8_t addr_idx =  read8(bytecode, frame->ip + 1);
            uint16_t    size = read16(bytecode, frame->ip + 2);

            ctrl_assert( frame->ip + 4 + size < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "STORE_IMM: missing immediate data" );

            uint8_t* addr_reg = &locals[select_reg(addr_idx)];

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, size)
                       , TRAP_SEGMENTATION_FAULT, "STORE_IMM: invalid dest addr" );

            memcpy(addr, &bytecode[frame->ip + 4], size);

            frame->ip += 1 + 1 + 2 + size;
        } break;

        case OP_STORE: {
            ctrl_assert( frame->ip + 3 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "STORE: missing variables" );

            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 2);

            ctrl_assert( (addr_idx < table->num_locals) & (data_idx < table->num_locals)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "STORE: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(addr_idx)];
            uint8_t* data_reg = &locals[select_reg(data_idx)];

            ctrl_assert( table->layouts.data[addr_reg].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "STORE: addr register too small" );

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, table->layouts.data[data_idx].size)
                       , TRAP_SEGMENTATION_FAULT, "STORE: invalid dest addr" );

            memcpy(addr, data_reg, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;

        case OP_LOAD: {
            ctrl_assert( frame->ip + 3 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS, "LOAD: missing variables" );

            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 2);

            ctrl_assert( (addr_idx < table->num_locals) & (data_idx < table->num_locals)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "LOAD: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(addr_idx)];
            uint8_t* data_reg = &locals[select_reg(data_idx)];

            ctrl_assert( table->layouts.data[addr_reg].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS, "LOAD: addr register too small" );

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, table->layouts.data[data_idx].size)
                       , TRAP_SEGMENTATION_FAULT, "LOAD: invalid src addr" );

            memcpy(data_reg, addr, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;
    }

    return CTRL_EXEC;
}
