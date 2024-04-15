#include "stdlib.h"
#include "stdio.h"
#include "stdint.h"
#include "stdbool.h"
#include "string.h"

#define todo { fprintf(stderr, "nyi"); exit(1); }

#define SLICE_T(T) struct { T* data; size_t size; }
#define Slice(T) Slice_ ## T

#ifndef __INTELLISENSE__ // intellisense can't handle the backing type attribute
    #define ENUM_T(T) enum : T
#else
    #define ENUM_T(T) enum
#endif

typedef float  float32_t;
typedef double float64_t;


typedef ENUM_T(uint8_t) {
    CTRL_EXEC,
    CTRL_TRAP,
} Control;

typedef ENUM_T(uint8_t) {
    NAT_CTRL_RETURN,
    NAT_CTRL_CONTINUE,
    NAT_CTRL_PROMPT,
    NAT_CTRL_STEP,
    NAT_CTRL_TRAP,
} NativeControl;

typedef ENUM_T(uint8_t) {
    FN_BYTECODE,
    FN_NATIVE,
} FunctionKind;

typedef ENUM_T(uint8_t) {
    TRAP_NOTHING,
    TRAP_UNEXPECTED,
    TRAP_UNREACHABLE,
    TRAP_OPERAND_OVERFLOW,
    TRAP_OPERAND_OUT_OF_BOUNDS,
    TRAP_CALL_OVERFLOW,
    TRAP_IP_OUT_OF_BOUNDS,
    TRAP_HANDLER_OVERFLOW,
} TrapKind;

typedef ENUM_T(uint8_t) {
    // triggers a trap if executed
    // 8xOP
    OP_UNREACHABLE = 255,

    // does nothing
    // 8xOP
    OP_NOP = 0,


    // call the function at the address stored in FUN_REG
    // passing it ARG_REGS as arguments, and placing the result in RET_REG
    // 8xOP + 8xNUM_ARGS + 8xFUN_REG + 8xRET_REG
    // [(8*NUM_ARGS)xARG_REGS]
    OP_CALL,

    // prompt the handler at a given HANDLER_INDEX
    // 8xOP + 16xHANDLER_INDEX + 8xCASE_INDEX + 8xNUM_ARGS + 8xRET_REG
    // [(8*NUM_ARGS)xARG_REGS]
    OP_PROMPT,

    // return from the current function
    // 8xOP
    OP_RET,

    // return control from the current handler
    // 8xOP
    OP_CONTINUE,


    // a block using the HANDLER provided as an immediate to handle the effect at HANDLER_INDEX
    // 8xOP + 16xHANDLER_INDEX + 8xREG in V blocks
    // [sizeof(Handler)xHANDLER]
    OP_WITH_HANDLER, OP_WITH_HANDLER_V,

    // starts a loop block; never yields a value.
    // also ends a loop block, when used inside a loop with the same LABEL
    // 8xOP + 16xLABEL
    OP_LOOP,

    // a pair of if/else blocks
    // 8xOP + 16xLABEL + 16xLABEL + 8xREG in V blocks
    OP_COND, OP_COND_V,

    // an unconditional block
    // 8xOP + 16xLABEL + 8xREG in V blocks
    OP_BLOCK, OP_BLOCK_V,

    // in a loop, jump to the start of the loop
    // in any other block, jump to the end, optionally yielding a value
    // 8xOP + 16xLABEL + 8xREG for the yielded value in V blocks
    OP_BR,

    // terminate a block, yielding an immediate value to be used as the output value
    // 8xOP + 16xSIZE
    // [SIZExIMM]
    OP_BR_IMM,

    // if the value stored in COND_REG is non-zero in the lower byte,
    // in a loop, jump to the start of the loop
    // in any other block, jump to the end, optionally yielding a value
    // 8xOP + 16xLABEL + 8xCOND_REG + 8xREG for the yielded value in V blocks
    OP_BR_IF,

    // if the value stored in COND_REG is non-zero in the lower byte,
    // terminate a block, yielding an immediate value to be used as the output value
    // 8xOP + 16xLABEL + 8xCOND_REG + 16xSIZE
    // [SIZExIMM]
    OP_BR_IF_IMM,


    // copy the address of a register in a DATA_REG
    // of the current handler's parent frame pointer
    // into ADDR_REG of the current frame,
    // applying OFFSET to the address
    // 8xOP + 16xOFFSET + 8xADDR_REG
    OP_UP_VALUE_ADDR,

    // copy the address of DATA_REG into ADDR_REG, applying OFFSET to the address
    // 8xOP + 16xOFFSET + 8xADDR_REG + 8xDATA_REG
    OP_ADDR_OF,

    // store the immediate value into the address in ADDR_REG
    // 8xOP + 16xSIZE + 8xADDR_REG
    // [SIZExIMM]
    OP_STORE_IMM,

    // copy the value from DATA_REG to the address in ADDR_REG
    // 8xOP + 8xADDR_REG + 8xDATA_REG
    OP_STORE,

    // copy the value from the address in ADDR_REG to DATA_REG
    // 8xOP + 8xADDR_REG + 8xDATA_REG
    OP_LOAD,


    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform integer addition, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_IADD8, OP_IADD16, OP_IADD32, OP_IADD64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform integer subtraction, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_ISUB8, OP_ISUB16, OP_ISUB32, OP_ISUB64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform integer multiplication, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_IMUL8, OP_IMUL16, OP_IMUL32, OP_IMUL64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform unsigned integer division, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_UDIV8, OP_UDIV16, OP_UDIV32, OP_UDIV64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform signed integer division, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_SDIV8, OP_SDIV16, OP_SDIV32, OP_SDIV64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform unsigned integer modulo, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_UMOD8, OP_UMOD16, OP_UMOD32, OP_UMOD64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform signed integer modulo, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_SMOD8, OP_SMOD16, OP_SMOD32, OP_SMOD64,

    // load a SIZE value from IN_REG
    // and perform integer negation, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_INEG8, OP_INEG16, OP_INEG32, OP_INEG64,

    // load two SIZE values from LEFT_REG and RIGHT_REG
    // and perform integer comparison of the given KIND, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_IEQ8, OP_IEQ16, OP_IEQ32, OP_IEQ64,
    OP_INE8, OP_INE16, OP_INE32, OP_INE64,
    OP_ILT8, OP_ILT16, OP_ILT32, OP_ILT64,
    OP_ILE8, OP_ILE16, OP_ILE32, OP_ILE64,
    OP_IGT8, OP_IGT16, OP_IGT32, OP_IGT64,
    OP_IGE8, OP_IGE16, OP_IGE32, OP_IGE64,


    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform floating point addition, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FADD32, OP_FADD64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform floating point subtraction, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FSUB32, OP_FSUB64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform floating point multiplication, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FMUL32, OP_FMUL64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform floating point division, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FDIV32, OP_FDIV64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform floating point modulo, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FMOD32, OP_FMOD64,

    // load a SIZE value from IN_REG
    // and perform floating point negation, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_FNEG32, OP_FNEG64,

    // load two SIZE values from LEFT_REG and RIGHT_REG
    // and perform floating point comparison of the given TYPE, placing the result in OUT_REG
    // 8xOP_AND_KIND + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_FEQ32, OP_FEQ64,
    OP_FNE32, OP_FNE64,
    OP_FLT32, OP_FLT64,
    OP_FLE32, OP_FLE64,
    OP_FGT32, OP_FGT64,
    OP_FGE32, OP_FGE64,


    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform a left shift of the LEFT_REG by the RIGHT_REG, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_SHL8, OP_SHL16, OP_SHL32, OP_SHL64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform an arithmetic right shift of the LEFT_REG by the RIGHT_REG, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_ASHR8, OP_ASHR16, OP_ASHR32, OP_ASHR64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform a logical right shift of the LEFT_REG by the RIGHT_REG, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_LSHR8, OP_LSHR16, OP_LSHR32, OP_LSHR64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform a bitwise AND, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_BAND8, OP_BAND16, OP_BAND32, OP_BAND64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform a bitwise OR, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_BOR8, OP_BOR16, OP_BOR32, OP_BOR64,

    // load two SIZE values from LEFT_REG and RIGHT_REG registers
    // and perform a bitwise XOR, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xLEFT_REG + 8xRIGHT_REG
    OP_BXOR8, OP_BXOR16, OP_BXOR32, OP_BXOR64,

    // load a SIZE value from IN_REG
    // and perform a bitwise NOT, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_BNOT8, OP_BNOT16, OP_BNOT32, OP_BNOT64,


    // zero-extend a SIZE integer value from IN_REG to a larger SIZE, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_ZEXT_8_16,  OP_ZEXT_8_32,  OP_ZEXT_8_64,
    OP_ZEXT_16_32, OP_ZEXT_16_64,
    OP_ZEXT_32_64,

    // sign-extend a SIZE integer value from IN_REG to a larger SIZE, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_SEXT_8_16,  OP_SEXT_8_32,  OP_SEXT_8_64,
    OP_SEXT_16_32, OP_SEXT_16_64,
    OP_SEXT_32_64,

    // truncate a SIZE integer value from IN_REG to a smaller SIZE, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_ITRUNC_64_32, OP_ITRUNC_64_16, OP_ITRUNC_64_8,
    OP_ITRUNC_32_16, OP_ITRUNC_32_8,
    OP_ITRUNC_16_8,

    // extend a SIZE floating point value from IN_REG to the larger SIZE, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_FEXT,

    // truncate a SIZE floating point value from IN_REG to the smaller SIZE, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_FTRUNC,

    // convert a SIZE signed integer value from IN_REG to a SIZE floating point value, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_S32_TO_F32, OP_S64_TO_F64,

    // convert a SIZE floating point value from IN_REG to a SIZE signed integer value, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_F32_TO_S32, OP_F64_TO_S64,

    // convert a SIZE unsigned integer value from IN_REG to a SIZE floating point value, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_U32_TO_F32, OP_U64_TO_F64,

    // convert a SIZE floating point value from IN_REG to a SIZE unsigned integer value, placing the result in OUT_REG
    // 8xOP + 8xOUT_REG + 8xIN_REG
    OP_F32_TO_U32, OP_F64_TO_U64,
} OpCode;

typedef struct DataStack DataStack;
typedef struct Block Block;
typedef struct Bytecode Bytecode;
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

typedef NativeControl (*Native) (Fiber*);

typedef SLICE_T(uint8_t)   Slice(uint8_t);
typedef SLICE_T(OpCode)    Slice(OpCode);
typedef SLICE_T(uint16_t)  Slice(uint16_t);
typedef SLICE_T(Layout)    Slice(Layout);
typedef SLICE_T(Block)     Slice(Block);
typedef SLICE_T(Frame)     Slice(Frame);
typedef SLICE_T(Function*) Slice(Function);
typedef SLICE_T(Handler)   Slice(Handler);


struct Layout {
    uint16_t size;
    uint16_t align;
};

struct Block {
    uint16_t base;
    uint16_t size;
    uint16_t parent;
    uint16_t next;
};

#define NIL_BLOCK 0xFFFF

struct LayoutTable {
    Slice(Layout) layouts;
    uint16_t* local_offsets;
    uint32_t size;
    uint16_t align;
    uint8_t num_params;
    uint8_t num_locals;
};

struct Bytecode {
    Slice(OpCode) instructions;
    Slice(Block) blocks;
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
    Handler* handler;
    Slice(uint16_t) param_offsets;
    size_t old_sp;
    size_t bp;
    uint16_t ipb;
    uint16_t ipi;
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


#define read8(mem, ip) \
    (mem[ip])          \

#define read16(mem, ip)                 \
    ( (((uint16_t) mem[ip + 0]) << 8)   \
    | (((uint16_t) mem[ip + 1]) << 0) ) \

#define read32(mem, ip)                  \
    ( (((uint32_t) mem[ip + 0]) << 24)   \
    | (((uint32_t) mem[ip + 1]) << 16)   \
    | (((uint32_t) mem[ip + 2]) <<  8)   \
    | (((uint32_t) mem[ip + 3]) <<  0) ) \

#define read64(mem, ip)                  \
    ( (((uint64_t) mem[ip + 0]) << 56)   \
    | (((uint64_t) mem[ip + 1]) << 48)   \
    | (((uint64_t) mem[ip + 2]) << 40)   \
    | (((uint64_t) mem[ip + 3]) << 32)   \
    | (((uint64_t) mem[ip + 4]) << 24)   \
    | (((uint64_t) mem[ip + 5]) << 16)   \
    | (((uint64_t) mem[ip + 6]) <<  8)   \
    | (((uint64_t) mem[ip + 7]) <<  0) ) \


#define ctrl_trap(trap_kind, trap_message) { \
    fiber->trap.kind = trap_kind;            \
    fiber->trap.message = trap_message;      \
    return CTRL_TRAP;                        \
}                                            \

#define ctrl_assert(cond, trap_kind, trap_message)  \
    if (!(cond)) ctrl_trap(trap_kind, trap_message) \

#define calc_padding(addr, align)       \
    ((addr + align - 1) & ~(align - 1)) \

#define validate_reg(table, idx)         \
    (idx < 128                           \
        ? idx < table->num_params + 1    \
        : idx - 128 < table->num_locals) \

#define select_reg(frame, idx)                       \
    (*(idx < 128                                     \
        ? frame->function->table.local_offsets + idx \
        : frame->param_offsets.data + (idx - 128)))  \

#define calc_relative_offset(frame, new_bp, idx)    \
    (select_reg(frame, idx) + (new_bp - frame->bp)) \

#define validate_data_pointer(ctx, ptr, size) \
    (ptr != NULL)                             \
    // && is_data_addr(ctx, ptr, size);

#define validate_function_pointer(ctx, fn) \
    (fn != NULL)                           \
    // && is_function_addr(ctx, ptr, size);

#define stack_alloc(sp, size, align)        \
    ( sp += calc_padding(*sp, align) + size \
    , sp - size )                           \


Control step_bc (Fiber* fiber) {
    Frame* frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
    Function* function = frame->function;
    Bytecode* bytecode = function->bytecode;
    LayoutTable* table = &function->table;

    uint8_t* locals = &fiber->data_stack.mem.data[frame->bp];

    ctrl_assert( frame->ipb < bytecode->blocks.size
               , TRAP_IP_OUT_OF_BOUNDS
               , "ipb out of bounds" );

    ctrl_assert( frame->ipi < bytecode->blocks.data[frame->ipb].size
               , TRAP_IP_OUT_OF_BOUNDS
               , "ipi out of bounds" );

    switch (bytecode->instructions.data[bytecode->blocks.data[frame->ipb].base + frame->ipi]) {
        case OP_UNREACHABLE:
            ctrl_trap(TRAP_UNREACHABLE, "unreachable code executed");


        case OP_NOP: {
            frame->ipi += 1;
        } break;


        OP_CALL: {
            todo
        } break;


        OP_PROMPT: {
            todo
        } break;


        OP_RET: {
            todo
        } break;


        OP_CONTINUE: {
            todo
        } break;


        OP_WITH_HANDLER: {
            todo
        } break;


        OP_WITH_HANDLER_V: {
            todo
        } break;


        OP_LOOP: {
            todo
        } break;


        OP_COND: {
            todo
        } break;


        OP_COND_V: {
            todo
        } break;


        OP_BLOCK: {
            todo
        } break;


        OP_BLOCK_V: {
            todo
        } break;


        OP_BR: {
            todo
        } break;


        OP_BR_IMM: {
            todo
        } break;


        OP_BR_IF: {
            todo
        } break;


        OP_BR_IF_IMM: {
            todo
        } break;


        OP_UP_VALUE_ADDR: {
            todo
        } break;


        OP_ADDR_OF: {
            todo
        } break;


        OP_STORE_IMM: {
            todo
        } break;


        OP_STORE: {
            todo
        } break;


        OP_LOAD: {
            todo
        } break;


        default:
            ctrl_trap(TRAP_UNEXPECTED, "Unexpected opcode");
    }

    return CTRL_EXEC;
}


int main (int argc, char** args) {
    return 0;
}
