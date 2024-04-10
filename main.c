#include "stdio.h"
#include "stdint.h"
#include "stdbool.h"
#include "string.h"


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
    TRAP_SEGMENTATION_FAULT,
    TRAP_CALL_OVERFLOW,
    TRAP_CALL_UNDERFLOW,
    TRAP_IP_OUT_OF_BOUNDS,
    TRAP_HANDLER_OVERFLOW,
    TRAP_HANDLER_MISSING,
} TrapKind;

typedef ENUM_T(uint8_t) {
    // triggers a trap if executed
    // 8xOP
    OP_UNREACHABLE = 255,

    // does nothing
    // 8xOP
    OP_NOP = 0,


    // call the function at the address stored in FUN_REG
    // 8xOP + 8xNUM_ARGS + 8xFUN_REG + 8xRET_REG
    // [(8*NUM_ARGS)xARG_REGS]
    OP_CALL,

    // return from the current function
    // 8xOP
    OP_RET,

    // jump to the designated offset in the function
    // 8xOP + 16xOFFSET
    OP_JMP,

    // jump to the designated offset in the function
    // if the value stored in COND_REG is non-zero in the lower byte
    // 8xOP + 16xOFFSET + 8xCOND_REG
    OP_JMP_IF,


    // create a handler from FUN_COUNT functions at the addresses stored in FUN_REGS,
    // placing the result in OUT_REG
    // 8xOP + 8xFUN_COUNT + 8xOUT_REG
    // [(FUN_COUNT*8)xFUN_REG]
    OP_NEW_HANDLER,

    // copy the handler from the IN_REG into the handler vector at the HANDLER_INDEX
    // offsets the handlers thereafter
    // 8xOP + 16xHANDLER_INDEX + 8xIN_REG
    OP_INSERT_HANDLER,

    // copy the handler from the HANDLER_INDEX in the handler vector into the INOUT_REG,
    // replacing the handler at that index with the one that was in INOUT_REG
    // 8xOP + 16xHANDLER_INDEX + 8xINOUT_REG
    OP_SWAP_HANDLER,

    // copy the HANDLER_INDEX from the handler vector, placing it in the OUT_REG
    // 8xOP + 16xHANDLER_INDEX + 8xOUT_REG
    OP_COPY_HANDLER,

    // remove the HANDLER_INDEX from the handler vector
    // offsets the handlers thereafter
    // 8xOP + 16xHANDLER_INDEX
    OP_REMOVE_HANDLER,



    // Prompt the handler at a given HANDLER_INDEX
    // 8xOP + 8xNUM_ARGS + 16xHANDLER_INDEX + 8xRET_REG
    // [(8*NUM_ARGS)xARG_REGS]
    OP_PROMPT,

    // Return control from the current handler
    // 8xOP
    OP_CONTINUE,


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

typedef NativeControl (*Native) (Fiber*);

typedef SLICE_T(uint8_t)  Slice(uint8_t);
typedef SLICE_T(uint16_t) Slice(uint16_t);
typedef SLICE_T(Layout)   Slice(Layout);
typedef SLICE_T(Frame)    Slice(Frame);
typedef SLICE_T(Function*) Slice(Function*);
typedef SLICE_T(Handler)  Slice(Handler);


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
    Slice(Function*) cases;
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


static inline
uint8_t read8 (uint8_t const* mem, size_t ip) {
    return mem[ip];
}

static inline
uint16_t read16 (uint8_t const* mem, size_t ip) {
    return (((uint16_t) mem[ip + 0]) << 8)
         | (((uint16_t) mem[ip + 1]) << 0)
         ;
}

static inline
uint32_t read32 (uint8_t const* mem, size_t ip) {
    return (((uint32_t) mem[ip + 0]) << 24)
         | (((uint32_t) mem[ip + 1]) << 16)
         | (((uint32_t) mem[ip + 2]) <<  8)
         | (((uint32_t) mem[ip + 3]) <<  0)
         ;
}

static inline
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


static inline
size_t calc_padding (size_t addr, size_t align) {
    return (addr + align - 1) & ~(align - 1);
}

static inline
bool validate_reg (LayoutTable* table, uint8_t idx) {
    return (idx < 128? idx < table->num_params + 1 : idx - 128 < table->num_locals);
}

static inline
uint16_t select_reg (Frame* frame, uint8_t idx) {
    uint16_t* a = frame->function->table.local_offsets + idx;
    uint16_t* b = frame->param_offsets.data + (idx - 128);
    return *(idx < 128? a : b); // cmovns https://godbolt.org/z/v6r6ThsWf
}

static inline
uint16_t calc_relative_offset (Frame* frame, size_t new_bp, uint8_t idx) {
    return select_reg(frame, idx) + (new_bp - frame->bp);
}

static inline
size_t stack_alloc (size_t* sp, size_t size, size_t align) {
    size_t padding = calc_padding(*sp, align);

    size_t out = *sp + padding;
    *sp += size + padding;

    return out;
}

static inline
bool validate_data_pointer (Context* ctx, uint8_t* ptr, size_t size) {
    return ptr != NULL
       ; // && is_data_addr(ctx, ptr, size);
}

static inline
bool validate_function_pointer (Context* ctx, Function* fn) {
    return fn != NULL
       ; // && is_fun_addr(ctx, fn);
}


Control step_bc (Fiber* fiber) {
    Frame* frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
    Function* function = frame->function;
    uint8_t* bytecode = function->bytecode.data;
    LayoutTable* table = &function->table;

    uint8_t* locals = &fiber->data_stack.mem.data[frame->bp];

    ctrl_assert( frame->ip < function->bytecode.size
               , TRAP_IP_OUT_OF_BOUNDS
               , "IP out of bounds" );

    switch (bytecode[frame->ip]) {
        case OP_UNREACHABLE:
            ctrl_trap(TRAP_UNREACHABLE, "unreachable code executed");


        case OP_NOP: {
            frame->ip += 1;
        } break;


        case OP_CALL: {
            ctrl_assert( frame->ip + 1 + 1 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "CALL: missing variables" );

            uint8_t num_args = read8(bytecode, frame->ip + 1);
            uint8_t fun_idx  = read8(bytecode, frame->ip + 1 + 1);
            uint8_t ret_idx  = read8(bytecode, frame->ip + 1 + 1 + 1);

            ctrl_assert( frame->ip + 4 + num_args < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "CALL: missing arguments" );

            uint8_t* arg_idxs = &bytecode[frame->ip + 1 + 1 + 1 + 1];

            ctrl_assert( validate_reg(table, fun_idx)
                       & validate_reg(table, ret_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "CALL: register out of bounds" );

            uint8_t* fun_reg = &locals[select_reg(frame, fun_idx)];
            uint8_t* ret_reg = &locals[select_reg(frame, ret_idx)];

            ctrl_assert( table->layouts.data[fun_idx].size >= sizeof(Function*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "CALL: fun register too small" );

            Function* new_function = *(Function**) fun_reg;

            ctrl_assert( validate_function_pointer(fiber->context, new_function)
                       , TRAP_UNEXPECTED
                       , "CALL: invalid function pointer" );

            size_t num_inputs = new_function->table.num_params + 1;

            size_t sp = fiber->data_stack.sp;

            size_t offsets_sp     = stack_alloc(&sp, num_inputs * sizeof(uint16_t), _Alignof(uint16_t));
            size_t new_locals_sp  = stack_alloc(&sp, new_function->table.size, new_function->table.align);
            size_t new_locals_max = new_locals_sp + new_function->table.size;

            ctrl_assert( sp <= fiber->data_stack.mem.size
                       , TRAP_OPERAND_OVERFLOW
                       , "CALL: operand stack overflow" );

            ctrl_assert( fiber->call_stack.fp + 1 < fiber->call_stack.frames.size
                       , TRAP_CALL_OVERFLOW
                       , "CALL: call stack overflow" );

            fiber->call_stack.fp += 1;

            Frame* new_frame = &fiber->call_stack.frames.data[fiber->call_stack.fp];
            new_frame->function = new_function;
            new_frame->param_offsets.data = (void*) &fiber->data_stack.mem.data[offsets_sp],
            new_frame->param_offsets.size = num_inputs + new_function->table.num_locals,
            new_frame->old_sp = fiber->data_stack.sp,
            new_frame->bp = new_locals_sp,
            new_frame->ip = new_function->ep;

            new_frame->param_offsets.data[0] = calc_relative_offset(frame, new_locals_sp, ret_idx);

            switch (num_args) { // loop -> single branch optimization https://godbolt.org/z/6hebcGraz
                case 0: break;

                #define CASE(N)                                                                                         \
                    case N: {                                                                                           \
                        ctrl_assert( validate_reg(table, arg_idxs[N - 1])                                               \
                                   , TRAP_OPERAND_OUT_OF_BOUNDS                                                         \
                                   , "CALL: argument register out of bounds" );                                         \
                        new_frame->param_offsets.data[N] = calc_relative_offset(frame, new_locals_sp, arg_idxs[N - 1]); \
                    }                                                                                                   \

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

                default:
                    ctrl_trap(TRAP_UNEXPECTED, "CALL: too many arguments");
            }

            fiber->data_stack.sp = sp;
            frame->ip += 1 + 1 + 1 + num_args;
        } break;


        case OP_RET: {
            fiber->data_stack.sp = frame->old_sp;
            fiber->call_stack.fp -= 1;
        } break;


        case OP_JMP: {
            ctrl_assert( frame->ip + 1 + 2 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "JMP: missing offset" );

            int16_t offset = read16(bytecode, frame->ip + 1);

            ctrl_assert( frame->ip + 1 + 2 + offset < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "JMP: offset out of bounds" );

            frame->ip += 1 + 2 + offset;
        } break;


        case OP_JMP_IF: {
            ctrl_assert( frame->ip + 1 + 2 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "JMP_IF: missing offset" );

            int16_t   offset = read16(bytecode, frame->ip + 1);
            uint8_t cond_idx =  read8(bytecode, frame->ip + 1 + 2);

            ctrl_assert( frame->ip + 1 + 2 + 1 + offset < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "JMP: offset out of bounds" );

            ctrl_assert( validate_reg(table, cond_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "JMP_IF: register out of bounds" );

            uint8_t* cond_reg = &locals[select_reg(frame, cond_idx)];

            frame->ip += 1 + 1 + 2;

            if (*cond_reg != 0) {
                frame->ip += offset;
            }
        } break;


        case OP_NEW_HANDLER: {
            ctrl_assert( frame->ip + 1 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "NEW_HANDLER: missing variables" );

            uint8_t fun_count = read8(bytecode, frame->ip + 1);
            uint8_t out_idx   = read8(bytecode, frame->ip + 1 + 1);

            ctrl_assert( frame->ip + 1 + 1 + 1 + fun_count < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "NEW_HANDLER: missing functions" );

            uint8_t* fun_idxs = &bytecode[frame->ip + 1 + 1 + 1];

            ctrl_assert( validate_reg(table, out_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "NEW_HANDLER: register out of bounds" );

            uint8_t* out_reg = &locals[select_reg(frame, out_idx)];

            ctrl_assert( table->layouts.data[out_idx].size >= sizeof(Handler)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "NEW_HANDLER: out register too small" );

            Handler* handler = (Handler*) out_reg;

            size_t sp = fiber->data_stack.sp;

            size_t cases_sp = stack_alloc(&sp, fun_count * sizeof(Function), _Alignof(Function));

            ctrl_assert( sp <= fiber->data_stack.mem.size
                       , TRAP_OPERAND_OVERFLOW
                       , "NEW_HANDLER: operand stack overflow" );

            Function* cases = (Function*) &fiber->data_stack.mem.data[cases_sp];

            switch (fun_count) {
                case 0: break;


                #define CASE(N)                                                              \
                    case N: {                                                                \
                        ctrl_assert( validate_reg(table, fun_idxs[N])                        \
                                   , TRAP_OPERAND_OUT_OF_BOUNDS                              \
                                   , "NEW_HANDLER: function register out of bounds" );       \
                                                                                             \
                        Function* fun = (Function*) &locals[select_reg(frame, fun_idxs[N])]; \
                                                                                             \
                        ctrl_assert( validate_function_pointer(fiber->context, fun)          \
                                   , TRAP_UNEXPECTED                                         \
                                   , "NEW_HANDLER: invalid function pointer" );              \
                                                                                             \
                        cases[N] = fun;                                                      \
                    }                                                                        \

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


                default:
                    ctrl_trap(TRAP_UNEXPECTED, "NEW_HANDLER: too many functions");
            }

            handler->cases.data = cases;
            handler->cases.size = fun_count;
            handler->fp = fiber->call_stack.fp;

            fiber->data_stack.sp = sp;

            frame->ip += 1 + 1 + 1 + fun_count;
        } break;


        case OP_INSERT_HANDLER: {
            ctrl_assert( fiber->handler_vector.handlers.size < fiber->handler_vector.handlers.capacity
                       , TRAP_HANDLER_OVERFLOW
                       , NULL );

            ctrl_assert( frame->ip + 1 + 2 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "INSERT_HANDLER: missing variables" );

            uint16_t handler_idx = read16(bytecode, frame->ip + 1);
            uint8_t       in_idx =  read8(bytecode, frame->ip + 1 + 2);

            ctrl_assert( validate_reg(table, in_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "INSERT_HANDLER: register out of bounds" );

            uint8_t* in_reg = &locals[select_reg(frame, in_idx)];

            ctrl_assert( table->layouts.data[in_idx].size >= sizeof(Handler)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "INSERT_HANDLER: in register too small" );

            Handler* handler = (Handler*) in_reg;

            ctrl_assert( handler_idx <= fiber->handler_vector.handlers.size
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "INSERT_HANDLER: handler index out of bounds" );

            memmove( &fiber->handler_vector.handlers.data[handler_idx + 1]
                   , &fiber->handler_vector.handlers.data[handler_idx]
                   , (fiber->handler_vector.handlers.size - handler_idx) * sizeof(Handler));

            fiber->handler_vector.handlers.data[handler_idx] = *handler;

            frame->ip += 1 + 2 + 1;
        } break;


        case OP_SWAP_HANDLER: {
            ctrl_assert( frame->ip + 1 + 2 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "SWAP_HANDLER: missing variables" );

            uint16_t handler_idx = read16(bytecode, frame->ip + 1);
            uint8_t    inout_idx =  read8(bytecode, frame->ip + 1 + 2);

            ctrl_assert( handler_idx < fiber->handler_vector.handlers.size
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "SWAP_HANDLER: handler index out of bounds" );

            ctrl_assert( validate_reg(table, inout_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "SWAP_HANDLER: register out of bounds" );

            uint8_t* inout_reg = &locals[select_reg(frame, inout_idx)];

            ctrl_assert( table->layouts.data[inout_idx].size >= sizeof(Handler)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "SWAP_HANDLER: inout register too small" );

            Handler* inout = (Handler*) inout_reg;

            Handler tmp = fiber->handler_vector.handlers.data[handler_idx];

            fiber->handler_vector.handlers.data[handler_idx] = *inout;
            *inout = tmp;

            frame->ip += 1 + 2;
        } break;


        case OP_COPY_HANDLER: {
            ctrl_assert( frame->ip + 1 + 2 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "TAKE_HANDLER: missing variables" );

            uint16_t handler_idx = read16(bytecode, frame->ip + 1);
            uint8_t      out_idx =  read8(bytecode, frame->ip + 1 + 2);

            ctrl_assert( handler_idx < fiber->handler_vector.handlers.size
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "TAKE_HANDLER: handler index out of bounds" );

            ctrl_assert( validate_reg(table, out_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "TAKE_HANDLER: register out of bounds" );

            uint8_t* out_reg = &locals[select_reg(frame, out_idx)];

            ctrl_assert( table->layouts.data[out_idx].size >= sizeof(Handler)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "TAKE_HANDLER: out register too small" );

            Handler* out = (Handler*) out_reg;

            *out = fiber->handler_vector.handlers.data[handler_idx];

            frame->ip += 1 + 1;
        } break;


        case OP_REMOVE_HANDLER: {
            ctrl_assert( frame->ip + 1 + 2 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "REMOVE_HANDLER: missing variables" );

            uint16_t handler_idx = read16(bytecode, frame->ip + 1);

            ctrl_assert( handler_idx < fiber->handler_vector.handlers.size
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "REMOVE_HANDLER: handler index out of bounds" );

            memmove( &fiber->handler_vector.handlers.data[handler_idx]
                   , &fiber->handler_vector.handlers.data[handler_idx + 1]
                   , (fiber->handler_vector.handlers.size - handler_idx - 1) * sizeof(Handler));

            frame->ip += 1 + 2;
        } break;


        case OP_PROMPT: {
            // TODO
        } break;


        case OP_CONTINUE: {
            // TODO
        } break;


        case OP_UP_VALUE_ADDR: {
            ctrl_assert( frame->ip + 1 + 2 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "UP_VALUE_ADDR: missing variables" );

            uint16_t  offset = read16(bytecode, frame->ip + 1);
            uint8_t addr_idx =  read8(bytecode, frame->ip + 1 + 2);
            uint8_t data_idx =  read8(bytecode, frame->ip + 1 + 2 + 1);

            // TODO: get the frame of the handler
            // we need to store this somewhere
            Frame* up_frame;

            ctrl_assert( validate_reg(table, addr_idx)
                       & validate_reg(&up_frame->table, data_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "UP_VALUE_ADDR: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(frame, addr_idx)];
            uint8_t* data_reg = &locals[select_reg(up_frame, data_idx)];

            ctrl_assert( table->layouts.data[addr_idx].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "UP_VALUE_ADDR: addr register too small" );

            void** addr = (void**) addr_reg;

            ctrl_assert( up_frame->table.layouts.data[data_idx].size > offset
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "UP_VALUE_ADDR: offset out of bounds" );

            *addr = data_reg + offset;

            frame->ip += 1 + 2 + 1 + 1;
        } break;


        case OP_ADDR_OF: {
            ctrl_assert( frame->ip + 1 + 2 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "ADDR_OF: missing variables" );

            uint16_t  offset = read16(bytecode, frame->ip + 1);
            uint8_t addr_idx =  read8(bytecode, frame->ip + 1 + 2);
            uint8_t data_idx =  read8(bytecode, frame->ip + 1 + 2 + 1);

            ctrl_assert( validate_reg(table, addr_idx)
                       & validate_reg(table, data_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "ADDR_OF: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(frame, addr_idx)];
            uint8_t* data_reg = &locals[select_reg(frame, data_idx)];

            ctrl_assert( table->layouts.data[addr_idx].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "ADDR_OF: addr register too small" );

            void** addr = (void**) addr_reg;

            ctrl_assert( table->layouts.data[data_idx].size > offset
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "ADDR_OF: offset out of bounds" );

            *addr = data_reg + offset;

            frame->ip += 1 + 2 + 1 + 1;
        } break;


        case OP_STORE_IMM: {
            ctrl_assert( frame->ip + 1 + 2 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "STORE_IMM: missing variables" );

            uint16_t    size = read16(bytecode, frame->ip + 1);
            uint8_t addr_idx =  read8(bytecode, frame->ip + 1 + 2);

            ctrl_assert( frame->ip + 4 + size < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "STORE_IMM: missing immediate data" );

            ctrl_assert( validate_reg(table, addr_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "STORE_IMM: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(frame, addr_idx)];

            ctrl_assert( table->layouts.data[addr_idx].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "STORE_IMM: addr register too small" );

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, size)
                       , TRAP_SEGMENTATION_FAULT
                       , "STORE_IMM: invalid dest addr" );

            memcpy(addr, &bytecode[frame->ip + 1 + 1 + 2], size);

            frame->ip += 1 + 1 + 2 + size;
        } break;


        case OP_STORE: {
            ctrl_assert( frame->ip + 1 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "STORE: missing variables" );

            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 1 + 1);

            ctrl_assert( validate_reg(table, addr_idx)
                       & validate_reg(table, data_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "STORE: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(frame, addr_idx)];
            uint8_t* data_reg = &locals[select_reg(frame, data_idx)];

            ctrl_assert( table->layouts.data[addr_idx].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "STORE: addr register too small" );

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, table->layouts.data[data_idx].size)
                       , TRAP_SEGMENTATION_FAULT
                       , "STORE: invalid dest addr" );

            memcpy(addr, data_reg, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;


        case OP_LOAD: {
            ctrl_assert( frame->ip + 1 + 1 + 1 < function->bytecode.size
                       , TRAP_IP_OUT_OF_BOUNDS
                       , "LOAD: missing variables" );

            uint8_t addr_idx = read8(bytecode, frame->ip + 1);
            uint8_t data_idx = read8(bytecode, frame->ip + 1 + 1);

            ctrl_assert( validate_reg(table, addr_idx)
                       & validate_reg(table, data_idx)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "LOAD: register out of bounds" );

            uint8_t* addr_reg = &locals[select_reg(frame, addr_idx)];
            uint8_t* data_reg = &locals[select_reg(frame, data_idx)];

            ctrl_assert( table->layouts.data[addr_idx].size >= sizeof(void*)
                       , TRAP_OPERAND_OUT_OF_BOUNDS
                       , "LOAD: addr register too small" );

            void* addr = *(void**) addr_reg;

            ctrl_assert( validate_data_pointer(fiber->context, addr, table->layouts.data[data_idx].size)
                       , TRAP_SEGMENTATION_FAULT
                       , "LOAD: invalid src addr" );

            memcpy(data_reg, addr, table->layouts.data[data_idx].size);

            frame->ip += 1 + 1 + 1;
        } break;


        #define BIN(NAME, OP, TYPE, SIZE)                                         \
            case OP_ ## NAME ## SIZE: {                                           \
                ctrl_assert(frame->ip + 1 + 1 + 1 + 1 < function->bytecode.size   \
                           , TRAP_IP_OUT_OF_BOUNDS, #NAME ": missing operands" ); \
                                                                                  \
                uint8_t out_idx = read8(bytecode, frame->ip + 1);                 \
                uint8_t lhs_idx = read8(bytecode, frame->ip + 1 + 1);             \
                uint8_t rhs_idx = read8(bytecode, frame->ip + 1 + 1 + 1);         \
                                                                                  \
                ctrl_assert( validate_reg(table, out_idx)                         \
                           & validate_reg(table, lhs_idx)                         \
                           & validate_reg(table, rhs_idx)                         \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register out of bounds" );                  \
                                                                                  \
                uint8_t* out_reg = &locals[select_reg(frame, out_idx)];           \
                uint8_t* lhs_reg = &locals[select_reg(frame, lhs_idx)];           \
                uint8_t* rhs_reg = &locals[select_reg(frame, rhs_idx)];           \
                                                                                  \
                ctrl_assert( table->layouts.data[out_idx].size >= SIZE / 8        \
                           & table->layouts.data[lhs_idx].size >= SIZE / 8        \
                           & table->layouts.data[rhs_idx].size >= SIZE / 8        \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register too small" );                      \
                                                                                  \
                TYPE ## SIZE ## _t* out = (TYPE ## SIZE ## _t*) out_reg;          \
                TYPE ## SIZE ## _t* lhs = (TYPE ## SIZE ## _t*) lhs_reg;          \
                TYPE ## SIZE ## _t* rhs = (TYPE ## SIZE ## _t*) rhs_reg;          \
                                                                                  \
                *out = *lhs OP *rhs;                                              \
                                                                                  \
                frame->ip += 1 + 1 + 1 + 1;                                       \
            } break;                                                              \

        #define BINx4(NAME, OP, TYPE) \
            BIN(NAME, OP, TYPE,  8);  \
            BIN(NAME, OP, TYPE, 16);  \
            BIN(NAME, OP, TYPE, 32);  \
            BIN(NAME, OP, TYPE, 64);  \

        #define BINx2(NAME, OP, TYPE) \
            BIN(NAME, OP, TYPE, 32);  \
            BIN(NAME, OP, TYPE, 64);  \

        BINx4(IADD, +, uint);
        BINx4(ISUB, -, uint);
        BINx4(IMUL, *, uint);
        BINx4(UDIV, /, uint);
        BINx4(SDIV, /,  int);
        BINx4(UMOD, %, uint);
        BINx4(SMOD, %,  int);

        BINx2(FADD, +, float);
        BINx2(FSUB, -, float);
        BINx2(FMUL, *, float);
        BINx2(FDIV, /, float);
        // BINx2(FMOD, %, float);

        BINx4( SHL, <<, uint);
        BINx4(LSHR, >>, uint);
        BINx4(ASHR, >>,  int);
        BINx4(BAND,  &, uint);
        BINx4( BOR,  |, uint);
        BINx4(BXOR,  ^, uint);

        #undef BIN
        #undef BINx4
        #undef BINx2


        #define UN(NAME, OP, TYPE, SIZE)                                          \
            case OP_ ## NAME ## SIZE: {                                           \
                ctrl_assert(frame->ip + 1 + 1 + 1 < function->bytecode.size       \
                           , TRAP_IP_OUT_OF_BOUNDS, #NAME ": missing operands" ); \
                                                                                  \
                uint8_t out_idx = read8(bytecode, frame->ip + 1);                 \
                uint8_t val_idx = read8(bytecode, frame->ip + 1 + 1);             \
                                                                                  \
                ctrl_assert( validate_reg(table, out_idx)                         \
                           & validate_reg(table, val_idx)                         \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register out of bounds" );                  \
                                                                                  \
                uint8_t* out_reg = &locals[select_reg(frame, out_idx)];           \
                uint8_t* val_reg = &locals[select_reg(frame, val_idx)];           \
                                                                                  \
                ctrl_assert( table->layouts.data[out_idx].size >= SIZE / 8        \
                           & table->layouts.data[val_idx].size >= SIZE / 8        \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register too small" );                      \
                                                                                  \
                TYPE ## SIZE ## _t* out = (TYPE ## SIZE ## _t*) out_reg;          \
                TYPE ## SIZE ## _t* val = (TYPE ## SIZE ## _t*) val_reg;          \
                                                                                  \
                *out = OP *val;                                                   \
                                                                                  \
                frame->ip += 1 + 1 + 1;                                           \
            } break;                                                              \

        #define UNx4(NAME, OP, TYPE) \
            UN(NAME, OP, TYPE,  8);  \
            UN(NAME, OP, TYPE, 16);  \
            UN(NAME, OP, TYPE, 32);  \
            UN(NAME, OP, TYPE, 64);  \

        #define UNx2(NAME, OP, TYPE) \
            UN(NAME, OP, TYPE, 32);  \
            UN(NAME, OP, TYPE, 64);  \

        UNx4(INEG, -,   int);
        UNx2(FNEG, -, float);
        UNx4(BNOT, ~,  uint);

        #undef UN
        #undef UNx4
        #undef UNx2


        #define CMP(NAME, OP, TYPE, SIZE)                                        \
            case OP_ ## NAME ## SIZE: {                                          \
                ctrl_assert( frame->ip + 1 + 1 + 1 + 1 < function->bytecode.size \
                           , TRAP_IP_OUT_OF_BOUNDS                               \
                           , #NAME ": missing operands" );                       \
                                                                                 \
                uint8_t out_idx = read8(bytecode, frame->ip + 1);                \
                uint8_t lhs_idx = read8(bytecode, frame->ip + 1 + 1);            \
                uint8_t rhs_idx = read8(bytecode, frame->ip + 1 + 1 + 1);        \
                                                                                 \
                ctrl_assert( validate_reg(table, out_idx)                        \
                           & validate_reg(table, lhs_idx)                        \
                           & validate_reg(table, rhs_idx)                        \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                          \
                           , #NAME ": register out of bounds" );                 \
                                                                                 \
                uint8_t* out_reg = &locals[select_reg(frame, out_idx)];          \
                uint8_t* lhs_reg = &locals[select_reg(frame, lhs_idx)];          \
                uint8_t* rhs_reg = &locals[select_reg(frame, rhs_idx)];          \
                                                                                 \
                ctrl_assert( table->layouts.data[out_idx].size >= sizeof(bool)   \
                           & table->layouts.data[lhs_idx].size >= SIZE / 8       \
                           & table->layouts.data[rhs_idx].size >= SIZE / 8       \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                          \
                           , #NAME ": register too small" );                     \
                                                                                 \
                bool* out = (bool*) out_reg;                                     \
                TYPE ## SIZE ## _t* lhs = (TYPE ## SIZE ## _t*) lhs_reg;         \
                TYPE ## SIZE ## _t* rhs = (TYPE ## SIZE ## _t*) rhs_reg;         \
                                                                                 \
                *out = *lhs == *rhs;                                             \
                                                                                 \
                frame->ip += 1 + 1 + 1 + 1;                                      \
            } break;                                                             \

        #define CMPx4(NAME, OP, TYPE) \
            CMP(NAME, OP, TYPE, 8);   \
            CMP(NAME, OP, TYPE, 16);  \
            CMP(NAME, OP, TYPE, 32);  \
            CMP(NAME, OP, TYPE, 64);  \

        #define CMPx2(NAME, OP, TYPE) \
            CMP(NAME, OP, TYPE, 32);  \
            CMP(NAME, OP, TYPE, 64);  \

        CMPx4(IEQ, ==, uint);
        CMPx4(INE, !=, uint);
        CMPx4(ILT, <,  uint);
        CMPx4(ILE, <=, uint);
        CMPx4(IGT, >,  uint);
        CMPx4(IGE, >=, uint);

        CMPx2(FEQ, ==, float);
        CMPx2(FNE, !=, float);
        CMPx2(FLT, <,  float);
        CMPx2(FLE, <=, float);
        CMPx2(FGT, >,  float);
        CMPx2(FGE, >=, float);

        #undef CMP
        #undef CMPx4
        #undef CMPx2


        #define CAST(NAME, TYPE_A, TYPE_B, SIZE_A, SIZE_B)                        \
            case OP_ ## NAME: {                                                   \
                ctrl_assert( frame->ip + 1 + 1 + 1 < function->bytecode.size      \
                           , TRAP_IP_OUT_OF_BOUNDS                                \
                           , #NAME ": missing operands" );                        \
                                                                                  \
                uint8_t out_idx = read8(bytecode, frame->ip + 1);                 \
                uint8_t in_idx  = read8(bytecode, frame->ip + 1 + 1);             \
                                                                                  \
                ctrl_assert( validate_reg(table, out_idx)                         \
                           & validate_reg(table, in_idx)                          \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register out of bounds" );                  \
                                                                                  \
                uint8_t* out_reg = &locals[select_reg(frame, out_idx)];           \
                uint8_t* in_reg  = &locals[select_reg(frame, in_idx)];            \
                                                                                  \
                ctrl_assert( table->layouts.data[out_idx].size >= SIZE_B / 8      \
                           & table->layouts.data[in_idx].size  >= SIZE_A / 8      \
                           , TRAP_OPERAND_OUT_OF_BOUNDS                           \
                           , #NAME ": register too small" );                      \
                                                                                  \
                TYPE_B ## SIZE_B ## _t* out = (TYPE_B ## SIZE_B ## _t*) out_reg;  \
                TYPE_A ## SIZE_A ## _t*  in = (TYPE_A ## SIZE_A ## _t*) in_reg;   \
                                                                                  \
                *out = (TYPE_B ## SIZE_B ## _t) *in;                              \
                                                                                  \
                frame->ip += 1 + 1 + 1;                                           \
            } break;                                                              \

        CAST( ZEXT_8_16, uint, uint,  8, 16);
        CAST( ZEXT_8_32, uint, uint,  8, 32);
        CAST( ZEXT_8_64, uint, uint,  8, 64);
        CAST(ZEXT_16_32, uint, uint, 16, 32);
        CAST(ZEXT_16_64, uint, uint, 16, 64);
        CAST(ZEXT_32_64, uint, uint, 32, 64);

        CAST( SEXT_8_16, int, int,  8, 16);
        CAST( SEXT_8_32, int, int,  8, 32);
        CAST( SEXT_8_64, int, int,  8, 64);
        CAST(SEXT_16_32, int, int, 16, 32);
        CAST(SEXT_16_64, int, int, 16, 64);
        CAST(SEXT_32_64, int, int, 32, 64);

        CAST(ITRUNC_64_32, uint, uint, 64, 32);
        CAST(ITRUNC_64_16, uint, uint, 64, 16);
        CAST( ITRUNC_64_8, uint, uint, 64,  8);
        CAST(ITRUNC_32_16, uint, uint, 32, 16);
        CAST( ITRUNC_32_8, uint, uint, 32,  8);
        CAST( ITRUNC_16_8, uint, uint, 16,  8);

        CAST(  FEXT, float, float, 32, 64);
        CAST(FTRUNC, float, float, 64, 32);

        CAST(S32_TO_F32,   int, float, 32, 32);
        CAST(U32_TO_F32,  uint, float, 32, 32);
        CAST(S64_TO_F64,   int, float, 64, 64);
        CAST(U64_TO_F64,  uint, float, 64, 64);
        CAST(F32_TO_S32, float,   int, 32, 32);
        CAST(F32_TO_U32, float,  uint, 32, 32);
        CAST(F64_TO_S64, float,   int, 64, 64);
        CAST(F64_TO_U64, float,  uint, 64, 64);

        #undef CAST


        default:
            ctrl_trap(TRAP_UNEXPECTED, "unknown opcode");
    }

    return CTRL_EXEC;
}


int main (int argc, char** args) {
    return 0;
}
