#include <assert.h>
#include <inttypes.h>
#include <iso646.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


//  Wishlist headers
////////////////////////////////////////////////////////////////

//  #include <stdbit.h>
//  #include <stdcountof.h>


//  Apple headers
////////////////////////////////////////////////////////////////

#include <mach-o/fat.h>
#include <mach-o/loader.h>
#include <mach/vm_page_size.h>


//  Just making sure
////////////////////////////////////////////////////////////////

static_assert(CHAR_BIT == 8);
static_assert(sizeof(size_t) == 8);


//  Macro bits
////////////////////////////////////////////////////////////////

#define numof(a)                                                \
  (sizeof (a) / sizeof ((a)[0]))

#define bitsof(a)                                               \
  (CHAR_BIT * sizeof(a))

#define eval(x)                                                 \
  x

#define quote(x)                                                \
  #x

#define cat_(a, b)                                              \
  a##b

#define cat2(a, b)                                              \
  cat_(a, b)

#define cat3(a, b, c)                                           \
  cat2(cat2(a, b), c)

#define of(a, b)                                                \
  cat3(a, _, b)

#define unwrap(...)                                             \
  __VA_ARGS__

#define when(a, b)                                              \
  (not (a) or (b))

#define after(former, latter)                                   \
  ((former) ? ((latter), true) : ((latter), false))


//  Systematic names for types
////////////////////////////////////////////////////////////////

#define type_alias(name, of)                                    \
  typedef of name##Var;                                         \
  typedef name##Var const name;                                 \
  typedef name *name##RefVar;                                   \
  typedef name##RefVar const name##Ref;                         \
  typedef name##Var *name##VarRefVar;                           \
  typedef name##VarRefVar const name##VarRef

#define new_type(kind, name)                                    \
typedef kind name name##Var;                                    \
typedef name##Var const name;                                   \
typedef name *name##RefVar;                                     \
typedef name##RefVar const name##Ref;                           \
typedef name##Var *name##VarRefVar;                             \
typedef name##VarRefVar const name##VarRef

#define enum_type(name, ...)                                    \
  enum name##Id { __VA_ARGS__ };                                \
  new_type(enum, name##Id);                                     \
  new_type(struct, name);                                       \
  struct name { name##IdVar id; }

#define struct_type(name)                                       \
  new_type(struct, name)

#define union_type(name)                                        \
  new_type(union, name)

#define function_type(name, type, params)                       \
  typedef type name params;                                     \
  typedef name *name##RefVar;                                   \
  typedef name##RefVar const name##Ref


//  Standard types
////////////////////////////////////////////////////////////////

type_alias(ExitStatus,  int      );
type_alias(Argc,        int      );
type_alias(Argv,        char **  );

type_alias(Chr, char);

[[maybe_unused]]
static Chr NUL = '\0';

type_alias(Arg,       ChrRefVar);
type_alias(Args,      ArgRefVar);
type_alias(FilePath,  ChrRefVar);
type_alias(Str,       ChrRefVar);
type_alias(Tag,       ChrRefVar);

//  Number of elements, length, cardinality.
type_alias(Num, size_t);

//  Zero-based index, position.
type_alias(Idx, size_t);

#define IdxFmt "z"

//  Memory size, number of bytes.
type_alias(Size, size_t);

//  Positive memory stride, alignment, byte multiple.
type_alias(Stride, size_t);

//  Log-2 alignment, index of least significant address bit.
type_alias(Align, size_t);

type_alias(Bool, bool);

//  Says how much room is left in `this`.
static inline Size
size_room(
  Size this
) {
  return SIZE_MAX - this;
}

//  Says whether `this` has `that` many bytes of room.
static inline Size
size_has(
  Size this,
  Size that
) {
  return that <= size_room(this);
}


//  Sized types
////////////////////////////////////////////////////////////////

type_alias(U1    , unsigned _BitInt(  1));
type_alias(U8    , unsigned _BitInt(  8));
type_alias(U10   , unsigned _BitInt( 10));
type_alias(U16   , unsigned _BitInt( 16));
type_alias(U24   , unsigned _BitInt( 24));
type_alias(U32   , unsigned _BitInt( 32));
type_alias(U64   , unsigned _BitInt( 64));

#define U1(n)    ((U1Var)(n))
#define U8(n)    ((U8Var)(n))
#define U10(n)   ((U10Var)(n))
#define U16(n)   ((U16Var)(n))
#define U24(n)   ((U24Var)(n))
#define U32(n)   ((U32Var)(n))
#define U64(n)   ((U64Var)(n))

#define u(n)       (n##uwb)
#define u1(n)      (U1(u(n)))
#define u8(n)      (U8(u(n)))
#define u10(n)     (U10(u(n)))
#define u16(n)     (U16(u(n)))
#define u24(n)     (U24(u(n)))
#define u32(n)     (U32(u(n)))
#define u64(n)     (U64(u(n)))


//  Output buffer, as long as we're generating static output
////////////////////////////////////////////////////////////////

static U8Var reow[33432];
static_assert(numof(reow) == sizeof(reow));


//  Messaging --- logging, warnings, errors
////////////////////////////////////////////////////////////////

type_alias(Line, typeof(__LINE__));

#define LineFmt "d"

//  When a macro takes a format string and format arguments,
//  instead of defining it with `fmt, ...` parameters,
//  we use just `...`,
//  then we can use `__VA_OPT__` with `head` and `tail`
//  to make the format string optional.

#define head(x, ...)                                            \
  x

#define take_1(...)                                             \
  __VA_OPT__(head(__VA_ARGS__))

#define tail(x, ...)                                            \
  __VA_ARGS__

#define drop_1(...)                                             \
  __VA_OPT__(tail(__VA_ARGS__))

#define comma_tail(x, ...)                                      \
  __VA_OPT__(,) __VA_ARGS__

#define comma_drop_1(...)                                       \
  __VA_OPT__(comma_tail(__VA_ARGS__))

#define tell(fmt, file, line, fun, tag, ...)                    \
  (void)fprintf(                                                \
    stderr,                                                     \
    "%s: "                                                      \
    "%s:"                                                       \
    "%"LineFmt": "                                              \
    "%s: "                                                      \
    "%s"                                                        \
    fmt                                                         \
    "\n",                                                       \
    "nb",                                                       \
    file,                                                       \
    line,                                                       \
    fun,                                                        \
    tag                                                         \
    __VA_OPT__(,) __VA_ARGS__                                   \
  )

#define error(...)                                              \
  tell(                                                         \
    ""                                                          \
    __VA_OPT__(": ")                                            \
    take_1(__VA_ARGS__),                                        \
    __FILE__,                                                   \
    __LINE__,                                                   \
    __FUNCTION__,                                               \
    "error"                                                     \
    comma_drop_1(__VA_ARGS__)                                   \
  )

#define warn(...)                                               \
  tell(                                                         \
    ""                                                          \
    __VA_OPT__(": ")                                            \
    take_1(__VA_ARGS__),                                        \
    __FILE__,                                                   \
    __LINE__,                                                   \
    __FUNCTION__,                                               \
    "warning"                                                   \
    comma_drop_1(__VA_ARGS__)                                   \
  )

#define trace(...)                                              \
  tell(                                                         \
    ""                                                          \
    __VA_OPT__(": ")                                            \
    take_1(__VA_ARGS__),                                        \
    __FILE__,                                                   \
    __LINE__,                                                   \
    __FUNCTION__,                                               \
    "trace"                                                     \
    comma_drop_1(__VA_ARGS__)                                   \
  )

#define shall(what, ...)                                        \
  (                                                             \
    (what) ? true : (                                           \
      error(                                                    \
        "shall(%s)"                                             \
        __VA_OPT__(": ")                                        \
        take_1(__VA_ARGS__),                                    \
        #what                                                   \
        comma_drop_1(__VA_ARGS__)                               \
      ),                                                        \
      abort(),                                                  \
      true                                                      \
    )                                                           \
  )

#define should(what, ...)                                       \
  (                                                             \
    (what) ? true : (                                           \
      warn(                                                     \
        "should(%s)"                                            \
        __VA_OPT__(": ")                                        \
        take_1(__VA_ARGS__),                                    \
        #what                                                   \
        comma_drop_1(__VA_ARGS__)                               \
      ),                                                        \
      true                                                      \
    )                                                           \
  )

#define whereas(what)                                           \
  (                                                             \
    (what) ?                                                    \
    (trace("whereas(%s): true", #what), true) :                 \
    (trace("whereas(%s): false", #what), false)                 \
  )

#define be_same(fmtx, fmtd, t, a, b)                            \
  "((%s) = %"fmtx" (%"fmtd"))"                                  \
  " = "                                                         \
  "((%s) = %"fmtx" (%"fmtd"))",                                 \
  #a, (t)(a), (t)(a),                                           \
  #b, (t)(b), (t)(b)

#define be_same_32(a, b)                                        \
  be_same("0.8"PRIX32, PRIu32, uint32_t, a, b)

#define be_same_64(a, b)                                        \
  be_same("0.16"PRIX64, PRIu64, uint64_t, a, b)

#define shall_be_same(a, b)                                     \
  _Generic(                                                     \
    (a),                                                        \
    U64Var: ((void)shall((a) == (b), be_same_64(a, b)), (a)),   \
    U32Var: ((void)shall((a) == (b), be_same_32(a, b)), (a))    \
  )

#define should_be_same(a, b)                                    \
  _Generic(                                                     \
    (a),                                                        \
    U64Var: ((void)should((a) == (b), be_same_64(a, b)), (a)),  \
    U32Var: ((void)should((a) == (b), be_same_32(a, b)), (a))   \
  )


//  Main entry point
////////////////////////////////////////////////////////////////

static Bool
nb(
  [[maybe_unused]]
  Str pgm,
  Num arg_num,
  Args args
);

static void test(void);

ExitStatusVar
main(
  Argc argc,
  Argv argv
) {
  shall(argc >= 1);
  shall(argv != nullptr);
  test();
  Bool okay = nb(argv[0], (Num)(argc - 1), (ArgsVar)&argv[1]);
  if (not okay) {
    error("failed");
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}


//  Alignment and stride

[[maybe_unused]]
static inline Stride align_stride(Align align) {
  shall(align < bitsof(Stride));
  return (Stride)1 << align;
}


//  Endianness
////////////////////////////////////////////////////////////////

[[maybe_unused]]
static inline U32 l32(U32 i) {
  return 0
    | ((i & u32(0x000000FF)) << 0'3'0)
    | ((i & u32(0x0000FF00)) << 0'1'0)
    | ((i & u32(0x00FF0000)) >> 0'1'0)
    | ((i & u32(0xFF000000)) >> 0'3'0);
}

[[maybe_unused]]
static inline U32 rl32(U8Ref there) {
  return
    ( U32(there[0]) << 0'0'0
    | U32(there[1]) << 0'1'0
    | U32(there[2]) << 0'2'0
    | U32(there[3]) << 0'3'0
    );
}

[[maybe_unused]]
static inline U64 rl64(U8Ref there) {
  return
    ( U64(there[0]) << 0'0'0
    | U64(there[1]) << 0'1'0
    | U64(there[2]) << 0'2'0
    | U64(there[3]) << 0'3'0
    | U64(there[4]) << 0'4'0
    | U64(there[5]) << 0'5'0
    | U64(there[6]) << 0'6'0
    | U64(there[7]) << 0'7'0
    );
}


//  The unavoidable twiddling of bits
////////////////////////////////////////////////////////////////

// A mask with the nth bit set, equal to 2^n.
static inline U64 bit_64(U64 n) {
  shall(n < bitsof(U64));
  return u64(1) << n;
}

// A mask of all zeros.
static U64 zeros_64 = u64(0);

// A mask of all ones.
static U64 ones_64 = compl zeros_64;

// A 64-bit mask with the n bits in the range [(n - 1) : 0] set.
static inline U64 mask_64(U64 n) {
  shall(n <= bitsof(U64));
  return
    n == 0 ? zeros_64 :
    n == 64 ? ones_64 :
    ones_64 >> (64 - n);
}

// Gets the last tab stop of size 2^x from n,
// rounding n downward to the greatest kd =< n where d = 2^x,
// in the range [n - ((2^x)-1) : n].
static inline U64 down_64(U64 n, U64 x) {
  return n & compl mask_64(x);
}

// Gets how far n is above the last tab stop of size 2^x,
// in the range [0 : ((2^x)-1)].
static inline U64 above_64(U64 n, U64 x) {
  return n & mask_64(x);
}

// Gets the next stab stop of size 2^x from n,
// rounding n upward to the least kd >= n where d = 2^x,
// in the range [n : n + ((2^x)-1)].
static inline U64 up_64(U64 n, U64 x) {
  shall(n <= UINT64_MAX - mask_64(x));
  return down_64(mask_64(x) + n, x);
}

// Gets how far n is below the next tab stop of size 2^x,
// in the range [0 : ((2^x)-1)].
static inline U64 below_64(U64 n, U64 x) {
  return mask_64(x) - above_64(n - 1, x);
}


//  Ownership
////////////////////////////////////////////////////////////////

enum_type(
  Owner,
  Static,
  Dynamic,
);


//  Buffers
////////////////////////////////////////////////////////////////

struct_type(Buf);

struct Buf {
  U8VarRefVar  in;
  OwnerVar     owner;
  IdxVar       at;
  IdxVar       end;
};

union_type(V16U8);

union V16U8 {
  U8 vec[16];
  unsigned char str[16];
};

////////////////////////////////

static inline Bool
buf_wf(
  BufRef buf
);

static inline Bool
buf_open(
  BufVarRef buf,
  Num num,
  Size size
);

static inline Size
buf_room(
  BufRef buf
);

static inline Bool
buf_has(
  BufRef buf,
  Size size
);

static inline U8Ref
buf_from(
  BufRef buf
);

static inline U8VarRef
buf_to(
  BufRef buf
);

static inline void
buf_rewind(
  BufVarRef buf
);

static inline void
buf_skip(
  BufVarRef buf,
  Size by
);

static inline void
buf_out_u8(
  BufVarRef buf,
  U8 i
);

static inline void
buf_out_u32(
  BufVarRef buf,
  U32 i
);

static inline void
buf_out_u64(
  BufVarRef buf,
  U64 i
);

static inline void
buf_out_v16u8(
  BufVarRef buf,
  V16U8 v
);

static inline void
buf_out_pad(
  BufVarRef buf,
  Stride till
);

static inline void
buf_out_str(
  BufVarRef buf,
  Str str,
  Num max
);

static inline Bool
buf_shut(
  BufVarRef buf
);

////////////////////////////////

//  Says whether a `buf` is well formed.
[[maybe_unused]]
static inline Bool
buf_wf(
  BufRef buf
) {
  return
    should(buf != nullptr) and (
      should(buf->in != nullptr) and
      should(buf->at <= buf->end)
    );
}

static inline Bool
buf_open(
  BufVarRef buf,
  Num num,
  Size size
) {
  shall(buf != nullptr);
  typeof(buf->in) const in = calloc(num, size);
  Bool const calloc_succeeded = shall(in != nullptr);
  *buf = (Buf){

    .in     = in                                    ,
    .owner  = (Owner){Dynamic}                      ,
    .at     = 0                                     ,
    .end    = ((void)calloc_succeeded, num * size)  ,

  };
  return true;
}

//  Says how much room `buf` has at `buf->at` before `buf->end`.
[[maybe_unused]]
static inline Size
buf_room(
  BufRef buf
) {
  shall(buf_wf(buf));
  return buf->end - buf->at;
}

//  Says whether `buf` has `size` bytes available.
[[maybe_unused]]
static inline Bool
buf_has(
  BufRef buf,
  Size size
) {
  shall(buf_wf(buf));
  return size <= buf_room(buf);
}

//  Gets a pointer to read from `buf`.
[[maybe_unused]]
static inline U8Ref
buf_from(
  BufRef buf
) {
  shall(buf_wf(buf));
  return &buf->in[buf->at];
}

//  Gets a pointer to write to `buf`.
[[maybe_unused]]
static inline U8VarRef
buf_to(
  BufRef buf
) {
  shall(buf_wf(buf));
  return &buf->in[buf->at];
}

[[maybe_unused]]
static inline void
buf_rewind(
  BufVarRef buf
) {
  shall(buf_wf(buf));
  buf->at = 0;
}

[[maybe_unused]]
static inline void
buf_skip(
  BufVarRef buf,
  Size by
) {
  shall(buf_wf(buf));
  shall(buf_has(buf, by));
  Size at = buf->at + +by;
  buf->at = at;
}

[[maybe_unused]]
static inline void
buf_out_u8(
  BufVarRef buf,
  U8 i
) {
  Size size = sizeof i;
  shall(buf_has(buf, size));
  U8VarRef to = buf_to(buf);
  to[0] = i;
  buf_skip(buf, size);
}

[[maybe_unused]]
static inline void
buf_out_u32(
  BufVarRef buf,
  U32 i
) {
  Size size = sizeof i;
  shall(buf_has(buf, size));
  U8VarRef to = buf_to(buf);
  to[0] = (i & u32(0x000000FF)) >> 0'0'0;
  to[1] = (i & u32(0x0000FF00)) >> 0'1'0;
  to[2] = (i & u32(0x00FF0000)) >> 0'2'0;
  to[3] = (i & u32(0xFF000000)) >> 0'3'0;
  buf_skip(buf, size);
}

[[maybe_unused]]
static inline void
buf_out_u64(
  BufVarRef buf,
  U64 i
) {
  Size size = sizeof i;
  shall(buf_has(buf, size));
  U8VarRef to = buf_to(buf);
  to[0] = (i & u64(0x00000000'000000FF)) >> 0'0'0;
  to[1] = (i & u64(0x00000000'0000FF00)) >> 0'1'0;
  to[2] = (i & u64(0x00000000'00FF0000)) >> 0'2'0;
  to[3] = (i & u64(0x00000000'FF000000)) >> 0'3'0;
  to[4] = (i & u64(0x000000FF'00000000)) >> 0'4'0;
  to[5] = (i & u64(0x0000FF00'00000000)) >> 0'5'0;
  to[6] = (i & u64(0x00FF0000'00000000)) >> 0'6'0;
  to[7] = (i & u64(0xFF000000'00000000)) >> 0'7'0;
  buf_skip(buf, size);
}

[[maybe_unused]]
static inline void
buf_out_v16u8(
  BufVarRef buf,
  V16U8 v
) {
  static_assert(sizeof v.vec == 16);
  shall(buf->at < buf->end - sizeof v.vec);
  U8VarRef here = &buf->in[buf->at];
  memcpy((void *)&here[0], (void *)&v.vec[0], sizeof v.vec);
  buf->at += +sizeof v.vec;
}

//  Adds 0 or more bytes of padding up to a multiple of `till`.
[[maybe_unused]]
static inline void
buf_out_pad(
  BufVarRef buf,
  Stride stride
) {
  shall(stride >= 1);
  shall(stride <= buf->end);
  // shall(buf->end % stride == 0 or buf->at <= (buf->end + 1) / stride);
  if (buf->at % stride == 0) return;
  Size to = ((buf->at + stride) / stride) * stride;
  shall(
    to <= buf->end,
    "padding with stride %zu from %zu to %zu falls after %zu",
    stride,
    buf->at,
    to,
    buf->end
  );
  Size by = to - buf->at;
  //  IDEA: Add an option to skip writing zeros.
  memset((void *)buf_to(buf), 0, by);
  buf_skip(buf, by);
}

//  Outputs `str`, including a NUL terminator.
//  The size must be no more than `max`.
//  Doesn't do any padding.
[[maybe_unused]]
static inline void
buf_out_str(
  BufVarRef buf,
  Str str,
  Num max
) {
  shall(buf_wf(buf));
  shall(str != nullptr);
  Size len = strnlen(str, max == SIZE_MAX ? SIZE_MAX : max + 1);
  shall(len <= max);
  Size size = len + sizeof NUL;
  shall(
    buf_has(buf, size),
    "have %zu B room, need %zu B",
    buf_room(buf),
    size
  );
  U8VarRef to = buf_to(buf);
  memmove((void *)to, (void const *)str, len);
  to[len] = NUL;
  buf_skip(buf, size);
}

static inline Bool
buf_shut(
  BufVarRef buf
) {
  shall(buf_wf(buf));
  if (buf->owner.id == Dynamic)
    free(buf->in);
  *buf = (Buf){};
  return true;
}


//  Tasks
////////////////////////////////////////////////////////////////

struct_type(Task);

function_type(Beg       , Bool, (TaskVarRef task                 ));
function_type(At        , Bool, (TaskVarRef task  , Idx    idx   ));
function_type(BegElt    , Bool, (TaskVarRef task  , Str    tag   ));
function_type(Elt       , Bool, (TaskVarRef task  , Str    tag   ));
function_type(OutU32    , Bool, (TaskVarRef task  , U32    val   ));
function_type(OutU64    , Bool, (TaskVarRef task  , U64    val   ));
function_type(OutV16U8  , Bool, (TaskVarRef task  , V16U8  val   ));
function_type(OutPad    , Bool, (TaskVarRef task  , Size   size  ));
function_type(OutStr    , Bool, (TaskVarRef task  , Str    str   ));
function_type(EndElt    , Bool, (TaskVarRef task  , Str    tag   ));
function_type(End       , Bool, (TaskVarRef task                 ));

struct Task {
  BegRefVar       beg        ;
  AtRefVar        at         ;
  BegEltRefVar    beg_elt    ;
  EltRefVar       elt        ;
  OutU32RefVar    out_u32    ;
  OutU64RefVar    out_u64    ;
  OutV16U8RefVar  out_v16u8  ;
  OutPadRefVar    out_pad    ;
  OutStrRefVar    out_str    ;
  EndEltRefVar    end_elt    ;
  EndRefVar       end        ;
};

#define may_call(fun, ...)                                      \
  when((fun) != nullptr, fun(__VA_ARGS__))

#define task_call(task, fun, ...)                               \
  may_call((task)->fun, (task) __VA_OPT__(,) __VA_ARGS__)

#define task_decl(fun, params, ...)                             \
  static inline Bool task_##fun(                                \
    TaskVarRef task __VA_OPT__(,)                               \
    unwrap params                                               \
  )

#define task_def(fun, params, ...)                              \
  task_decl(fun, params __VA_OPT__(,) __VA_ARGS__) {            \
    return task_call(                                           \
      task,                                                     \
      fun __VA_OPT__(,)                                         \
      __VA_ARGS__                                               \
    );                                                          \
  }

task_def(beg        , (                )           );
task_def(at         , (Idx     idx     ),  idx     );
task_def(beg_elt    , (Str     tag     ),  tag     );
task_def(elt        , (Str     tag     ),  tag     );
task_def(out_u32    , (U32     val     ),  val     );
task_def(out_u64    , (U64     val     ),  val     );
task_def(out_v16u8  , (V16U8   val     ),  val     );
task_def(out_pad    , (Stride  stride  ),  stride  );
task_def(out_str    , (Str     str     ),  str     );
task_def(end_elt    , (Str     tag     ),  tag     );
task_def(end        , (                )           );

[[maybe_unused]]
static inline Bool task_elt_u32(
  TaskVarRef  task,
  Str         tag,
  U32         val
) {
  return task_elt(task, tag) and task_out_u32(task, val);
}

[[maybe_unused]]
static inline Bool task_elt_u64(
  TaskVarRef  task,
  Str         tag,
  U64         val
) {
  return task_elt(task, tag) and task_out_u64(task, val);
}

[[maybe_unused]]
static inline Bool task_elt_v16u8(
  TaskVarRef  task,
  Str         tag,
  V16U8       val
) {
  return task_elt(task, tag) and task_out_v16u8(task, val);
}


//  Supplementary definitions implicit in Mach headers
////////////////////////////////////////////////////////////////

U32 CPU_TYPE_MASK = compl U32(CPU_ARCH_MASK);


//  Generating the output
////////////////////////////////////////////////////////////////

Bool work(TaskVarRef task) {

#define declare_field(name, num, sub)                           \
  [[maybe_unused]]                                              \
  IdxVar of(name, sub)[num] = {}

#define declare_struct(name, num)                               \
  declare_field(name, num, beg);                                \
  declare_field(name, num, end);

  declare_struct(  file,                    1                   );

  declare_struct(  fat_binary,              1                   );

  declare_struct(  fat_header,              1                   );
  declare_field(   fat_header,              1,  magic           );
  declare_field(   fat_header,              1,  nfat_arch       );

  declare_struct(  fat_arch,                1                   );
  declare_field(   fat_arch,                1,  cputype         );
  declare_field(   fat_arch,                1,  cpusubtype      );
  declare_field(   fat_arch,                1,  offset          );
  declare_field(   fat_arch,                1,  size            );
  declare_field(   fat_arch,                1,  align           );
  declare_field(   fat_arch,                1,  reserved        );

  declare_struct(  mach_object,             1                   );

  declare_struct(  mach_header_64,          1                   );
  declare_field(   mach_header_64,          1,  magic           );
  declare_field(   mach_header_64,          1,  cputype         );
  declare_field(   mach_header_64,          1,  cpusubtype      );
  declare_field(   mach_header_64,          1,  filetype        );
  declare_field(   mach_header_64,          1,  ncmds           );
  declare_field(   mach_header_64,          1,  sizeofcmds      );
  declare_field(   mach_header_64,          1,  flags           );
  declare_field(   mach_header_64,          1,  reserved        );

  declare_struct(  load_commands,           1                   );

  declare_struct(  segment_command_64,      4                   );
  declare_field(   segment_command_64,      4,  cmd             );
  declare_field(   segment_command_64,      4,  cmdsize         );
  declare_field(   segment_command_64,      4,  segname         );
  declare_field(   segment_command_64,      4,  vmaddr          );
  declare_field(   segment_command_64,      4,  vmsize          );
  declare_field(   segment_command_64,      4,  fileoff         );
  declare_field(   segment_command_64,      4,  filesize        );
  declare_field(   segment_command_64,      4,  maxprot         );
  declare_field(   segment_command_64,      4,  initprot        );
  declare_field(   segment_command_64,      4,  nsects          );
  declare_field(   segment_command_64,      4,  flags           );

  declare_struct(  section_64,              4                   );
  declare_field(   section_64,              4,  sectname        );
  declare_field(   section_64,              4,  segname         );
  declare_field(   section_64,              4,  addr            );
  declare_field(   section_64,              4,  size            );
  declare_field(   section_64,              4,  offset          );
  declare_field(   section_64,              4,  align           );
  declare_field(   section_64,              4,  reloff          );
  declare_field(   section_64,              4,  nreloc          );
  declare_field(   section_64,              4,  flags           );
  declare_field(   section_64,              4,  reserved1       );
  declare_field(   section_64,              4,  reserved2       );
  declare_field(   section_64,              4,  stub_size       );
  declare_field(   section_64,              4,  reserved3       );

  declare_struct(  prebound_dylib_command,  1                   );
  declare_field(   prebound_dylib_command,  1,  cmd             );
  declare_field(   prebound_dylib_command,  1,  cmdsize         );
  declare_field(   prebound_dylib_command,  1,  name            );
  declare_field(   prebound_dylib_command,  1,  nmodules        );
  declare_field(   prebound_dylib_command,  1,  linked_modules  );

  ////////////////////////////////////////////////////////////

  task_beg(task);
  task_at(task, 0x0000);

  task_beg_elt(task, "file"); {

    //  fill with sentinel bytes
    //  memset((void *)file_beg[0], 0xBA, sizeof reow);

    Bool fat_binary_enabled = false;

    if (fat_binary_enabled) task_beg_elt(task, "fat_binary"); {

      if (fat_binary_enabled) {

        task_beg_elt(task, "fat_header"); {
          task_elt(  task,  "magic"      );  task_out_u32(  task,  shall_be_same(u32(0xCAFEBABE), U32(FAT_MAGIC))  );
          task_elt(  task,  "nfat_arch"  );  task_out_u32(  task,  u32(1)                                         );
        } task_end_elt(task, "fat_header");

        task_beg_elt(task, "fat_arch"); {

          task_elt(  task,  "cputype"     );  task_out_u32(  task, shall_be_same(u32(0x0100000C), U32(CPU_TYPE_ARM64))                        );
          task_elt(  task,  "cpusubtype"  );  task_out_u32(  task, shall_be_same(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL))                 );
          task_elt(  task,  "offset"      );  task_out_u32(  task, should_be_same(u32(0xBABABABA), U32(mach_object_beg[0] - file_beg[0]))    );  // TODO: offset
          task_elt(  task,  "size"        );  task_out_u32(  task, should_be_same(u32(0xBABABABA), U32(file_end[0] - file_beg[0]))           );  // TODO: size
          task_elt(  task,  "align"       );  task_out_u32(  task, shall_be_same(shall_be_same(u32(14), U32(vm_page_shift)), U32(PAGE_SHIFT))  );  // mach/vm_page_size.h:vm_page_shift
          task_elt(  task,  "reserved"    );  task_out_u32(  task, u32(0x00000000)                                                           );

        } task_end_elt(task, "fat_arch");

        // pad up to PAGE_SIZE with u8(0x00)
        // mach/vm_page_size.h:vm_page_size

        task_out_pad(task, shall_be_same(shall_be_same(u32(0x4000), U32(vm_page_size)), U32(PAGE_SIZE)));

      }

      task_beg_elt(task, "mach_object"); {

        task_beg_elt(task, "mach_header_64"); {

          task_elt(task, "magic"     );  task_out_u32(  task, shall_be_same(u32(0xFEEDFACF),
                                                                            U32(MH_MAGIC_64)));
          task_elt(task, "cputype"   );  task_out_u32(  task,
                                                        shall_be_same(
                                                          u32(0x0100000C),
                                                          shall_be_same(
                                                            U32(CPU_TYPE_ARM64),
                                                            ( ( shall_be_same(u32(0x01000000),
                                                                              U32(CPU_ARCH_ABI64))
                                                              & shall_be_same(u32(0xFF000000),
                                                                              U32(CPU_ARCH_MASK))
                                                              )
                                                            | ( shall_be_same(U32(u24(12)),
                                                                              U32(CPU_TYPE_ARM))
                                                              & shall_be_same(u32(0x00FFFFFF),
                                                                              U32(CPU_TYPE_MASK))
                                                              )))));
          task_elt(task, "cpusubtype"  );  task_out_u32(  task,
                                                          shall_be_same(u32(0x00000000),
                                                                        U32(CPU_SUBTYPE_ARM64_ALL)));
          task_elt(task, "filetype"    );  task_out_u32(  task,
                                                          shall_be_same(u32(0x00000002),
                                                                        U32(MH_EXECUTE)));
          task_elt(task, "ncmds"       );  task_out_u32(  task,
                                                          shall_be_same(u32(0x00000011),
                                                                        u32(17)));

          task_elt(task, "sizeofcmds"  );  task_out_u32(  task,
                                                          shall_be_same(u32(0x00000420),
                                                                        u32(1056)));
          task_elt(task, "flags"       );  task_out_u32(  task,
                                                          shall_be_same(  u32(0x00200085),
                                                                          ( shall_be_same(shall_be_same(u32(0x00200000), U32(MH_PIE)     ), u32(1) << 0'2'5)
                                                                          | shall_be_same(shall_be_same(u32(0x00000080), U32(MH_TWOLEVEL)), u32(1) << 0'0'7)
                                                                          | shall_be_same(shall_be_same(u32(0x00000004), U32(MH_DYLDLINK)), u32(1) << 0'0'2)
                                                                          | shall_be_same(shall_be_same(u32(0x00000001), U32(MH_NOUNDEFS)), u32(1) << 0'0'0)
                                                                          )));

          task_elt(task, "reserved");
          task_out_u32(task, u32(0x00000000));

        } task_end_elt(task, "mach_header_64");

        task_at(task, 0x0020);
        // TODO: on set load_commands_end: assert: sizeofcmds  = load_commands_end - load_commands_beg
        task_beg_elt(task, "load_commands"); {

          task_at(task, 0x0020);
          task_beg_elt(task, "segment_command_64"); {

            task_elt(  task, "cmd"       );  task_out_u32(    task, shall_be_same(u32(0x00000019),
                                                                                  U32(LC_SEGMENT_64))  );
            task_elt(  task, "cmdsize"   );  task_out_u32(    task,  u32(0x00000048)                  );
            task_elt(  task, "segname"   );  task_out_v16u8(  task,  (V16U8){.str = u8"__PAGEZERO"}   );
            task_elt(  task, "vmaddr"    );  task_out_u64(    task,  u64(0x00000000'00000000)         );
            task_elt(  task, "vmsize"    );  task_out_u64(    task,  u64(0x00000001'00000000)         );
            task_elt(  task, "fileoff"   );  task_out_u64(    task,  u64(0x00000000'00000000)         );
            task_elt(  task, "filesize"  );  task_out_u64(    task,  u64(0x00000000'00000000)         );
            task_elt(  task, "maxprot"   );  task_out_u32(    task,  u32(0x00000000)                  );
            task_elt(  task, "initprot"  );  task_out_u32(    task,  u32(0x00000000)                  );
            task_elt(  task, "nsects"    );  task_out_u32(    task,  u32(0x00000000)                  );
            task_elt(  task, "flags"     );  task_out_u32(    task,  u32(0x00000000)                  );

          } task_end_elt(task, "segment_command_64");

          task_at(task, u32(0x0068));
          task_beg_elt(task, "segment_command_64"); {

            task_elt(  task, "cmd"       );  task_out_u32(    task,  shall_be_same(u32(0x00000019), U32(LC_SEGMENT_64))  );
            task_elt(  task, "cmdsize"   );  task_out_u32(    task,  u32(0x00000188)                                    );
            task_elt(  task, "segname"   );  task_out_v16u8(  task,  (V16U8){.str = u8"__TEXT"}                         );
            task_elt(  task, "vmaddr"    );  task_out_u64(    task,  u64(0x00000001'00000000)                           );
            task_elt(  task, "vmsize"    );  task_out_u64(    task,  u64(0x00000000'00004000)                           );
            task_elt(  task, "fileoff"   );  task_out_u64(    task,  u64(0x00000000'00000000)                           );
            task_elt(  task, "filesize"  );  task_out_u64(    task,  u64(0x00000000'00004000)                           );
            task_elt(  task, "maxprot"   );  task_out_u32(    task,  u32(0x00000005)                                    );
            task_elt(  task, "initprot"  );  task_out_u32(    task,  u32(0x00000005)                                    );
            task_elt(  task, "nsects"    );  task_out_u32(    task,  u32(0x00000004)                                    );
            task_elt(  task, "flags"     );  task_out_u32(    task,  u32(0x00000000)                                    );

            //  segment_command_64.begin
            //  + sizeof segment_command_64
            task_at(task, 0x00B0);
            task_beg_elt(task, "sections"); {

              task_at(task, 0x00B0);
              task_beg_elt(task, "section_64"); {

                task_elt(  task, "sectname"  );  task_out_v16u8(  task, (V16U8){.str = u8"__text"}  );
                task_elt(  task, "segname"   );  task_out_v16u8(  task, (V16U8){.str = u8"__TEXT"}  );
                task_elt(  task, "addr"      );  task_out_u64(    task, u64(0x00000001'00000460)    );
                task_elt(  task, "size"      );  task_out_u64(    task, u64(0x00000000'0000003c)    );
                task_elt(  task, "offset"    );  task_out_u32(    task, u32(0x00000460)             );
                task_elt(  task, "align"     );  task_out_u32(    task, u32(0x00000002)             );
                task_elt(  task, "reloff"    );  task_out_u32(    task, u32(0x00000000)             );
                task_elt(  task, "nreloc"    );  task_out_u32(    task, u32(0x00000000)             );
                task_elt(  task, "flags"     );  task_out_u32(    task, shall_be_same(u32(0x80000400),
                                                                                      ( ( shall_be_same(u32(0x000000FF), U32(SECTION_TYPE))
                                                                                        & shall_be_same(u32(0x00000000), U32(S_REGULAR))
                                                                                        )
                                                                                      | ( shall_be_same(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
                                                                                        & ( shall_be_same(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
                                                                                          | shall_be_same(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
                                                                                          )
                                                                                        )
                                                                                      )
                                                                                     ));
                task_elt(task, "reserved1"); task_out_u32(task, u32(0x00000000));
                task_elt(task, "reserved2"); task_out_u32(task, u32(0x00000000));
                task_elt(task, "reserved3"); task_out_u32(task, u32(0x00000000));

              } task_end_elt(task, "section_64");

              task_at(task, 0x0100);
              task_beg_elt(task, "section_64"); {

                task_elt(task, "sectname"); task_out_v16u8(task, (V16U8){.str = u8"__stubs"});
                task_elt(task, "segname"); task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});
                task_elt(task, "addr"); task_out_u64(task, u64(0x00000001'0000049c));
                task_elt(task, "size"); task_out_u64(task, u64(0x00000000'0000000c));
                task_elt(task, "offset"); task_out_u32(task, u32(0x0000049c));
                task_elt(task, "align"); task_out_u32(task, u32(0x00000002));
                task_elt(task, "reloff"); task_out_u32(task, u32(0x00000000));
                task_elt(task, "nreloc"); task_out_u32(task, u32(0x00000000));
                task_elt(task, "flags"); task_out_u32(task, shall_be_same(
                                                              u32(0x80000408),
                                                              ( ( shall_be_same(u32(0x000000FF), U32(SECTION_TYPE))
                                                                & shall_be_same(u32(0x00000008), U32(S_SYMBOL_STUBS))
                                                                )
                                                              | ( shall_be_same(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
                                                                & ( shall_be_same(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
                                                                  | shall_be_same(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
                                                                  )
                                                                )
                                                              )
                                                            ));
                task_elt(task, "reserved1"); task_elt(task, "index_into_indirect_symbol_table"); task_out_u32(task, u32(0x00000000));
                task_elt(task, "reserved2"); task_elt(task, "stub_size"); task_out_u32(task, u32(0x0000000c));
                task_elt(task, "reserved3"); task_out_u32(task, u32(0x00000000));

              } task_end_elt(task, "section_64");

              task_at(task, 0x0150);
              task_beg_elt(task, "section_64"); {

                task_elt(task, "sectname"   );  task_out_v16u8(  task, (V16U8){.str = u8"__cstring"}                           );
                task_elt(task, "segname"    );  task_out_v16u8(  task, (V16U8){.str = u8"__TEXT"}                              );
                task_elt(task, "addr"       );  task_out_u64(    task, u64(0x00000001'000004a8)                                );
                task_elt(task, "size"       );  task_out_u64(    task, u64(0x00000000'00000005)                                );
                task_elt(task, "offset"     );  task_out_u32(    task, shall_be_same(u32(0x000004a8), U32(1192))               );
                task_elt(task, "align"      );  task_out_u32(    task, u32(0x00000000)                                         );
                task_elt(task, "reloff"     );  task_out_u32(    task, u32(0x00000000)                                         );
                task_elt(task, "nreloc"     );  task_out_u32(    task, u32(0x00000000)                                         );
                task_elt(task, "flags"      );  task_out_u32(    task, shall_be_same(u32(0x00000002), U32(S_CSTRING_LITERALS)) );
                task_elt(task, "reserved1"  );  task_out_u32(    task, u32(0x00000000)                                         );
                task_elt(task, "reserved2"  );  task_out_u32(    task, u32(0x00000000)                                         );
                task_elt(task, "reserved3"  );  task_out_u32(    task, u32(0x00000000)                                         );

              } task_end_elt(task, "section_64");

              task_at(task, 0x01A0);
              task_beg_elt(task, "section_64"); {

                task_elt(task, "sectname"   );  task_out_v16u8(  task,  (V16U8){.str = u8"__unwind_info"}  );
                task_elt(task, "segname"    );  task_out_v16u8(  task,  (V16U8){.str = u8"__TEXT"}         );
                task_elt(task, "addr"       );  task_out_u64(    task,  u64(0x00000001'000004b0)           );
                task_elt(task, "size"       );  task_out_u64(    task,  u64(0x00000000'00000058)           );
                task_elt(task, "offset"     );  task_out_u32(    task,  u32(0x000004b0)                    );
                task_elt(task, "align"      );  task_out_u32(    task,  u32(0x00000002)                    );
                task_elt(task, "reloff"     );  task_out_u32(    task,  u32(0x00000000)                    );
                task_elt(task, "nreloc"     );  task_out_u32(    task,  u32(0x00000000)                    );
                task_elt(task, "flags"      );  task_out_u32(    task,  u32(0x00000000)                    );
                task_elt(task, "reserved1"  );  task_out_u32(    task,  u32(0x00000000)                    );
                task_elt(task, "reserved2"  );  task_out_u32(    task,  u32(0x00000000)                    );
                task_elt(task, "reserved3"  );  task_out_u32(    task,  u32(0x00000000)                    );

              } task_end_elt(task, "section_64");

            } task_end_elt(task, "sections");

          } task_end_elt(task, "segment_command_64");

          task_at(task, 0x01F0);
          task_beg_elt(task, "segment_command_64"); {

            task_elt(  task, "cmd"       );  task_out_u32(    task,  shall_be_same(u32(0x00000019), U32(LC_SEGMENT_64))  );
            task_elt(  task, "cmdsize"   );  task_out_u32(    task,  u32(0x00000098)                                     );
            task_elt(  task, "segname"   );  task_out_v16u8(  task,  (V16U8){.str = u8"__DATA_CONST"}                    );
            task_elt(  task, "vmaddr"    );  task_out_u64(    task,  u64(0x00000001'00004000)                            );
            task_elt(  task, "vmsize"    );  task_out_u64(    task,  u64(0x00000000'00004000)                            );
            task_elt(  task, "fileoff"   );  task_out_u64(    task,  u64(0x00000000'00004000)                            );
            task_elt(  task, "filesize"  );  task_out_u64(    task,  u64(0x00000000'00004000)                            );
            task_elt(  task, "maxprot"   );  task_out_u32(    task,  shall_be_same(u32(0x00000003),
                                                                                   ( U32(VM_PROT_READ)
                                                                                   | U32(VM_PROT_WRITE)
                                                                                   )));
            task_elt(  task, "initprot"  );  task_out_u32(    task,  u32(0x00000003)                                     );
            task_elt(  task, "nsects"    );  task_out_u32(    task,  u32(0x00000001)                                     );
            task_elt(  task, "flags"     );  task_out_u32(    task,  shall_be_same(u32(0x00000010),
                                                                                   U32(SG_READ_ONLY)));

            task_at(task, 0x0238);
            task_beg_elt(task, "sections"); {

              task_beg_elt(task, "section_64"); {

                task_elt(task, "sectname"   );                                                        task_out_v16u8(  task,  (V16U8){.str = u8"__got"}         );
                task_elt(task, "segname"    );                                                        task_out_v16u8(  task,  (V16U8){.str = u8"__DATA_CONST"}  );
                task_elt(task, "addr"       );                                                        task_out_u64(    task,  u64(0x00000001'00004000)          );
                task_elt(task, "size"       );                                                        task_out_u64(    task,  u64(0x00000000'00000008)          );
                task_elt(task, "offset"     );                                                        task_out_u32(    task,  u32(0x00004000)                   );
                task_elt(task, "align"      );                                                        task_out_u32(    task,  u32(0x00000003)                   );
                task_elt(task, "reloff"     );                                                        task_out_u32(    task,  u32(0x00000000)                   );
                task_elt(task, "nreloc"     );                                                        task_out_u32(    task,  u32(0x00000000)                   );
                task_elt(task, "flags"      );                                                        task_out_u32(    task,  shall_be_same(u32(0x00000006),
                                                                                                                                            U32(S_NON_LAZY_SYMBOL_POINTERS)));
                task_elt(task, "reserved1"  );  task_elt(task, "index_into_indirect_symbol_table");   task_out_u32(    task,  u32(0x00000001)                   );
                task_elt(task, "reserved2"  );                                                        task_out_u32(    task,  u32(0x00000000)                   );
                task_elt(task, "reserved3"  );                                                        task_out_u32(    task,  u32(0x00000000)                   );

              } task_end_elt(task, "section_64");

            } task_end_elt(task, "sections");

          } task_end_elt(task, "segment_command_64");

          task_at(task, 0x0288);
          task_beg_elt(task, "segment_command_64"); {

            task_elt(  task, "cmd"       );  task_out_u32(    task,  shall_be_same(u32(0x00000019), U32(LC_SEGMENT_64))  );
            task_elt(  task, "cmdsize"   );  task_out_u32(    task,  u32(0x00000048)                                    );
            task_elt(  task, "segname"   );  task_out_v16u8(  task,  (V16U8){.str = u8"__LINKEDIT"}                     );
            task_elt(  task, "vmaddr"    );  task_out_u64(    task,  u64(0x00000001'00008000)                           );
            task_elt(  task, "vmsize"    );  task_out_u64(    task,  u64(0x00000000'00004000)                           );
            task_elt(  task, "fileoff"   );  task_out_u64(    task,  u64(0x00000000'00008000)                           );
            task_elt(  task, "filesize"  );  task_out_u64(    task,  u64(0x00000000'00000298)                           );
            task_elt(  task, "maxprot"   );  task_out_u32(    task,  u32(0x00000001)                                    );
            task_elt(  task, "initprot"  );  task_out_u32(    task,  u32(0x00000001)                                    );
            task_elt(  task, "nsects"    );  task_out_u32(    task,  u32(0x00000000)                                    );
            task_elt(  task, "flags"     );  task_out_u32(    task,  u32(0x00000000)                                    );

          } task_end_elt(task, "segment_command_64");

          task_at(task, 0x02D0);
          task_beg_elt(task, "linkedit_data_command"); {

            task_elt(  task,  "cmd"             );  task_out_u32(  task,  shall_be_same(
                                                                            u32(0x80000034),
                                                                            shall_be_same(
                                                                              U32(LC_DYLD_CHAINED_FIXUPS),
                                                                              ( U32(0x34)
                                                                              | U32(LC_REQ_DYLD)
                                                                              ))));
            task_elt(  task,  "cmdsize"         );  task_out_u32(  task,  u32(0x00000010));
            task_elt(  task,  "dataoff"         );  task_out_u32(  task,  u32(0x00008000));
            task_elt(  task,  "datasize"        );  task_out_u32(  task,  u32(0x00000060));

          } task_end_elt(task, "linkedit_data_command");

          task_at(task, 0x02E0);
          task_beg_elt(task, "linkedit_data_command"); {
            task_elt(task, "cmd"       ); task_out_u32(task, shall_be_same(
                                                               u32(0x80000033),
                                                               shall_be_same(
                                                                 U32(LC_DYLD_EXPORTS_TRIE),
                                                                 ( U32(0x33)
                                                                 | U32(LC_REQ_DYLD)
                                                                 ))));
            task_elt(task, "cmdsize"   ); task_out_u32(task, u32(0x00000010));
            task_elt(task, "dataoff"   ); task_out_u32(task, u32(0x00008060));
            task_elt(task, "datasize"  ); task_out_u32(task, u32(0x00000030));
          } task_end_elt(task, "linkedit_data_command");

          task_at(task, 0x02F0);
          task_beg_elt(task, "symtab_command"); {
            task_elt(task, "cmd"      ); task_out_u32(task, shall_be_same(u32(0x00000002), U32(LC_SYMTAB)));
            task_elt(task, "cmdsize"  ); task_out_u32(task, u32(0x00000018));
            task_elt(task, "symoff"   ); task_out_u32(task, u32(0x00008098));
            task_elt(task, "nsyms"    ); task_out_u32(task, u32(0x00000003));
            task_elt(task, "stroff"   ); task_out_u32(task, u32(0x000080d0));
            task_elt(task, "strsize"  ); task_out_u32(task, u32(0x00000028));
          } task_end_elt(task, "symtab_command");

          task_at(task, 0x0308);
          task_beg_elt(task, "dysymtab_command"); {
            task_elt(task, "cmd"             ); task_out_u32(task, shall_be_same(u32(0x0000000b), U32(LC_DYSYMTAB)));
            task_elt(task, "cmdsize"         ); task_out_u32(task, u32(0x00000050));
            task_elt(task, "ilocalsym"       ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nlocalsym"       ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "iextdefsym"      ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nextdefsym"      ); task_out_u32(task, u32(0x00000002));
            task_elt(task, "iundefsym"       ); task_out_u32(task, u32(0x00000002));
            task_elt(task, "nundefsym"       ); task_out_u32(task, u32(0x00000001));
            task_elt(task, "tocoff"          ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "ntoc"            ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "modtaboff"       ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nmodtab"         ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "extrefsymoff"    ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nextrefsyms"     ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "indirectsymoff"  ); task_out_u32(task, u32(0x000080c8));
            task_elt(task, "nindirectsyms"   ); task_out_u32(task, u32(0x00000002));
            task_elt(task, "extreloff"       ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nextrel"         ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "locreloff"       ); task_out_u32(task, u32(0x00000000));
            task_elt(task, "nlocrel"         ); task_out_u32(task, u32(0x00000000));
          } task_end_elt(task, "dysymtab_command");

          task_at(task, 0x0358);
          task_beg_elt(task, "dylinker_command"); {
            task_elt(task, "cmd"); task_out_u32(task, shall_be_same(u32(0x0000000e), U32(LC_LOAD_DYLINKER)));
            task_elt(task, "cmdsize"); task_out_u32(task, u32(0x00000020));
            task_elt(task, "name");
            task_out_u32(task, u32(0x0000000c)); // this.end - parent.begin
            task_out_str(task, "/usr/lib/dyld");
            // `cmdsize` is a multiple of 8 on a 64-bit arch
            task_out_pad(task, sizeof(U64));
          } task_end_elt(task, "dylinker_command");

          task_at(task, 0x0378);
          task_beg_elt(task, "uuid_command"); {
            task_elt(task, "cmd"); task_out_u32(task, shall_be_same(u32(0x0000001b), U32(LC_UUID)));
            task_elt(task, "cmdsize"); task_out_u32(task, u32(0x00000018));
            task_elt(task, "uuid");
            task_out_v16u8(
              task,
              (V16U8){
                .vec = {
                  U8(0xEC), U8(0x0C), U8(0x26), U8(0xFD),
                  U8(0xDE), U8(0x18), U8(0x31), U8(0x25),
                  U8(0xBB), U8(0x14), U8(0x82), U8(0x52),
                  U8(0x02), U8(0x43), U8(0x59), U8(0xD9),
                }
              }
            );
          } task_end_elt(task, "uuid_command");

          task_at(task, 0x0390);
          task_beg_elt(task, "build_version_command"); {

            task_elt(task, "cmd");
            task_out_u32(
              task,
              shall_be_same(
                u32(0x00000032),
                U32(LC_BUILD_VERSION)
              )
            );

            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000020));

            task_elt(task, "platform");
            task_out_u32(
              task,
              shall_be_same(
                u32(0x00000001),
                U32(PLATFORM_MACOS)
              )
            );

            task_elt(task, "minos");
            task_out_u32(
              task,
              shall_be_same(
                u32(0x000f0000),
                ( U32(u16(15))  << 0'2'0
                | U32( u8( 0))  << 0'1'0
                | U32( u8( 0))  << 0'0'0
                )
              )
            );

            task_elt(task, "sdk");
            task_out_u32(
              task,
              shall_be_same(
                u32(0x000f0500),
                // X.Y.Z
                ( U32(u16(15))  << 0'2'0
                | U32( u8( 5))  << 0'1'0
                | U32( u8( 0))  << 0'0'0
                )
              )
            );

            task_elt(task, "ntools");
            task_out_u32(task, u32(0x00000001));

            task_beg_elt(task, "build_tool_version"); {

              task_elt(task, "tool");
              task_out_u32(
                task,
                shall_be_same(
                  u32(0x00000003),
                  U32(TOOL_LD)
                )
              );

              task_elt(task, "version");
              task_out_u32(
                task,
                shall_be_same(
                  u32(0x048f0500),
                  // X.Y.Z
                  ( U32(u16(1167))  << 0'2'0
                  | U32( u8(   5))  << 0'1'0
                  | U32( u8(   0))  << 0'0'0
                  )
                )
              );

            } task_end_elt(task, "build_tool_version");

          } task_end_elt(task, "build_version_command");

          task_at(task, 0x03B0);
          task_beg_elt(task, "source_version_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(u32(0x0000002a), U32(LC_SOURCE_VERSION)));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000010));
            task_out_u64(
              task,
              shall_be_same(
                u64(0x00000000'00000000),
                // A.B.C.D.E
                ( U64(u24(0)) << 40
                | U64(u10(0)) << 30
                | U64(u10(0)) << 20
                | U64(u10(0)) << 10
                | U64(u10(0)) <<  0
                )
              )
            );
          } task_end_elt(task, "source_version_command");

          task_at(task, 0x03C0);
          task_beg_elt(task, "entry_point_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(
                                 u32(0x80000028),
                                 shall_be_same(
                                   U32(LC_MAIN),
                                   ( U32(0x28)
                                   | U32(LC_REQ_DYLD)
                                   ))));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000018));
            task_elt(task, "entryoff");
            //  _main - __TEXT
            task_out_u64(task, u64(0x00000000'00000460));
            task_elt(task, "stacksize");
            //  0 or initial stack size
            task_out_u64(task, u64(0x00000000'00000000));
          } task_end_elt(task, "entry_point_command");

          task_at(task, 0x03D8);
          task_beg_elt(task, "dylib_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(u32(0x0000000c), U32(LC_LOAD_DYLIB)));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000038));
            task_beg_elt(task, "dylib"); {
              task_elt(task, "name");
              task_out_u32(task, u32(0x00000018));
              task_elt(task, "timestamp");
              // 1969-12-31 00:00:02 UTC
              task_out_u32(task, u32(0x00000002));
              task_elt(task, "current_version");
              task_out_u32(
                task,
                shall_be_same(
                  u32(0x05470000),
                  // X.Y.Z
                  ( U32(u16(1351))  << 0'2'0
                  | U32( u8(   0))  << 0'1'0
                  | U32( u8(   0))  << 0'0'0
                  )
                )
              );
              task_elt(task, "compatibility_version");
              task_out_u32(
                task,
                shall_be_same(
                  u32(0x00010000),
                  ( U32(u16(1))  << 0'2'0
                  | U32( u8(0))  << 0'1'0
                  | U32( u8(0))  << 0'0'0
                  )
                )
              );
            } task_end_elt(task, "dylib");

            task_out_str(task, "/usr/lib/libSystem.B.dylib");
            task_out_pad(task, sizeof(U64));

          } task_end_elt(task, "dylib_command");

          task_at(task, 0x0410);
          task_beg_elt(task, "linkedit_data_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(u32(0x00000026), U32(LC_FUNCTION_STARTS)));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000010));
            task_elt(task, "dataoff");
            task_out_u32(task, u32(0x00008090));
            task_elt(task, "datasize");
            task_out_u32(task, u32(0x00000008));
          } task_end_elt(task, "linkedit_data_command");

          task_at(task, 0x0420);
          task_beg_elt(task, "linkedit_data_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(u32(0x00000029), U32(LC_DATA_IN_CODE)));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000010));
            task_elt(task, "dataoff");
            task_out_u32(task, u32(0x00008098));
            task_elt(task, "datasize");
            task_out_u32(task, u32(0x00000000));
          } task_end_elt(task, "linkedit_data_command");

          task_at(task, 0x0430);
          task_beg_elt(task, "linkedit_data_command"); {
            task_elt(task, "cmd");
            task_out_u32(task, shall_be_same(u32(0x0000001d), U32(LC_CODE_SIGNATURE)));
            task_elt(task, "cmdsize");
            task_out_u32(task, u32(0x00000010));
            task_elt(task, "dataoff");
            task_out_u32(task, u32(0x00008100));
            task_elt(task, "datasize");
            task_out_u32(task, u32(0x00000198));
          } task_end_elt(task, "linkedit_data_command");

          {
            // padding
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
            task_out_u32(task, u32(0x00000000));
          }

        } task_end_elt(task, "load_commands");

        task_at(task, 0x0460);

        /*  task_out_pad(task, PAGE_SIZE);  */

        {
          task_at(task, 0x0460);
          // __TEXT,__text._main
          task_out_u32(task, u32(0xd100c3ff));  //  sub sp, sp, #0x30
          task_out_u32(task, u32(0xa9027bfd));  //  stp x29, x30, [sp, #0x20]
          task_out_u32(task, u32(0x910083fd));  //  add x29, sp, #0x20
          task_out_u32(task, u32(0x52800008));  //  mov w8, #0x0
          task_out_u32(task, u32(0xb9000fe8));  //  str w8, [sp, #0xc]
          task_out_u32(task, u32(0xb81fc3bf));  //  stur wzr, [x29, #-0x4]
          task_out_u32(task, u32(0xb81f83a0));  //  stur w0, [x29, #-0x8]
          task_out_u32(task, u32(0xf9000be1));  //  str x1, [sp, #0x10]
          task_out_u32(task, u32(0x90000000));  //  adrp x0, 0; 0x10000000
          task_out_u32(task, u32(0x9112a000));  //  add x0, x0, #0x4a8 ; "reow"
          task_out_u32(task, u32(0x94000005));  //  bl 0x10000049c ; _puts
          task_out_u32(task, u32(0xb9400fe0));  //  ldr w0, [sp, #0xc]
          task_out_u32(task, u32(0xa9427bfd));  //  ldp x29, x30, [sp, #0x20]
          task_out_u32(task, u32(0x9100c3ff));  //  add sp, sp, #0x30
          task_out_u32(task, u32(0xd65f03c0));  //  ret

          task_at(task, 0x049C);
          // ?
          task_out_u32(task, u32(0x90000030));
          task_out_u32(task, u32(0xf9400210));
          task_out_u32(task, u32(0xd61f0200));

          task_at(task, 0x04A8);
          // "reow"
          task_out_u32(task, u32(0x776f6572));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x0000001c));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x0000001c));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x0000001c));
          task_out_u32(task, u32(0x00000002));
          task_out_u32(task, u32(0x00000460));
          task_out_u32(task, u32(0x00000040));
          task_out_u32(task, u32(0x00000040));

          task_at(task, 0x04D8);
          // _puts
          task_out_u32(task, u32(0x0000049c));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000040));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000003));
          task_out_u32(task, u32(0x0001000c));
          task_out_u32(task, u32(0x00010010));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x04000000));

          //  14 3/4 KiB of zeros

          // buf_skip(&BUF, +0x3B00);
          task_out_pad(task, 0x4000);

          task_at(task, 0x4000);
          task_out_u64(task, u64(0x80000000'00000000));

          // buf_skip(&BUF, +0x3FFC);
          task_out_pad(task, 0x8000);

          // 16 KiB of zeros

          task_at(task, 0x8000);
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000020));
          task_out_u32(task, u32(0x00000050));
          task_out_u32(task, u32(0x00000054));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000004));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000018));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000018));
          task_out_u32(task, u32(0x00064000));
          task_out_u32(task, u32(0x00004000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x00000201));

          // "_puts"
          task_at(task, 0x8054);
          task_out_u32(task, u32(0x75705f00));
          task_out_u32(task, u32(0x00007374));

          task_out_u32(task, u32(0x00000000));

          // "_"
          task_at(task, 0x8060);
          task_out_u32(task, u32(0x005f0100));
          task_out_u32(task, u32(0x00000012));
          task_out_u32(task, u32(0x00000200));
          task_out_u32(task, u32(0xe0000300));
          task_out_u32(task, u32(0x02000008));

          // "_mh_execute_header"
          // "main"
          task_out_u32(task, u32(0x5f686d5f));
          task_out_u32(task, u32(0x63657865));
          task_out_u32(task, u32(0x5f657475));
          task_out_u32(task, u32(0x64616568));
          task_out_u32(task, u32(0x09007265));
          task_out_u32(task, u32(0x6e69616d));

          task_at(task, 0x808C);
          task_out_u32(task, u32(0x00000d00));
          task_out_u32(task, u32(0x000008e0));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000002));
          task_out_u32(task, u32(0x0010010f));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x00000016));
          task_out_u32(task, u32(0x0000010f));
          task_out_u32(task, u32(0x00000460));
          task_out_u32(task, u32(0x00000001));
          task_out_u32(task, u32(0x0000001c));
          task_out_u32(task, u32(0x01000001));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000002));
          task_out_u32(task, u32(0x00000002));

          task_at(task, 0x80D0);
          // "__mh_execute_header"
          // "_main"
          // "_puts"
          task_out_u32(task, u32(0x5f5f0020));
          task_out_u32(task, u32(0x655f686d));
          task_out_u32(task, u32(0x75636578));
          task_out_u32(task, u32(0x685f6574));
          task_out_u32(task, u32(0x65646165));
          task_out_u32(task, u32(0x6d5f0072));
          task_out_u32(task, u32(0x006e6961));
          task_out_u32(task, u32(0x7475705f));
          task_out_u32(task, u32(0x00000073));

          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));

          task_at(task, 0x8100);
          task_out_u32(task, u32(0xc00cdefa));
          task_out_u32(task, u32(0x95010000));
          task_out_u32(task, u32(0x01000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x14000000));

          task_at(task, 0x8114);
          task_out_u32(task, u32(0x020cdefa));
          task_out_u32(task, u32(0x81010000));
          task_out_u32(task, u32(0x00040200));
          task_out_u32(task, u32(0x02000200));
          task_out_u32(task, u32(0x61000000));
          task_out_u32(task, u32(0x58000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x09000000));
          task_out_u32(task, u32(0x00810000));
          task_out_u32(task, u32(0x0c000220));

          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x00000000));

          task_at(task, 0x8160);
          task_out_u32(task, u32(0x3c000000));
          task_out_u32(task, u32(0x00000000));
          task_out_u32(task, u32(0x01000000));

          task_at(task, 0x816C);
          // "reow"
          task_out_u32(task, u32(0x776f6572));
          // ".bin"
          task_out_u32(task, u32(0x6e69622e));

          task_at(task, 0x8174);
          task_out_u32(task, u32(0xa3d84c00));
          task_out_u32(task, u32(0xf17b0c0b));
          task_out_u32(task, u32(0xed0e7b23));
          task_out_u32(task, u32(0xc02a8a13));
          task_out_u32(task, u32(0xfd8bf22a));
          task_out_u32(task, u32(0x5c0dea5d));
          task_out_u32(task, u32(0xa78ff427));
          task_out_u32(task, u32(0xc21f4fc1));
          task_out_u32(task, u32(0xac7fadf1));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xac7fada7));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xac7fada7));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xebd5dfa7));
          task_out_u32(task, u32(0x6695f186));
          task_out_u32(task, u32(0x062ca103));
          task_out_u32(task, u32(0x1f63f436));
          task_out_u32(task, u32(0x0b0df166));
          task_out_u32(task, u32(0xa3eed4b8));
          task_out_u32(task, u32(0xe0825bd2));
          task_out_u32(task, u32(0xb40292e5));
          task_out_u32(task, u32(0xac7faded));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xac7fada7));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xac7fada7));
          task_out_u32(task, u32(0xc66f58b2));
          task_out_u32(task, u32(0x04c066e9));
          task_out_u32(task, u32(0x6bd1d1d7));
          task_out_u32(task, u32(0x05584f02));
          task_out_u32(task, u32(0x7cb47cff));
          task_out_u32(task, u32(0xbdda857a));
          task_out_u32(task, u32(0x2c89488b));
          task_out_u32(task, u32(0xb72601a7));
          task_out_u32(task, u32(0x5edb6ef7));
          task_out_u32(task, u32(0x650adc99));
          task_out_u32(task, u32(0x98549d4b));
          task_out_u32(task, u32(0x5f8a3929));
          task_out_u32(task, u32(0x946de112));
          task_out_u32(task, u32(0x614d53eb));
          task_out_u32(task, u32(0x3f1ecea2));

          task_out_u32(task, u32(0x00000041));

        }

      } task_end_elt(task, "mach_object");

    } if (fat_binary_enabled) task_end_elt(task, "fat_binary");

  } task_end_elt(task, "file");

  task_end(task);

  return true;

}


//  Count the number of elements in the program
////////////////////////////////////////////////////////////////

static constexpr SizeVar num_elts_min_depth = 1;

struct_type(NumEltsTask);

struct NumEltsTask {
  TaskVar  task;
  SizeVar  begs;
  SizeVar  depth;
  SizeVar  leaves;
  SizeVar  ends;
};

static inline Bool
num_elts_open(
  NumEltsTaskVarRef num_elts
);

static inline Bool
num_elts_beg_elt(
  TaskVarRef task,
  [[maybe_unused]]
  Tag tag
);

static inline Bool
num_elts_elt(
  TaskVarRef task,
  [[maybe_unused]]
  Tag tag
);

static inline Bool
num_elts_end_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
num_elts_end(
  TaskVarRef task
);

static inline Bool
num_elts_open(
  NumEltsTaskVarRef num_elts
) {
  shall(num_elts != nullptr);
  *num_elts = (NumEltsTask){
    .task = (Task){

      .beg_elt  = num_elts_beg_elt  ,
      .elt      = num_elts_elt      ,
      .end_elt  = num_elts_end_elt  ,
      .end      = num_elts_end      ,

    },

    .begs    = 0                   ,
    .depth   = num_elts_min_depth  ,
    .leaves  = 0                   ,
    .ends    = 0                   ,

  };
  return true;
}

static inline Bool
num_elts_task(
  NumEltsTaskVarRef num_elts
) {
  shall(num_elts != nullptr);
  return
    num_elts_open(num_elts) and
    work((TaskVarRef)num_elts) and
    (
      trace(
        "counted "
        "(%zu = %zu) branches + %zu leaves = %zu elements",
        num_elts->begs,
        num_elts->ends,
        num_elts->leaves,
        num_elts->ends + num_elts->leaves
      ),
      true
    );
}

static inline Bool num_elts_beg_elt(
  TaskVarRef task,
  [[maybe_unused]]
  Tag tag
) {
  shall(task != nullptr);
  NumEltsTaskVarRef num_elts = (NumEltsTaskVarRef)task;
  shall(num_elts->begs < SIZE_MAX);
  shall(num_elts->depth < SIZE_MAX);
  return
    ++num_elts->begs,
    ++num_elts->depth,
    true;
}

static inline Bool num_elts_elt(
  TaskVarRef task,
  [[maybe_unused]]
  Tag tag
) {
  shall(task != nullptr);
  NumEltsTaskVarRef num_elts = (NumEltsTaskVarRef)task;
  shall(num_elts->leaves < SIZE_MAX);
  return
    ++num_elts->leaves,
    true;
}

static inline Bool num_elts_end_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  NumEltsTaskVarRef num_elts = (NumEltsTaskVarRef)task;
  shall(num_elts->ends < SIZE_MAX);
  return
    num_elts->depth >= num_elts_min_depth ? (
      ++num_elts->ends,
      --num_elts->depth,
      true
    ) :
    (
      error(
        "missing begin tag; "
        "name: %s, "
        "begs: %zu, "
        "ends: %zu, "
        "depth: %zu",
        tag,
        num_elts->begs,
        num_elts->ends,
        num_elts->depth
      ),
      false
    );
}

static inline Bool num_elts_end(
  TaskVarRef task
) {
  shall(task != nullptr);
  NumEltsTaskVarRef num_elts = (NumEltsTaskVarRef)task;
  return
    num_elts->depth == num_elts_min_depth and
    num_elts->begs == num_elts->ends
    or (
      error(
        "missing end tag; "
        "begs: %zu, "
        "depth: %zu, "
        "leaves: %zu, "
        "ends: %zu",
        num_elts->begs,
        num_elts->depth,
        num_elts->leaves,
        num_elts->ends
      ),
      false
    );
}


//  Count the number of bytes to allocate for tag names
////////////////////////////////////////////////////////////////

static constexpr SizeVar tag_alignment = 2;

static_assert(1 << tag_alignment == sizeof(U32));

struct_type(NumTagSizeTask);

struct NumTagSizeTask {
  TaskVar  task;
  SizeVar  tags;     // Tag bytes without NUL
  SizeVar  null;     // NUL bytes
  SizeVar  padding;  // Padding bytes
  SizeVar  total;    // Total bytes
  SizeVar  max;      // Highest single tag size without NUL
};

static inline Bool
num_tag_size_task(
  NumTagSizeTaskVarRef num_tag_size
);

static inline Bool
num_tag_size_wf(
  NumTagSizeTaskRef num_tag_size
);

static inline Bool
num_tag_size_open(
  NumTagSizeTaskVarRef num_tag_size
);

static inline Bool
num_tag_size_beg_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
num_tag_size_end(
  TaskVarRef task
);

////////////////////////////////

static inline Bool
num_tag_size_task(
  NumTagSizeTaskVarRef num_tag_size
) {
  shall(num_tag_size != nullptr);
  return
    num_tag_size_open(num_tag_size) and
    work((TaskVarRef)num_tag_size) and
    (
      trace("counted %zu tag bytes", num_tag_size->tags),
      trace("counted %zu NUL bytes", num_tag_size->null),
      trace("counted %zu pad bytes", num_tag_size->padding),
      trace("counted %zu total bytes", num_tag_size->total),
      trace("max tag size %zu bytes", num_tag_size->max),
      true
    );
}

static inline Bool
num_tag_size_wf(
  NumTagSizeTaskRef num_tag_size
) {
  SizeVar total;
  return
    should(num_tag_size != nullptr) and
    (
      (total = num_tag_size->tags + num_tag_size->null + num_tag_size->padding),
      should(num_tag_size->total == total, "%zu != %zu", num_tag_size->total, total) and
      should(total % (1 << tag_alignment) == 0)
    );
}

static inline Bool
num_tag_size_open(
  NumTagSizeTaskVarRef num_tag_size
) {
  shall(num_tag_size != nullptr);
  *num_tag_size = (NumTagSizeTask){
    .task = (Task){

      .beg_elt  = num_tag_size_beg_elt  ,
      .end      = num_tag_size_end      ,

    },

    .tags     = 0  ,
    .null     = 0  ,
    .padding  = 0  ,
    .max      = 0  ,

  };
  return true;
}

static inline Bool num_tag_size_beg_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  NumTagSizeTaskVarRef num_tag_size = (NumTagSizeTaskVarRef)task;
  shall(num_tag_size_wf(num_tag_size));
  Size tags = strlen(tag);
  shall(size_has(num_tag_size->tags, tags));
  shall(size_has(num_tag_size->null, sizeof NUL));
  Size padding = below_64(tags + sizeof NUL, tag_alignment);
  Size null = sizeof NUL;
  num_tag_size->tags += tags;
  num_tag_size->null += null;
  num_tag_size->padding += padding;
  {
    SizeVar total = num_tag_size->total;
    shall(size_has(total, tags));
    total += tags;
    shall(size_has(total, null));
    total += null;
    shall(size_has(total, padding));
    total += padding;
    num_tag_size->total = total;
  }
  if (num_tag_size->max < tags) num_tag_size->max = tags;
  return true;
}

static inline Bool
num_tag_size_end(
  TaskVarRef task
) {
  shall(task != nullptr);
  NumTagSizeTaskVarRef num_tag_size = (NumTagSizeTaskVarRef)task;
  should(
    num_tag_size->null <= num_tag_size->tags,
    "there are %zu B of NULs and %zu B of characters, "
    "yet there should be far fewer NULs than characters, "
    "unless all strings are empty",
    num_tag_size->null,
    num_tag_size->tags
  );
  should(
    num_tag_size->padding != 0,
    "there are 0 B of padding, "
    "but this is unlikely "
    "unless all strings including NULs happen to be aligned"
  );
  return true;
}


//  Count the number of unique tags to intern
////////////////////////////////////////////////////////////////

struct_type(TagNum);

struct TagNum {
  TagVar tag;
  NumVar num;
};

struct_type(NumTagsTask);

struct NumTagsTask {
  TaskVar          task;
  TagNumVarRefVar  set;
  NumVar           num;
  NumVar           end;
};

static inline Bool
num_tags_task(
  NumTagsTaskVarRef num_tags,
  NumEltsTaskRef num_elts
);

static inline Bool
num_tags_wf(
  NumTagsTaskVarRef num_tags
);

static inline Bool
num_tags_open(
  NumTagsTaskVarRef num_tags,
  Num elts
);

static inline Bool
num_tags_beg_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
num_tags_task(
  NumTagsTaskVarRef num_tags,
  NumEltsTaskRef num_elts
) {
  return
    num_tags_open(num_tags, num_elts->begs + num_elts->leaves) and
    shall(num_tags_wf(num_tags)) and
    work((TaskVarRef)num_tags) and
    (
      trace("counted %zu unique tags", num_tags->num),
      true
    );
}

static inline Bool
num_tags_wf(
  NumTagsTaskVarRef num_tags
) {
  return
    should(num_tags != nullptr) and
    should(when(num_tags->end != 0, num_tags->set != nullptr)) and
    should(num_tags->num <= num_tags->end);
}

static inline Bool
num_tags_open(
  NumTagsTaskVarRef num_tags,
  Num elts
) {
  shall(num_tags != nullptr);
  Size elt_size = sizeof num_tags->set[0];
  typeof(num_tags->set) const set = calloc(elts, elt_size);
  Bool const calloc_succeeded = shall(set != nullptr);
  *num_tags = (NumTagsTask){
    .task = (Task){
      .beg_elt = num_tags_beg_elt,
    },
    .set = set,
    .num = 0,
    .end = ((void)calloc_succeeded, elts * elt_size),
  };
  return true;
}

static inline Bool
num_tags_beg_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  shall(tag != nullptr);
  NumTagsTaskVarRef num_tags = (NumTagsTaskVarRef)task;
  shall(num_tags_wf(num_tags));
  for (IdxVar i = 0; i < num_tags->num; ++i) {
    if (strcmp(num_tags->set[i].tag, tag) == 0) {
      ++num_tags->set[i].num;
      return true;
    }
  }
  shall(num_tags->num < num_tags->end);
  num_tags->set[num_tags->num].tag = tag;
  num_tags->set[num_tags->num].num = 1;
  ++num_tags->num;
  return true;
}

static inline Bool
num_tags_shut(
  NumTagsTaskVarRef num_tags
) {
  shall(num_tags_wf(num_tags));
  free(num_tags->set);
  *num_tags = (NumTagsTask){};
  return true;
}


//  Generate output
////////////////////////////////////////////////////////////////

struct_type(OutputTask);

struct OutputTask {
  TaskVar      task       ;
  FilePathVar  file_path  ;
  BufVar       buf        ;
};

////////////////////////////////

static inline Bool
output_task(
  OutputTaskVarRef  output,
  FilePath          file_path
);

static inline Bool
output_wf(
  OutputTaskRef output
);

static inline Bool
output_open(
  OutputTaskVarRef  output,
  FilePath          file_path
);

static inline Bool
output_at(
  TaskVarRef task,
  Idx idx
);

static inline Bool
output_beg_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
output_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
output_out_u32(
  TaskVarRef task,
  U32 val
);

static inline Bool
output_out_u64(
  TaskVarRef task,
  U64 val
);

static inline Bool
output_out_v16u8(
  TaskVarRef task,
  V16U8 val
);

static inline Bool
output_out_pad(
  TaskVarRef task,
  Stride stride
);

static inline Bool
output_out_str(
  TaskVarRef  task,
  Str         str
);

static inline Bool
output_end_elt(
  TaskVarRef task,
  Tag tag
);

static inline Bool
output_end(
  TaskVarRef task
);

static inline Bool
output_shut(
  OutputTaskVarRef output
);

////////////////////////////////

static inline Bool
output_task(
  OutputTaskVarRef output,
  FilePath file_path
) {
  return
    shall(output != nullptr) and
    output_open(output, file_path) and
    after(
      work((TaskVarRef)output),
      output_shut(output)
    );
}

static inline Bool
output_wf(
  OutputTaskRef output
) {
  return
    should(output != nullptr) and
    should(output->file_path != nullptr) and
    should(buf_wf(&output->buf));
}

static inline Bool
output_open(
  OutputTaskVarRef output,
  FilePath         file_path
) {
  *output = (OutputTaskVar){
    .task = (Task){

      .at         = output_at         ,
      .beg_elt    = output_beg_elt    ,
      .elt        = output_elt        ,
      .out_u32    = output_out_u32    ,
      .out_u64    = output_out_u64    ,
      .out_v16u8  = output_out_v16u8  ,
      .out_pad    = output_out_pad    ,
      .out_str    = output_out_str    ,
      .end_elt    = output_end_elt    ,
      .end        = output_end        ,

    },
    .file_path = file_path,
    .buf = (Buf){

      .in     = &reow[0]         ,
      .owner  = (Owner){Static}  ,
      .at     = 0                ,
      .end    = numof(reow)      ,

    }
  };
  return true;
}

static inline Bool
output_at(
  TaskVarRef task,
  Idx idx
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "at %.8zX",
    output->buf.at,
    idx
  );
  should(
    output->buf.at == idx,
    "at offset %0.8zX, should be at offset %0.8zX",
    output->buf.at,
    idx
  );
  return true;
}

static inline Bool
output_beg_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "<%s>",
    output->buf.at,
    tag
  );
  return true;
}

static inline Bool
output_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "<%s>",
    output->buf.at,
    tag
  );
  return true;
}

static inline Bool
output_out_u32(
  TaskVarRef task,
  U32 val
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "u32 "
    "%0.8"PRIX32" (%"PRIu32")",
    output->buf.at,
    (uint32_t)val,
    (uint32_t)val
  );
  buf_out_u32(&output->buf, val);
  return true;
}

static inline Bool
output_out_u64(
  TaskVarRef task,
  U64 val
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "u64 "
    "%0.16"PRIX64" (%"PRIu64")",
    output->buf.at,
    (uint64_t)val,
    (uint64_t)val
  );
  buf_out_u64(&output->buf, val);
  return true;
}

static inline Str
byte_str(
  U8 byte
) {
  static Str strs[(Size)UINT8_MAX + 1] = {
     [0x00]="<NUL>"  , [0x01]="<SOH>"  , [0x02]="<STX>"  , [0x03]="<ETX>"  ,  [0x04]="<EOT>"  , [0x05]="<ENQ>"  , [0x06]="<ACK>"  , [0x07]="<BEL>"  ,
     [0x08]="<BS>"   , [0x09]="<HT>"   , [0x0A]="<LF>"   , [0x0B]="<VT>"   ,  [0x0C]="<FF>"   , [0x0D]="<CR>"   , [0x0E]="<SO>"   , [0x0F]="<SI>"   ,
     [0x10]="<DLE>"  , [0x11]="<DC1>"  , [0x12]="<DC2>"  , [0x13]="<DC3>"  ,  [0x14]="<DC4>"  , [0x15]="<NAK>"  , [0x16]="<SYN>"  , [0x17]="<ETB>"  ,
     [0x18]="<CAN>"  , [0x19]="<EM>"   , [0x1A]="<SUB>"  , [0x1B]="<ESC>"  ,  [0x1C]="<FS>"   , [0x1D]="<GS>"   , [0x1E]="<RS>"   , [0x1F]="<US>"   ,
     [0x20]="<SP>"   , [0x21]="!"      , [0x22]="\""     , [0x23]="#"      ,  [0x24]="$"      , [0x25]="%"      , [0x26]="&"      , [0x27]="'"      ,
     [0x28]="("      , [0x29]=")"      , [0x2A]="*"      , [0x2B]="+"      ,  [0x2C]=","      , [0x2D]="-"      , [0x2E]="."      , [0x2F]="/"      ,
     [0x30]="0"      , [0x31]="1"      , [0x32]="2"      , [0x33]="3"      ,  [0x34]="4"      , [0x35]="5"      , [0x36]="6"      , [0x37]="7"      ,
     [0x38]="8"      , [0x39]="9"      , [0x3A]=":"      , [0x3B]=";"      ,  [0x3C]="<"      , [0x3D]="="      , [0x3E]=">"      , [0x3F]="?"      ,
     [0x40]="@"      , [0x41]="A"      , [0x42]="B"      , [0x43]="C"      ,  [0x44]="D"      , [0x45]="E"      , [0x46]="F"      , [0x47]="G"      ,
     [0x48]="H"      , [0x49]="I"      , [0x4A]="J"      , [0x4B]="K"      ,  [0x4C]="L"      , [0x4D]="M"      , [0x4E]="N"      , [0x4F]="O"      ,
     [0x50]="P"      , [0x51]="Q"      , [0x52]="R"      , [0x53]="S"      ,  [0x54]="T"      , [0x55]="U"      , [0x56]="V"      , [0x57]="W"      ,
     [0x58]="X"      , [0x59]="Y"      , [0x5A]="Z"      , [0x5B]="["      ,  [0x5C]="\\"     , [0x5D]="]"      , [0x5E]="^"      , [0x5F]="_"      ,
     [0x60]="`"      , [0x61]="a"      , [0x62]="b"      , [0x63]="c"      ,  [0x64]="d"      , [0x65]="e"      , [0x66]="f"      , [0x67]="g"      ,
     [0x68]="h"      , [0x69]="i"      , [0x6A]="j"      , [0x6B]="k"      ,  [0x6C]="l"      , [0x6D]="m"      , [0x6E]="n"      , [0x6F]="o"      ,
     [0x70]="p"      , [0x71]="q"      , [0x72]="r"      , [0x73]="s"      ,  [0x74]="t"      , [0x75]="u"      , [0x76]="v"      , [0x77]="w"      ,
     [0x78]="x"      , [0x79]="y"      , [0x7A]="z"      , [0x7B]="{"      ,  [0x7C]="|"      , [0x7D]="}"      , [0x7E]="~"      , [0x7F]="<DEL>"  ,
  };
  return byte <= 0x7F ? strs[byte] : ".";
}

static inline Bool
output_out_v16u8(
  TaskVarRef task,
  V16U8 val
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "v16u8 "
    "%0.2X%0.2X%0.2X%0.2X "
    "%0.2X%0.2X%0.2X%0.2X "
    "%0.2X%0.2X%0.2X%0.2X "
    "%0.2X%0.2X%0.2X%0.2X "
    "(%s%s%s%s%s%s%s%s%s%s%s%s%s%s%s%s)",
    output->buf.at,
    (unsigned int)val.vec[ 0],
    (unsigned int)val.vec[ 1],
    (unsigned int)val.vec[ 2],
    (unsigned int)val.vec[ 3],
    (unsigned int)val.vec[ 4],
    (unsigned int)val.vec[ 5],
    (unsigned int)val.vec[ 6],
    (unsigned int)val.vec[ 7],
    (unsigned int)val.vec[ 8],
    (unsigned int)val.vec[ 9],
    (unsigned int)val.vec[10],
    (unsigned int)val.vec[11],
    (unsigned int)val.vec[12],
    (unsigned int)val.vec[13],
    (unsigned int)val.vec[14],
    (unsigned int)val.vec[15],
    byte_str(val.vec[ 0]),
    byte_str(val.vec[ 1]),
    byte_str(val.vec[ 2]),
    byte_str(val.vec[ 3]),
    byte_str(val.vec[ 4]),
    byte_str(val.vec[ 5]),
    byte_str(val.vec[ 6]),
    byte_str(val.vec[ 7]),
    byte_str(val.vec[ 8]),
    byte_str(val.vec[ 9]),
    byte_str(val.vec[10]),
    byte_str(val.vec[11]),
    byte_str(val.vec[12]),
    byte_str(val.vec[13]),
    byte_str(val.vec[14]),
    byte_str(val.vec[15])
  );
  buf_out_v16u8(&output->buf, val);
  return true;
}

static inline Bool
output_out_pad(
  TaskVarRef task,
  Stride stride
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "pad %zu",
    output->buf.at,
    stride
  );
  buf_out_pad(&output->buf, stride);
  return true;
}

static inline Bool
output_out_str(
  TaskVarRef task,
  Str str
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "str "
    "\"%s\"",
    output->buf.at,
    str
  );
  buf_out_str(&output->buf, str, SIZE_MAX);
  return true;
}

static inline Bool
output_end_elt(
  TaskVarRef task,
  Tag tag
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace(
    "%.8zX: "
    "</%s>",
    output->buf.at,
    tag
  );
  return true;
}

static inline Bool
output_end(
  TaskVarRef task
) {
  shall(task != nullptr);
  OutputTaskVarRef output = (OutputTaskVarRef)task;
  trace("end");
  shall(output_wf(output));
  FILE *const file = fopen(output->file_path, "w");
  if (file == nullptr) return false;
  Size bytes = output->buf.at;
  trace("output %zu B", bytes);
  if (bytes != sizeof reow) warn(
    "final size %zu is less than wanted size %zu",
    bytes,
    sizeof reow
  );
  buf_rewind(&output->buf);
  shall(buf_has(&output->buf, bytes));
  Num written = fwrite(
    (void *)buf_from(&output->buf),
    1,
    bytes,
    file
  );
  fclose(file);
  should(
    written == bytes,
    "wrote %zu B / %zu B",
    written,
    bytes
  );
  return true;
}

static inline Bool
output_shut(
  OutputTaskVarRef output
) {
  shall(output_wf(output));
  buf_shut(&output->buf);
  *output = (OutputTask){};
  return true;
}


//  Run compilation passes
////////////////////////////////////////////////////////////////

static inline Bool
save_tags(
  NumTagsTaskRef num_tags,
  NumTagSizeTaskRef num_tag_size,
  BufVarRef tag_buf
);

Bool nb(
  [[maybe_unused]]
  Str pgm,
  Num arg_num,
  Args args
) {

  NumEltsTaskVar     num_elts;
  NumTagSizeTaskVar  num_tag_size;
  NumTagsTaskVar     num_tags;
  BufVar             tag_buf;
  OutputTaskVar      output;

  trace();
  return
    arg_num == 1 and
    num_elts_task(&num_elts) and
    num_tag_size_task(&num_tag_size) and
    buf_open(&tag_buf, num_tag_size.total, sizeof(Chr)) and
    after(
      (
        after(
          (
            num_tags_task(&num_tags, &num_elts) and
            save_tags(&num_tags, &num_tag_size, &tag_buf) and
            output_task(&output, args[0])
          ),
          num_tags_shut(&num_tags)
        )
      ),
      buf_shut(&tag_buf)
    ) and
    (
      trace("good"),
      true
    );
}

static inline Bool
save_tags(
  NumTagsTaskRef num_tags,
  NumTagSizeTaskRef num_tag_size,
  BufVarRef tag_buf
) {
  shall(num_tags != nullptr);
  shall(num_tag_size != nullptr);
  shall(buf_wf(tag_buf));
  for (IdxVar i = 0; i < num_tags->num; ++i) {
    buf_out_str(
      tag_buf,
      num_tags->set[i].tag,
      num_tag_size->max
    );
    buf_out_pad(tag_buf, align_stride(tag_alignment));
  }
  return true;
}


//  Unit tests
////////////////////////////////////////////////////////////////

static void test(void) {
  {
    shall_be_same(bit_64(0), u64(0b0001));
    shall_be_same(bit_64(1), u64(0b0010));
    shall_be_same(bit_64(2), u64(0b0100));
    shall_be_same(bit_64(3), u64(0b1000));

    shall_be_same(bit_64(31), u64(0x00000000'80000000));
    shall_be_same(bit_64(32), u64(0x00000001'00000000));

    shall_be_same(bit_64(60), u64(0x10000000'00000000));
    shall_be_same(bit_64(61), u64(0x20000000'00000000));
    shall_be_same(bit_64(62), u64(0x40000000'00000000));
    shall_be_same(bit_64(63), u64(0x80000000'00000000));
  }
  {
    shall_be_same(mask_64(0), u64(0x0));
    shall_be_same(mask_64(1), u64(0x1));
    shall_be_same(mask_64(2), u64(0x3));
    shall_be_same(mask_64(3), u64(0x7));

    shall_be_same(mask_64(32), u64(0x00000000'FFFFFFFF));

    shall_be_same(mask_64(61), u64(0x1FFFFFFF'FFFFFFFF));
    shall_be_same(mask_64(62), u64(0x3FFFFFFF'FFFFFFFF));
    shall_be_same(mask_64(63), u64(0x7FFFFFFF'FFFFFFFF));
    shall_be_same(mask_64(64), u64(0xFFFFFFFF'FFFFFFFF));
  }
  {
    shall_be_same(down_64(0, 0), u64(0));
    shall_be_same(down_64(1, 0), u64(1));

    shall_be_same(down_64(0, 1), u64(0));
    shall_be_same(down_64(1, 1), u64(0));
    shall_be_same(down_64(2, 1), u64(2));
    shall_be_same(down_64(3, 1), u64(2));

    shall_be_same(down_64( 0, 2), u64(0));
    shall_be_same(down_64( 1, 2), u64(0));
    shall_be_same(down_64( 2, 2), u64(0));
    shall_be_same(down_64( 3, 2), u64(0));
    shall_be_same(down_64( 4, 2), u64(4));
    shall_be_same(down_64( 5, 2), u64(4));
    shall_be_same(down_64( 6, 2), u64(4));
    shall_be_same(down_64( 7, 2), u64(4));
    shall_be_same(down_64( 8, 2), u64(8));
    shall_be_same(down_64( 9, 2), u64(8));
  }
  {
    shall_be_same(above_64( 0, 2), u64(0));
    shall_be_same(above_64( 1, 2), u64(1));
    shall_be_same(above_64( 2, 2), u64(2));
    shall_be_same(above_64( 3, 2), u64(3));
    shall_be_same(above_64( 4, 2), u64(0));
    shall_be_same(above_64( 5, 2), u64(1));
    shall_be_same(above_64( 6, 2), u64(2));
    shall_be_same(above_64( 7, 2), u64(3));
    shall_be_same(above_64( 8, 2), u64(0));
    shall_be_same(above_64( 9, 2), u64(1));
  }
  {
    shall_be_same(up_64( 0, 2), u64( 0));
    shall_be_same(up_64( 1, 2), u64( 4));
    shall_be_same(up_64( 2, 2), u64( 4));
    shall_be_same(up_64( 3, 2), u64( 4));
    shall_be_same(up_64( 4, 2), u64( 4));
    shall_be_same(up_64( 5, 2), u64( 8));
    shall_be_same(up_64( 6, 2), u64( 8));
    shall_be_same(up_64( 7, 2), u64( 8));
    shall_be_same(up_64( 8, 2), u64( 8));
    shall_be_same(up_64( 9, 2), u64(12));
  }
  {
    shall_be_same(below_64( 0, 2), u64(0));
    shall_be_same(below_64( 1, 2), u64(3));
    shall_be_same(below_64( 2, 2), u64(2));
    shall_be_same(below_64( 3, 2), u64(1));
    shall_be_same(below_64( 4, 2), u64(0));
    shall_be_same(below_64( 5, 2), u64(3));
    shall_be_same(below_64( 6, 2), u64(2));
    shall_be_same(below_64( 7, 2), u64(1));
    shall_be_same(below_64( 8, 2), u64(0));
    shall_be_same(below_64( 9, 2), u64(3));
  }
}
