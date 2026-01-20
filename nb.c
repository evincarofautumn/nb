#include <assert.h>
#include <inttypes.h>
#include <iso646.h>
#include <stdarg.h>
//#include <stdbit.h>
#include <stdbool.h>
//#include <stdcountof.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mach-o/fat.h>
#include <mach-o/loader.h>
#include <mach/vm_page_size.h>

static_assert(CHAR_BIT == 8);
static_assert(sizeof(size_t) == 8);

#define countof(a)                                              \
  (sizeof (a) / sizeof ((a)[0]))

#define bitsof(a)                                               \
  (CHAR_BIT * sizeof(a))

#define cat_(a, b)                                              \
  a##b

#define cat2(a, b)                                              \
  cat_(a, b)

#define cat3(a, b, c)                                           \
  cat2(cat2(a, b), c)

#define of(a, b)                                                \
  cat3(a, _, b)

#define when(a, b)                                              \
  (not (a) or (b))

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

#define struct_type(name)                                       \
  new_type(struct, name)

#define union_type(name)                                        \
  new_type(union, name)

#define function_type(name, type, params)                       \
  typedef type name params;                                     \
  typedef name *name##RefVar;                                   \
  typedef name##RefVar const name##Ref

type_alias(ExitStatus, int);
type_alias(Argc, int);
type_alias(Argv, char **);

type_alias(Chr, char);

type_alias(Str, Chr *);

type_alias(U1    , unsigned _BitInt(  1));
type_alias(U8    , unsigned _BitInt(  8));
type_alias(U16   , unsigned _BitInt( 16));
type_alias(U24   , unsigned _BitInt( 24));
type_alias(U32   , unsigned _BitInt( 32));
type_alias(U64   , unsigned _BitInt( 64));
type_alias(U128  , unsigned _BitInt(128));

#define U1(n)    ((U1Var)(n))
#define U8(n)    ((U8Var)(n))
#define U16(n)   ((U16Var)(n))
#define U24(n)   ((U24Var)(n))
#define U32(n)   ((U32Var)(n))
#define U64(n)   ((U64Var)(n))
#define U128(n)  ((U128Var)(n))

#define u(n)       (n##uwb)
#define u1(n)      (U1(u(n)))
#define u8(n)      (U8(u(n)))
#define u16(n)     (U16(u(n)))
#define u24(n)     (U24(u(n)))
#define u32(n)     (U32(u(n)))
#define u64(n)     (U64(u(n)))
#define u128(h,l)  (U128(h) << 10'0 | U128(l))

// Number of elements, length, cardinality.
type_alias(Count, size_t);

// Zero-based index, position.
type_alias(Idx, size_t);

#define IdxFmt "z"

// Memory size, count of bytes.
type_alias(Size, size_t);

type_alias(Bool, bool);

[[maybe_unused]]
static inline U32 l32(U32 i) {
  return 0
    | ((i & u32(0x000000FF)) << 03'0)
    | ((i & u32(0x0000FF00)) << 01'0)
    | ((i & u32(0x00FF0000)) >> 01'0)
    | ((i & u32(0xFF000000)) >> 03'0);
}

static U8Var reow[33432];

[[maybe_unused]]
static inline U32 rl32(U8Ref there) {
  return
    ( U32(there[0]) << 00'0
    | U32(there[1]) << 01'0
    | U32(there[2]) << 02'0
    | U32(there[3]) << 03'0
    );
}

[[maybe_unused]]
static inline U64 rl64(U8Ref there) {
  return
    ( U64(there[0]) << 00'0
    | U64(there[1]) << 01'0
    | U64(there[2]) << 02'0
    | U64(there[3]) << 03'0
    | U64(there[4]) << 04'0
    | U64(there[5]) << 05'0
    | U64(there[6]) << 06'0
    | U64(there[7]) << 07'0
    );
}

struct_type(Buf);

struct Buf {
  U8VarRefVar in;
  SizeVar at;
  SizeVar end;
};

[[maybe_unused]]
static inline void buf_skip(BufVarRef buf, Size by) {
  assert(by < buf->end);
  assert(buf->at < buf->end - by);
  fprintf(
    stderr,
    "skip from %0.8zX (%zu) to %0.8zX (%zu)\n",
    buf->at, buf->at,
    buf->at + by, buf->at + by
  );
  buf->at += +by;
}

[[maybe_unused]]
static inline void buf_out_u8(BufVarRef buf, U8 i) {
  assert(buf->at < buf->end - sizeof i);
  U8VarRef here = &buf->in[buf->at];
  here[0] = i;
  buf->at += +sizeof i;
}

[[maybe_unused]]
static inline void buf_out_u32(BufVarRef buf, U32 i) {
  if (not (buf->at <= buf->end - sizeof i)) {
    fprintf(
      stderr,
      "not ((buf->at = %zu) <= (%zu = buf->end) - (sizeof i = %zu))\n",
      buf->at,
      buf->end,
      sizeof i
    );
    abort();
  }
  U8VarRef here = &buf->in[buf->at];
  here[0] = (i & u32(0x000000FF)) >> 00'0;
  here[1] = (i & u32(0x0000FF00)) >> 01'0;
  here[2] = (i & u32(0x00FF0000)) >> 02'0;
  here[3] = (i & u32(0xFF000000)) >> 03'0;
  buf->at += +sizeof i;
}

[[maybe_unused]]
static inline void buf_out_u64(BufVarRef buf, U64 i) {
  assert(buf->at < buf->end - sizeof i);
  U8VarRef here = &buf->in[buf->at];
  here[0] = (i & u64(0x00000000'000000FF)) >> 00'0;
  here[1] = (i & u64(0x00000000'0000FF00)) >> 01'0;
  here[2] = (i & u64(0x00000000'00FF0000)) >> 02'0;
  here[3] = (i & u64(0x00000000'FF000000)) >> 03'0;
  here[4] = (i & u64(0x000000FF'00000000)) >> 04'0;
  here[5] = (i & u64(0x0000FF00'00000000)) >> 05'0;
  here[6] = (i & u64(0x00FF0000'00000000)) >> 06'0;
  here[7] = (i & u64(0xFF000000'00000000)) >> 07'0;
  buf->at += +sizeof i;
}

union_type(V16U8);

union V16U8 {
  U8 vec[16];
  unsigned char str[16];
};

[[maybe_unused]]
static inline void buf_out_v16u8(BufVarRef buf, V16U8 v) {
  static_assert(sizeof v.vec == 16);
  assert(buf->at < buf->end - sizeof v.vec);
  U8VarRef here = &buf->in[buf->at];
  memcpy((void *)&here[0], (void *)&v.vec[0], sizeof v.vec);
  buf->at += +sizeof v.vec;
}

#define out_u8(x) buf_out_u8(&BUF, x)
#define out_u32(x) buf_out_u32(&BUF, x)
#define out_u64(x) buf_out_u64(&BUF, x)
#define out_v16u8(x) buf_out_v16u8(&BUF, x)

#define till(to)                                                \
  while ((BUF.at % (to)) != (Size)0)

type_alias(Line, typeof(__LINE__));

#define LineFmt "d"

#define tell(file, line, tag, fmt, ...)                         \
  (void)fprintf(                                                \
    stderr,                                                     \
    "%s: "                                                      \
    "%s:"                                                       \
    "%"LineFmt": "                                              \
    "%s: "                                                      \
    fmt"\n",                                                    \
    "nb",                                                       \
    file,                                                       \
    line,                                                       \
    tag __VA_OPT__(,)                                           \
    __VA_ARGS__                                                 \
  )

#define error(fmt, ...)                                         \
  tell(                                                         \
    __FILE__, __LINE__, "error",                                \
    fmt __VA_OPT__(,)                                           \
    __VA_ARGS__                                                 \
  )

#define warn(fmt, ...)                                          \
  tell(                                                         \
    __FILE__, __LINE__, "warning",                              \
    fmt __VA_OPT__(,)                                           \
    __VA_ARGS__                                                 \
  )

#define trace(fmt, ...)                                         \
  tell(                                                         \
    __FILE__, __LINE__, "trace",                                \
    fmt __VA_OPT__(,)                                           \
    __VA_ARGS__                                                 \
  )

#define not_same(fmtx, fmtd)                                    \
  "((%s) = %"fmtx" (%"fmtd"))"                                  \
  " != "                                                        \
  "((%s) = %"fmtx" (%"fmtd"))"

#define must_be_same(a, b)                                      \
  _Generic((a),                                                 \
           U64Var: ((a) == (b) ? (a) : (error(not_same("0.16"PRIX64, PRId64), #a, (uint64_t)(a), (uint64_t)(a), #b, (uint64_t)(b), (uint64_t)(b)), (b))), \
           U32Var: ((a) == (b) ? (a) : (error(not_same( "0.8"PRIX32, PRId32), #a, (uint32_t)(a), (uint32_t)(a), #b, (uint32_t)(b), (uint32_t)(b)), (b))))

#define should_be_same(a, b)                                    \
  _Generic((a),                                                 \
           U64Var: ((a) == (b) ? (a) : ( warn(not_same("0.16"PRIX64, PRId64), #a, (uint64_t)(a), (uint64_t)(a), #b, (uint64_t)(b), (uint64_t)(b)), (b))), \
           U32Var: ((a) == (b) ? (a) : ( warn(not_same( "0.8"PRIX32, PRId32), #a, (uint32_t)(a), (uint32_t)(a), #b, (uint32_t)(b), (uint32_t)(b)), (b))))

#define eval_(x)                                                \
  x

#define eval(x)                                                 \
  eval_(x)

struct_type(Task);

function_type(Beg,     Bool, (TaskVarRef task));
function_type(BegElt,  Bool, (TaskVarRef task, Str tag));
function_type(EndElt,  Bool, (TaskVarRef task, Str tag));
function_type(End,     Bool, (TaskVarRef task));

struct Task {
  BegRefVar     beg;
  BegEltRefVar  beg_elt;
  EndEltRefVar  end_elt;
  EndRefVar     end;
};

static inline Bool work_beg       (TaskVarRef task)           { return when(task->beg      != nullptr, task->beg       (task)       ); }
static inline Bool work_beg_elt   (TaskVarRef task, Str tag)  { return when(task->beg_elt  != nullptr, task->beg_elt   (task, tag)  ); }
static inline Bool work_end_elt   (TaskVarRef task, Str tag)  { return when(task->end_elt  != nullptr, task->end_elt   (task, tag)  ); }
static inline Bool work_end       (TaskVarRef task)           { return when(task->end      != nullptr, task->end       (task)       ); }

Bool work(TaskVarRef task) {
  return
    work_beg      (task          )  and
    work_beg_elt  (task, "taga"  )  and
    work_beg_elt  (task, "tagb"  )  and
    work_end_elt  (task, "tagb"  )  and
    work_end_elt  (task, "taga"  )  and
    work_end      (task          )  and
    true;
}

////////////////////////////////////////////////////////////////

struct_type(CountEltsTask);

struct CountEltsTask {
  Task task;
  SizeVar begs;
  SizeVar depth;
  SizeVar ends;
};

static inline Bool count_elts_beg_elt(
  TaskVarRef task,
  Str tag
) {
  assert(task != nullptr);
  CountEltsTaskVarRef self = (CountEltsTaskVarRef)task;
  assert(self->begs < SIZE_MAX);
  assert(self->depth < SIZE_MAX);
  return
    ++self->begs,
    ++self->depth,
    true;
}

static inline Bool count_elts_end_elt(
  TaskVarRef task,
  Str tag
) {
  assert(task != nullptr);
  CountEltsTaskVarRef self = (CountEltsTaskVarRef)task;
  assert(self->ends < SIZE_MAX);
  return
    self->depth > 0 ? (
      ++self->ends,
      --self->depth,
      true
    ) :
    (
      error(
        "missing begin tag; name: %s, begs: %zu, ends: %zu, depth: %zu",
        tag,
        self->begs,
        self->ends,
        self->depth
      ),
      false
    );
}

static inline Bool count_elts_end(
  TaskVarRef task
) {
  assert(task != nullptr);
  CountEltsTaskVarRef self = (CountEltsTaskVarRef)task;
  return
    self->depth == 0 and
    self->begs == self->ends or
    (
      error(
        "missing end tag; begs: %zu, ends: %zu, depth: %zu",
        self->begs,
        self->ends,
        self->depth
      ),
      false
    );
}

////////////////////////////////////////////////////////////////

static constexpr SizeVar tag_alignment = 2;

static_assert(1 << tag_alignment == sizeof(U32));

struct_type(CountTagSizeTask);

struct CountTagSizeTask {
  Task task;
  SizeVar size;
  SizeVar null;
  SizeVar padding;
};

[[maybe_unused]]
static Chr NUL = '\0';

// A mask with the nth bit set, equal to 2^n.
static inline U64 bit_64(U64 n) {
  assert(n < bitsof(U64));
  return u64(1) << n;
}

// A mask of all zeros.
static U64 zeros_64 = u64(0);

// A mask of all ones.
static U64 ones_64 = compl zeros_64;

// A 64-bit mask with the n bits in the range [(n - 1) : 0] set.
static inline U64 mask_64(U64 n) {
  assert(n <= bitsof(U64));
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
  assert(n <= UINT64_MAX - mask_64(x));
  return down_64(mask_64(x) + n, x);
}

// Gets how far n is below the next tab stop of size 2^x,
// in the range [0 : ((2^x)-1)].
static inline U64 below_64(U64 n, U64 x) {
  return mask_64(x) - above_64(n - 1, x);
}

static inline Bool count_tag_size_beg_elt(
  TaskVarRef task,
  Str tag
) {
  assert(task != nullptr);
  CountTagSizeTaskVarRef self = (CountTagSizeTaskVarRef)task;
  assert(
    (self->size + self->null + self->padding)
    % (1 << tag_alignment)
    == 0
  );
  Size size = strlen(tag);
  assert(self->size <= SIZE_MAX - size);
  assert(self->null <= SIZE_MAX - sizeof NUL);
  Size padding = below_64(size + sizeof NUL, tag_alignment);
  self->size += size;
  self->null += sizeof NUL;
  self->padding += padding;
  return true;
}

////////////////////////////////////////////////////////////////

struct_type(TagCount);

struct TagCount {
  StrVar tag;
  CountVar count;
};

struct_type(CountTagsTask);

struct CountTagsTask {
  Task task;
  TagCountVarRefVar set;
  CountVar count;
  CountVar end;
};

static inline Bool count_tags_beg_elt(
  TaskVarRef task,
  Str tag
) {
  assert(task != nullptr);
  assert(tag != nullptr);
  CountTagsTaskVarRef self = (CountTagsTaskVarRef)task;
  assert(self->count <= self->end);
  for (IdxVar i = 0; i < self->count; ++i) {
    if (strcmp(self->set[i].tag, tag) == 0) {
      ++self->set[i].count;
      return true;
    }
  }
  assert(self->count < self->end);
  self->set[self->count].tag = tag;
  self->set[self->count].count = 1;
  ++self->count;
  return true;
}

////////////////////////////////////////////////////////////////

Bool nb() {

  CountEltsTaskVar count_elts = (CountEltsTaskVar){
    .task = (Task){
      .beg_elt  = count_elts_beg_elt  ,
      .end_elt  = count_elts_end_elt  ,
      .end      = count_elts_end      ,
    },
    .begs   = 0,
    .depth  = 0,
    .ends   = 0,
  };
  if (not work((TaskVarRef)&count_elts)) return false;
  trace("counted %zu total elements", count_elts.ends);

  CountTagSizeTaskVar count_tag_size = (CountTagSizeTaskVar){
    .task = (Task){
      .beg_elt = count_tag_size_beg_elt,
    },
    .size = 0,
    .null = 0,
    .padding = 0,
  };
  if (not work((TaskVarRef)&count_tag_size)) return false;
  trace("counted %zu tag bytes", count_tag_size.size);
  trace("counted %zu NUL bytes", count_tag_size.null);
  trace("counted %zu pad bytes", count_tag_size.padding);
  Size tag_size
    = count_tag_size.size
    + count_tag_size.null
    + count_tag_size.padding;
  trace("counted %zu total bytes", tag_size);

  CountTagsTaskVar count_tags = (CountTagsTaskVar){
    .task = (Task){
      .beg_elt = count_tags_beg_elt,
    },
    .set = calloc(count_elts.ends, sizeof count_tags.set[0]),
    .count = 0,
    .end = count_elts.ends,
  };
  assert(count_tags.set != nullptr);
  if (not work((TaskVarRef)&count_tags)) return false;
  trace("counted %zu unique tags", count_tags.count);

  free(count_tags.set);

  return true;

}

////////////////////////////////////////////////////////////////

static void test(void) {
  {
    must_be_same(bit_64(0), u64(0b0001));
    must_be_same(bit_64(1), u64(0b0010));
    must_be_same(bit_64(2), u64(0b0100));
    must_be_same(bit_64(3), u64(0b1000));

    must_be_same(bit_64(31), u64(0x00000000'80000000));
    must_be_same(bit_64(32), u64(0x00000001'00000000));

    must_be_same(bit_64(60), u64(0x10000000'00000000));
    must_be_same(bit_64(61), u64(0x20000000'00000000));
    must_be_same(bit_64(62), u64(0x40000000'00000000));
    must_be_same(bit_64(63), u64(0x80000000'00000000));
  }
  {
    must_be_same(mask_64(0), u64(0x0));
    must_be_same(mask_64(1), u64(0x1));
    must_be_same(mask_64(2), u64(0x3));
    must_be_same(mask_64(3), u64(0x7));

    must_be_same(mask_64(32), u64(0x00000000'FFFFFFFF));

    must_be_same(mask_64(61), u64(0x1FFFFFFF'FFFFFFFF));
    must_be_same(mask_64(62), u64(0x3FFFFFFF'FFFFFFFF));
    must_be_same(mask_64(63), u64(0x7FFFFFFF'FFFFFFFF));
    must_be_same(mask_64(64), u64(0xFFFFFFFF'FFFFFFFF));
  }
  {
    must_be_same(down_64(0, 0), u64(0));
    must_be_same(down_64(1, 0), u64(1));

    must_be_same(down_64(0, 1), u64(0));
    must_be_same(down_64(1, 1), u64(0));
    must_be_same(down_64(2, 1), u64(2));
    must_be_same(down_64(3, 1), u64(2));

    must_be_same(down_64( 0, 2), u64(0));
    must_be_same(down_64( 1, 2), u64(0));
    must_be_same(down_64( 2, 2), u64(0));
    must_be_same(down_64( 3, 2), u64(0));
    must_be_same(down_64( 4, 2), u64(4));
    must_be_same(down_64( 5, 2), u64(4));
    must_be_same(down_64( 6, 2), u64(4));
    must_be_same(down_64( 7, 2), u64(4));
    must_be_same(down_64( 8, 2), u64(8));
    must_be_same(down_64( 9, 2), u64(8));
  }
  {
    must_be_same(above_64( 0, 2), u64(0));
    must_be_same(above_64( 1, 2), u64(1));
    must_be_same(above_64( 2, 2), u64(2));
    must_be_same(above_64( 3, 2), u64(3));
    must_be_same(above_64( 4, 2), u64(0));
    must_be_same(above_64( 5, 2), u64(1));
    must_be_same(above_64( 6, 2), u64(2));
    must_be_same(above_64( 7, 2), u64(3));
    must_be_same(above_64( 8, 2), u64(0));
    must_be_same(above_64( 9, 2), u64(1));
  }
  {
    must_be_same(up_64( 0, 2), u64( 0));
    must_be_same(up_64( 1, 2), u64( 4));
    must_be_same(up_64( 2, 2), u64( 4));
    must_be_same(up_64( 3, 2), u64( 4));
    must_be_same(up_64( 4, 2), u64( 4));
    must_be_same(up_64( 5, 2), u64( 8));
    must_be_same(up_64( 6, 2), u64( 8));
    must_be_same(up_64( 7, 2), u64( 8));
    must_be_same(up_64( 8, 2), u64( 8));
    must_be_same(up_64( 9, 2), u64(12));
  }
  {
    must_be_same(below_64( 0, 2), u64(0));
    must_be_same(below_64( 1, 2), u64(3));
    must_be_same(below_64( 2, 2), u64(2));
    must_be_same(below_64( 3, 2), u64(1));
    must_be_same(below_64( 4, 2), u64(0));
    must_be_same(below_64( 5, 2), u64(3));
    must_be_same(below_64( 6, 2), u64(2));
    must_be_same(below_64( 7, 2), u64(1));
    must_be_same(below_64( 8, 2), u64(0));
    must_be_same(below_64( 9, 2), u64(3));
  }
}

////////////////////////////////////////////////////////////////

ExitStatusVar
main(
  Argc argc,
  Argv argv
) {
  assert(argc == 2);
  assert(argv);

  test();
  Bool okay = nb();
  if (not okay) {
    error("failed");
    return EXIT_FAILURE;
  }

  FILE *o = fopen(argv[1], "wb");
  assert(o);

  static_assert(countof(reow) == sizeof(reow));
  BufVar BUF = (Buf){
    .in = &reow[0],
    .at = 0,
    .end = countof(reow)
  };

#define declare_field(name, count, sub)                         \
  [[maybe_unused]]                                              \
  IdxVar of(name, sub)[count] = {}

#define declare_struct(name, count)                             \
  declare_field(name, count, beg);                              \
  declare_field(name, count, end);

#define def(name, idx, sub)                                  \
  [[maybe_unused]]                                              \
  of(name, of(sub, idx)):                                       \
    fprintf(                                                    \
      stderr,                                                   \
      "%s_%s[%"IdxFmt"u] = %0.8"IdxFmt"X (%"IdxFmt"u)\n",       \
      #name,                                                    \
      #sub,                                                     \
      (Idx)idx,                                                 \
      (Idx)BUF.at,                                              \
      (Idx)BUF.at                                               \
    );                                                          \
  of(name, sub)[idx] = BUF.at;

#define beg(name, idx)                                        \
  def(name, idx, beg)

#define end(name, idx)                                          \
  def(name, idx, end)

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

  beg(file, 0);

  //  fill with sentinel bytes
  //  memset((void *)file_beg[0], 0xBA, sizeof reow);

  Bool fat_binary_enabled = false;

  if (fat_binary_enabled) {

    beg(fat_binary, 0);

    beg(fat_header, 0);
    def(fat_header, 0, magic);
    out_u32(must_be_same(u32(0xCAFEBABE), U32(FAT_MAGIC)));
    def(fat_header, 0, nfat_arch);
    out_u32(u32(1));
    end(fat_header, 0);

    beg(fat_arch, 0);

    def(fat_arch, 0, cputype);
    out_u32(must_be_same(u32(0x0100000C), U32(CPU_TYPE_ARM64)));

    def(fat_arch, 0, cpusubtype);
    out_u32(must_be_same(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL)));

    def(fat_arch, 0, offset);
    // TODO
    out_u32(should_be_same(u32(0xBABABABA), U32(mach_object_beg[0] - file_beg[0])));

    def(fat_arch, 0, size);
    // TODO: size
    out_u32(should_be_same(u32(0xBABABABA), U32(file_end[0] - file_beg[0])));

    def(fat_arch, 0, align);
    // mach/vm_page_size.h:vm_page_shift
    out_u32(must_be_same(must_be_same(u32(14), U32(vm_page_shift)), U32(PAGE_SHIFT)));

    def(fat_arch, 0, reserved);
    out_u32(u32(0x00000000));

    end(fat_arch, 0);

    // pad up to PAGE_SIZE with u8(0x00)
    // mach/vm_page_size.h:vm_page_size
    till(must_be_same(must_be_same(u32(0x4000), U32(vm_page_size)), U32(PAGE_SIZE))) {
      out_u8(u8(0x00));
    }

  }

  beg(mach_object, 0);
  beg(mach_header_64, 0);

  def(mach_header_64, 0, magic);
  out_u32(must_be_same(u32(0xFEEDFACF), MH_MAGIC_64));

  def(mach_header_64, 0, cputype);
  U32 CPU_TYPE_MASK = compl U32(CPU_ARCH_MASK);
  out_u32(must_be_same(
    u32(0x0100000C),
    must_be_same(
      U32(CPU_TYPE_ARM64),
      ( ( U32(must_be_same(u32(0x01000000), U32(CPU_ARCH_ABI64)))
        & must_be_same(u32(0xFF000000), U32(CPU_ARCH_MASK))
        )
      | ( must_be_same(U32(u24(12)), U32(CPU_TYPE_ARM))
        & must_be_same(u32(0x00FFFFFF), U32(CPU_TYPE_MASK))
        )
      )
    )
  ));

  def(mach_header_64, 0, cpusubtype);
  out_u32(must_be_same(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL)));

  def(mach_header_64, 0, filetype);
  out_u32(must_be_same(u32(0x00000002), U32(MH_EXECUTE)));

  def(mach_header_64, 0, ncmds);
  out_u32(must_be_same(u32(0x00000011), u32(17)));

  def(mach_header_64, 0, sizeofcmds);
  out_u32(must_be_same(u32(0x00000420), u32(1056)));

  def(mach_header_64, 0, flags);
  out_u32(must_be_same(
    u32(0x00200085),
    ( must_be_same(must_be_same(u32(0x00200000), U32(MH_PIE)     ), u32(1) << 02'5)
    | must_be_same(must_be_same(u32(0x00000080), U32(MH_TWOLEVEL)), u32(1) << 00'7)
    | must_be_same(must_be_same(u32(0x00000004), U32(MH_DYLDLINK)), u32(1) << 00'2)
    | must_be_same(must_be_same(u32(0x00000001), U32(MH_NOUNDEFS)), u32(1) << 00'0)
    )
  ));

  def(mach_header_64, 0, reserved);
  out_u32(u32(0x00000000));

  end(mach_header_64, 0);

  // TODO: on set load_commands_end: assert: sizeofcmds  = load_commands_end - load_commands_beg

  beg(load_commands, 0);

  // command 1
  beg(segment_command_64, 0);

  def(segment_command_64, 0, cmd);
  out_u32(must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));

  def(segment_command_64, 0, cmdsize);
  out_u32(u32(0x00000048));

  def(segment_command_64, 0, segname);
  out_v16u8((V16U8){.str = u8"__PAGEZERO"});

  def(segment_command_64, 0, vmaddr);
  out_u64(u64(0x00000000'00000000));

  def(segment_command_64, 0, vmsize);
  out_u64(u64(0x00000001'00000000));

  def(segment_command_64, 0, fileoff);
  out_u64(u64(0x00000000'00000000));

  def(segment_command_64, 0, filesize);
  out_u64(u64(0x00000000'00000000));

  def(segment_command_64, 0, maxprot);
  out_u32(u32(0x00000000));

  def(segment_command_64, 0, initprot);
  out_u32(u32(0x00000000));

  def(segment_command_64, 0, nsects);
  out_u32(u32(0x00000000));

  def(segment_command_64, 0, flags);
  out_u32(u32(0x00000000));

  end(segment_command_64, 0);

  // command 2
  beg(segment_command_64, 1);

  def(segment_command_64, 1, cmd);
  out_u32(must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));

  def(segment_command_64, 1, cmdsize);
  out_u32(u32(0x00000188));

  def(segment_command_64, 1, segname);
  //ol128(u128(u64(0x45545F5F'00005458), u64(0x00000000'00000000)));
  out_v16u8((V16U8){.str = u8"__TEXT"});

  def(segment_command_64, 1, vmaddr);
  out_u64(u64(0x00000001'00000000));

  def(segment_command_64, 1, vmsize);
  out_u64(u64(0x00000000'00004000));

  def(segment_command_64, 1, fileoff);
  out_u64(u64(0x00000000'00000000));

  def(segment_command_64, 1, filesize);
  out_u64(u64(0x00000000'00004000));

  def(segment_command_64, 1, maxprot);
  out_u32(u32(0x00000005));

  def(segment_command_64, 1, initprot);
  out_u32(u32(0x00000005));

  def(segment_command_64, 1, nsects);
  out_u32(u32(0x00000004));

  def(segment_command_64, 1, flags);
  out_u32(u32(0x00000000));

  beg(section_64, 0);

  def(section_64, 0, sectname);
  out_v16u8((V16U8){.str = u8"__text"});
  def(section_64, 0, segname);
  out_v16u8((V16U8){.str = u8"__TEXT"});
  def(section_64, 0, addr);
  out_u64(u64(0x00000001'00000460));
  def(section_64, 0, size);
  out_u64(u64(0x00000000'0000003c));
  def(section_64, 0, offset);
  out_u32(u32(0x00000460));
  def(section_64, 0, align);
  out_u32(u32(0x00000002));

  def(section_64, 0, reloff);
  out_u32(u32(0x00000000));
  def(section_64, 0, nreloc);
  out_u32(u32(0x00000000));

  def(section_64, 0, flags);
  out_u32(must_be_same(
    u32(0x80000400),
    ( ( must_be_same(u32(0x000000FF), U32(SECTION_TYPE))
      & must_be_same(u32(0x00000000), U32(S_REGULAR))
      )
    | ( must_be_same(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
      & ( must_be_same(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
        | must_be_same(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
        )
      )
    )
  ));

  def(section_64, 0, reserved1);
  out_u32(u32(0x00000000));
  def(section_64, 0, reserved2);
  out_u32(u32(0x00000000));
  def(section_64, 0, reserved3);
  out_u32(u32(0x00000000));

  end(section_64, 0);

  beg(section_64, 1);

  def(section_64, 1, sectname);
  out_v16u8((V16U8){.str = u8"__stubs"});
  def(section_64, 1, segname);
  out_v16u8((V16U8){.str = u8"__TEXT"});
  def(section_64, 1, addr);
  out_u64(u64(0x00000001'0000049c));
  def(section_64, 1, size);
  out_u64(u64(0x00000000'0000000c));
  def(section_64, 1, offset);
  out_u32(u32(0x0000049c));
  def(section_64, 1, align);
  out_u32(u32(0x00000002));

  def(section_64, 1, reloff);
  out_u32(u32(0x00000000));
  def(section_64, 1, nreloc);
  out_u32(u32(0x00000000));

  def(section_64, 1, flags);
  out_u32(must_be_same(
    u32(0x80000408),
    ( ( must_be_same(u32(0x000000FF), U32(SECTION_TYPE))
      & must_be_same(u32(0x00000008), U32(S_SYMBOL_STUBS))
      )
    | ( must_be_same(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
      & ( must_be_same(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
        | must_be_same(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
        )
      )
    )
  ));
  def(section_64, 1, reserved1);
  out_u32(u32(0x00000000));
  def(section_64, 1, reserved2);
  def(section_64, 1, stub_size);
  out_u32(u32(0x0000000c));
  def(section_64, 1, reserved3);
  out_u32(u32(0x00000000));

  end(section_64, 1);

  beg(section_64, 2);

  out_v16u8((V16U8){.str = u8"__cstring"});
  out_v16u8((V16U8){.str = u8"__TEXT"});
  out_u64(u64(0x00000001'000004a8));
  out_u64(u64(0x00000000'00000005));
  out_u32(u32(0x000004a8));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  end(section_64, 2);

  beg(section_64, 3);

  out_v16u8((V16U8){.str = u8"__unwind_info"});
  out_v16u8((V16U8){.str = u8"__TEXT"});
  out_u64(u64(0x00000001'000004b0));
  out_u64(u64(0x00000000'00000058));
  out_u32(u32(0x000004b0));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  end(section_64, 3);

  end(segment_command_64, 1);

  // command 3
  beg(segment_command_64, 2);

  out_u32(must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));
  out_u32(u32(0x00000098));
  out_v16u8((V16U8){.str = u8"__DATA_CONST"});
  out_u64(u64(0x00000001'00004000));
  out_u64(u64(0x00000000'00004000));
  out_u64(u64(0x00000000'00004000));
  out_u64(u64(0x00000000'00004000));
  out_u32(u32(0x00000003));
  out_u32(u32(0x00000003));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000010));

  out_v16u8((V16U8){.str = u8"__got"});
  out_v16u8((V16U8){.str = u8"__DATA_CONST"});
  out_u64(u64(0x00000001'00004000));
  out_u64(u64(0x00000000'00000008));
  out_u32(u32(0x00004000));
  out_u32(u32(0x00000003));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000006));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  end(segment_command_64, 2);

  // command 4
  beg(segment_command_64, 3);

  out_u32(must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));
  out_u32(u32(0x00000048));
  out_v16u8((V16U8){.str = u8"__LINKEDIT"});
  out_u64(u64(0x00000001'00008000));
  out_u64(u64(0x00000000'00004000));
  out_u64(u64(0x00000000'00008000));
  out_u64(u64(0x00000000'00000298));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000001));
  out_u64(u64(0x00000000));
  out_u32(u32(0x80000034));

  end(segment_command_64, 3);

  // command 5
  beg(prebound_dylib_command, 0);

  def(prebound_dylib_command, 0, cmd);
  out_u32(must_be_same(u32(0x00000010), U32(LC_PREBOUND_DYLIB)));
  def(prebound_dylib_command, 0, cmdsize);
  out_u32(u32(0x00008000));
  def(prebound_dylib_command, 0, name);
  out_u32(u32(0x00000060));
  def(prebound_dylib_command, 0, nmodules);
  out_u32(u32(0x80000033));
  def(prebound_dylib_command, 0, linked_modules);
  out_u32(u32(0x00000010));

  end(prebound_dylib_command, 0);

  end(load_commands, 0);

  out_u32(u32(0x00008060));
  out_u32(u32(0x00000030));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000018));

  out_u32(u32(0x00008098));
  out_u32(u32(0x00000003));

  out_u32(u32(0x000080d0));
  out_u32(u32(0x00000028));
  out_u32(u32(0x0000000b));
  out_u32(u32(0x00000050));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  out_u32(u32(0x000080c8));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000000e));
  out_u32(u32(0x00000020));
  out_u32(u32(0x0000000c));

  // "/usr/lib/dyld"
  out_u32(u32(0x7273752f));
  out_u32(u32(0x62696c2f));
  out_u32(u32(0x6c79642f));

  out_u32(u32(0x00000064));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000001b));
  out_u32(u32(0x00000018));

  out_u32(u32(0xfd260cec));
  out_u32(u32(0x253118de));
  out_u32(u32(0x528214bb));
  out_u32(u32(0xd9594302));
  out_u32(u32(0x00000032));
  out_u32(u32(0x00000020));
  out_u32(u32(0x00000001));
  out_u32(u32(0x000f0000));
  out_u32(u32(0x000f0500));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000003));
  out_u32(u32(0x048f0500));
  out_u32(u32(0x0000002a));
  out_u32(u32(0x00000010));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x80000028));

  out_u32(u32(0x00000018));
  out_u32(u32(0x00000460));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000000c));
  out_u32(u32(0x00000038));
  out_u32(u32(0x00000018));
  out_u32(u32(0x00000002));
  out_u32(u32(0x05470000));
  out_u32(u32(0x00010000));

  // "/usr/lib/libSystem.B.dylib"
  out_u32(u32(0x7273752f));
  out_u32(u32(0x62696c2f));
  out_u32(u32(0x62696c2f));
  out_u32(u32(0x74737953));
  out_u32(u32(0x422e6d65));
  out_u32(u32(0x6c79642e));
  out_u32(u32(0x00006269));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000026));
  out_u32(u32(0x00000010));

  out_u32(u32(0x00008090));
  out_u32(u32(0x00000008));
  out_u32(u32(0x00000029));
  out_u32(u32(0x00000010));

  out_u32(u32(0x00008098));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000001d));
  out_u32(u32(0x00000010));
  out_u32(u32(0x00008100));
  out_u32(u32(0x00000198));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0xd100c3ff));
  out_u32(u32(0xa9027bfd));
  out_u32(u32(0x910083fd));
  out_u32(u32(0x52800008));
  out_u32(u32(0xb9000fe8));
  out_u32(u32(0xb81fc3bf));
  out_u32(u32(0xb81f83a0));
  out_u32(u32(0xf9000be1));
  out_u32(u32(0x90000000));
  out_u32(u32(0x9112a000));
  out_u32(u32(0x94000005));
  out_u32(u32(0xb9400fe0));
  out_u32(u32(0xa9427bfd));
  out_u32(u32(0x9100c3ff));
  out_u32(u32(0xd65f03c0));
  out_u32(u32(0x90000030));
  out_u32(u32(0xf9400210));
  out_u32(u32(0xd61f0200));

  // "reow"
  out_u32(u32(0x776f6572));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000001));
  out_u32(u32(0x0000001c));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000001c));
  out_u32(u32(0x00000000));
  out_u32(u32(0x0000001c));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000460));
  out_u32(u32(0x00000040));
  out_u32(u32(0x00000040));
  out_u32(u32(0x0000049c));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000040));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000003));
  out_u32(u32(0x0001000c));
  out_u32(u32(0x00010010));
  out_u32(u32(0x00000000));
  out_u32(u32(0x04000000));

  //  14 3/4 KiB of zeros
  buf_skip(&BUF, +0x3B00);

  out_u32(u32(0x80000000));

  buf_skip(&BUF, +0x3FFC);

  // 16 KiB of zeros

  out_u32(u32(0x00000020));
  out_u32(u32(0x00000050));
  out_u32(u32(0x00000054));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000004));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000018));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000018));
  out_u32(u32(0x00064000));
  out_u32(u32(0x00004000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000201));

  // "_puts"
  out_u32(u32(0x75705f00));
  out_u32(u32(0x00007374));

  out_u32(u32(0x00000000));

  // "_"
  out_u32(u32(0x005f0100));
  out_u32(u32(0x00000012));
  out_u32(u32(0x00000200));
  out_u32(u32(0xe0000300));
  out_u32(u32(0x02000008));

  // "_mh_execute_header"
  // "main"
  out_u32(u32(0x5f686d5f));
  out_u32(u32(0x63657865));
  out_u32(u32(0x5f657475));
  out_u32(u32(0x64616568));
  out_u32(u32(0x09007265));
  out_u32(u32(0x6e69616d));

  out_u32(u32(0x00000d00));
  out_u32(u32(0x000008e0));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000002));
  out_u32(u32(0x0010010f));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000001));
  out_u32(u32(0x00000016));
  out_u32(u32(0x0000010f));
  out_u32(u32(0x00000460));
  out_u32(u32(0x00000001));
  out_u32(u32(0x0000001c));
  out_u32(u32(0x01000001));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000002));
  out_u32(u32(0x00000002));

  // "__mh_execute_header"
  // "_main"
  // "_puts"
  out_u32(u32(0x5f5f0020));
  out_u32(u32(0x655f686d));
  out_u32(u32(0x75636578));
  out_u32(u32(0x685f6574));
  out_u32(u32(0x65646165));
  out_u32(u32(0x6d5f0072));
  out_u32(u32(0x006e6961));
  out_u32(u32(0x7475705f));
  out_u32(u32(0x00000073));

  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  out_u32(u32(0xc00cdefa));
  out_u32(u32(0x95010000));
  out_u32(u32(0x01000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x14000000));

  out_u32(u32(0x020cdefa));
  out_u32(u32(0x81010000));
  out_u32(u32(0x00040200));
  out_u32(u32(0x02000200));
  out_u32(u32(0x61000000));
  out_u32(u32(0x58000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x09000000));
  out_u32(u32(0x00810000));
  out_u32(u32(0x0c000220));

  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x00000000));

  out_u32(u32(0x3c000000));
  out_u32(u32(0x00000000));
  out_u32(u32(0x01000000));

  // "reow"
  out_u32(u32(0x776f6572));
  // ".bin"
  out_u32(u32(0x6e69622e));

  out_u32(u32(0xa3d84c00));
  out_u32(u32(0xf17b0c0b));
  out_u32(u32(0xed0e7b23));
  out_u32(u32(0xc02a8a13));
  out_u32(u32(0xfd8bf22a));
  out_u32(u32(0x5c0dea5d));
  out_u32(u32(0xa78ff427));
  out_u32(u32(0xc21f4fc1));
  out_u32(u32(0xac7fadf1));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xac7fada7));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xac7fada7));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xebd5dfa7));
  out_u32(u32(0x6695f186));
  out_u32(u32(0x062ca103));
  out_u32(u32(0x1f63f436));
  out_u32(u32(0x0b0df166));
  out_u32(u32(0xa3eed4b8));
  out_u32(u32(0xe0825bd2));
  out_u32(u32(0xb40292e5));
  out_u32(u32(0xac7faded));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xac7fada7));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xac7fada7));
  out_u32(u32(0xc66f58b2));
  out_u32(u32(0x04c066e9));
  out_u32(u32(0x6bd1d1d7));
  out_u32(u32(0x05584f02));
  out_u32(u32(0x7cb47cff));
  out_u32(u32(0xbdda857a));
  out_u32(u32(0x2c89488b));
  out_u32(u32(0xb72601a7));
  out_u32(u32(0x5edb6ef7));
  out_u32(u32(0x650adc99));
  out_u32(u32(0x98549d4b));
  out_u32(u32(0x5f8a3929));
  out_u32(u32(0x946de112));
  out_u32(u32(0x614d53eb));
  out_u32(u32(0x3f1ecea2));

  out_u32(u32(0x00000041));

  end(mach_object, 0);
  end(fat_binary, 0);
  end(file, 0);

  assert(BUF.at <= BUF.end);

  Size size = BUF.at;
  if (size != sizeof reow) warn(
    "final size %zu is less than wanted size %zu",
    size,
    sizeof reow
  );
  fwrite((void *)&reow[0], 1, size, o);
  fclose(o);
  return 0;
}
