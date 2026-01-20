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

#define eval_(x)                                                \
  x

#define eval(x)                                                 \
  eval_(x)

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

type_alias(Arg,   ChrRefVar);
type_alias(Args,  ArgRefVar);
type_alias(Str,   ChrRefVar);
type_alias(Tag,   ChrRefVar);

// Number of elements, length, cardinality.
type_alias(Num, size_t);

// Zero-based index, position.
type_alias(Idx, size_t);

#define IdxFmt "z"

// Memory size, number of bytes.
type_alias(Size, size_t);

type_alias(Bool, bool);


//  Sized types
////////////////////////////////////////////////////////////////

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

// You can have 128-bit values, but you can't write them!
#define u128(h,l)  (U128(h) << 10'0 | U128(l))


//  Output buffer, as long as we're generating static output
////////////////////////////////////////////////////////////////

static U8Var reow[33432];
static_assert(numof(reow) == sizeof(reow));


//  Messaging --- logging, warnings, errors
////////////////////////////////////////////////////////////////

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


//  Main entry point
////////////////////////////////////////////////////////////////

static Bool nb(
  [[maybe_unused]] Str pgm,
  Num arg_num,
  Args args
);

static void test(void);

ExitStatusVar
main(
  Argc argc,
  Argv argv
) {
  assert(argc >= 1);
  assert(argv != nullptr);
  test();
  Bool okay = nb(argv[0], (Num)(argc - 1), (ArgsVar)&argv[1]);
  if (not okay) {
    error("failed");
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}


//  Endiannes
////////////////////////////////////////////////////////////////

[[maybe_unused]]
static inline U32 l32(U32 i) {
  return 0
    | ((i & u32(0x000000FF)) << 03'0)
    | ((i & u32(0x0000FF00)) << 01'0)
    | ((i & u32(0x00FF0000)) >> 01'0)
    | ((i & u32(0xFF000000)) >> 03'0);
}

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


//  Buffers
////////////////////////////////////////////////////////////////

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
    error(
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

[[maybe_unused]]
static inline void buf_out_pad(BufVarRef buf, Size till) {
  trace(
    "pad from %0.8zX (%zu) till next multiple of %0.8zX (%zu)",
    buf->at, buf->at,
    till, till
  );
  assert(till >= 1);
  assert(till <= buf->end);
  // assert(buf->end % till == 0 or buf->at <= (buf->end + 1) / till);
  if (buf->at % till == 0) {
    trace("already aligned");
    return;
  }
  Size to = ((buf->at + till) / till) * till;
  assert(to <= buf->end);
  trace(
    "skip from %0.8zX (%zu) to %0.8zX (%zu)",
    buf->at, buf->at,
    to, to
  );
  buf->at = to;
}


//  Tasks
////////////////////////////////////////////////////////////////

struct_type(Task);

function_type(Beg       , Bool, (TaskVarRef task                 ));
function_type(BegElt    , Bool, (TaskVarRef task  , Str    tag   ));
function_type(Elt       , Bool, (TaskVarRef task  , Str    tag   ));
function_type(OutU32    , Bool, (TaskVarRef task  , U32    val   ));
function_type(OutU64    , Bool, (TaskVarRef task  , U64    val   ));
function_type(OutV16U8  , Bool, (TaskVarRef task  , V16U8  val   ));
function_type(OutPad    , Bool, (TaskVarRef task  , Size   size  ));
function_type(EndElt    , Bool, (TaskVarRef task  , Str    tag   ));
function_type(End       , Bool, (TaskVarRef task                 ));

struct Task {
  BegRefVar       beg        ;
  BegEltRefVar    beg_elt    ;
  EltRefVar       elt        ;
  OutU32RefVar    out_u32    ;
  OutU64RefVar    out_u64    ;
  OutV16U8RefVar  out_v16u8  ;
  OutPadRefVar    out_pad    ;
  EndEltRefVar    end_elt    ;
  EndRefVar       end        ;
};

static inline Bool task_beg       (TaskVarRef task              ) { return when(task->beg        != nullptr, task->beg        (task        )); }
static inline Bool task_beg_elt   (TaskVarRef task, Str   tag   ) { return when(task->beg_elt    != nullptr, task->beg_elt    (task, tag   )); }
static inline Bool task_elt       (TaskVarRef task, Str   tag   ) { return when(task->elt        != nullptr, task->elt        (task, tag   )); }
static inline Bool task_out_u32   (TaskVarRef task, U32   val   ) { return when(task->out_u32    != nullptr, task->out_u32    (task, val   )); }
static inline Bool task_out_u64   (TaskVarRef task, U64   val   ) { return when(task->out_u64    != nullptr, task->out_u64    (task, val   )); }
static inline Bool task_out_v16u8 (TaskVarRef task, V16U8 val   ) { return when(task->out_v16u8  != nullptr, task->out_v16u8  (task, val   )); }
static inline Bool task_out_pad   (TaskVarRef task, Size  size  ) { return when(task->out_pad    != nullptr, task->out_pad    (task, size  )); }
static inline Bool task_end_elt   (TaskVarRef task, Str   tag   ) { return when(task->end_elt    != nullptr, task->end_elt    (task, tag   )); }
static inline Bool task_end       (TaskVarRef task              ) { return when(task->end        != nullptr, task->end        (task        )); }


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

  ////////////////////////////////////////////////////////////////

  task_beg(task);

  task_beg_elt(task, "file"); // 0

  //  fill with sentinel bytes
  //  memset((void *)file_beg[0], 0xBA, sizeof reow);

  Bool fat_binary_enabled = false;

  if (fat_binary_enabled) {

    task_beg_elt(task, "fat_binary"); // 0

    task_beg_elt(task, "fat_header"); // 0
    task_elt(task, "magic"); // fat_header[0].magic
    task_out_u32(task, must_be_same(u32(0xCAFEBABE), U32(FAT_MAGIC)));
    task_elt(task, "nfat_arch"); // fat_header[0].nfat_arch
    task_out_u32(task, u32(1));
    task_end_elt(task, "fat_header"); // 0

    task_beg_elt(task, "fat_arch"); // 0

    task_elt(task, "cputype"); // fat_arch[0].cputype
    task_out_u32(task, must_be_same(u32(0x0100000C), U32(CPU_TYPE_ARM64)));

    task_elt(task, "cpusubtype"); // fat_arch[0].cpusubtype
    task_out_u32(task, must_be_same(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL)));

    task_elt(task, "offset"); // fat_arch[0].offset
    // TODO
    task_out_u32(task, should_be_same(u32(0xBABABABA), U32(mach_object_beg[0] - file_beg[0])));

    task_elt(task, "size"); // fat_arch[0].size
    // TODO: size
    task_out_u32(task, should_be_same(u32(0xBABABABA), U32(file_end[0] - file_beg[0])));

    task_elt(task, "align"); // fat_arch[0].align
    // mach/vm_page_size.h:vm_page_shift
    task_out_u32(task, must_be_same(must_be_same(u32(14), U32(vm_page_shift)), U32(PAGE_SHIFT)));

    task_elt(task, "reserved"); // fat_arch[0].reserved
    task_out_u32(task, u32(0x00000000));

    task_end_elt(task, "fat_arch"); // 0

    // pad up to PAGE_SIZE with u8(0x00)
    // mach/vm_page_size.h:vm_page_size

    task_out_pad(task, must_be_same(must_be_same(u32(0x4000), U32(vm_page_size)), U32(PAGE_SIZE)));

  }

  task_beg_elt(task, "mach_object"); // 0
  task_beg_elt(task, "mach_header_64"); // 0

  task_elt(task, "magic"); // mach_header_64[0].magic
  task_out_u32(task, must_be_same(u32(0xFEEDFACF), MH_MAGIC_64));

  task_elt(task, "cputype"); // mach_header_64[0].cputype
  U32 CPU_TYPE_MASK = compl U32(CPU_ARCH_MASK);
  task_out_u32(task, must_be_same(
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

  task_elt(task, "cpusubtype"); // mach_header_64[0].cpusubtype
  task_out_u32(task, must_be_same(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL)));

  task_elt(task, "filetype"); // mach_header_64[0].filetype
  task_out_u32(task, must_be_same(u32(0x00000002), U32(MH_EXECUTE)));

  task_elt(task, "ncmds"); // mach_header_64[0].ncmds
  task_out_u32(task, must_be_same(u32(0x00000011), u32(17)));

  task_elt(task, "sizeofcmds"); // mach_header_64[0].sizeofcmds
  task_out_u32(task, must_be_same(u32(0x00000420), u32(1056)));

  task_elt(task, "flags"); // mach_header_64[0].flags
  task_out_u32(task, must_be_same(
    u32(0x00200085),
    ( must_be_same(must_be_same(u32(0x00200000), U32(MH_PIE)     ), u32(1) << 02'5)
    | must_be_same(must_be_same(u32(0x00000080), U32(MH_TWOLEVEL)), u32(1) << 00'7)
    | must_be_same(must_be_same(u32(0x00000004), U32(MH_DYLDLINK)), u32(1) << 00'2)
    | must_be_same(must_be_same(u32(0x00000001), U32(MH_NOUNDEFS)), u32(1) << 00'0)
    )
  ));

  task_elt(task, "reserved"); // mach_header_64[0].reserved
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "mach_header_64"); // 0

  // TODO: on set load_commands_end: assert: sizeofcmds  = load_commands_end - load_commands_beg

  task_beg_elt(task, "load_commands"); // 0

  // command 1
  task_beg_elt(task, "segment_command_64"); // 0

  task_elt(task, "cmd"); // segment_command_64[0].cmd
  task_out_u32(task, must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));

  task_elt(task, "cmdsize"); // segment_command_64[0].cmdsize
  task_out_u32(task, u32(0x00000048));

  task_elt(task, "segname"); // segment_command_64[0].segname
  task_out_v16u8(task, (V16U8){.str = u8"__PAGEZERO"});

  task_elt(task, "vmaddr"); // segment_command_64[0].vmaddr
  task_out_u64(task, u64(0x00000000'00000000));

  task_elt(task, "vmsize"); // segment_command_64[0].vmsize
  task_out_u64(task, u64(0x00000001'00000000));

  task_elt(task, "fileoff"); // segment_command_64[0].fileoff
  task_out_u64(task, u64(0x00000000'00000000));

  task_elt(task, "filesize"); // segment_command_64[0].filesize
  task_out_u64(task, u64(0x00000000'00000000));

  task_elt(task, "maxprot"); // segment_command_64[0].maxprot
  task_out_u32(task, u32(0x00000000));

  task_elt(task, "initprot"); // segment_command_64[0].initprot
  task_out_u32(task, u32(0x00000000));

  task_elt(task, "nsects"); // segment_command_64[0].nsects
  task_out_u32(task, u32(0x00000000));

  task_elt(task, "flags"); // segment_command_64[0].flags
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "segment_command_64"); // 0

  // command 2
  task_beg_elt(task, "segment_command_64"); // 1

  task_elt(task, "cmd"); // segment_command_64[1].cmd
  task_out_u32(task, must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));

  task_elt(task, "cmdsize"); // segment_command_64[1].cmdsize
  task_out_u32(task, u32(0x00000188));

  task_elt(task, "segname"); // segment_command_64[1].segname
  //ol128(u128(u64(0x45545F5F'00005458), u64(0x00000000'00000000)));
  task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});

  task_elt(task, "vmaddr"); // segment_command_64[1].vmaddr
  task_out_u64(task, u64(0x00000001'00000000));

  task_elt(task, "vmsize"); // segment_command_64[1].vmsize
  task_out_u64(task, u64(0x00000000'00004000));

  task_elt(task, "fileoff"); // segment_command_64[1].fileoff
  task_out_u64(task, u64(0x00000000'00000000));

  task_elt(task, "filesize"); // segment_command_64[1].filesize
  task_out_u64(task, u64(0x00000000'00004000));

  task_elt(task, "maxprot"); // segment_command_64[1].maxprot
  task_out_u32(task, u32(0x00000005));

  task_elt(task, "initprot"); // segment_command_64[1].initprot
  task_out_u32(task, u32(0x00000005));

  task_elt(task, "nsects"); // segment_command_64[1].nsects
  task_out_u32(task, u32(0x00000004));

  task_elt(task, "flags"); // segment_command_64[1].flags
  task_out_u32(task, u32(0x00000000));

  task_beg_elt(task, "section_64"); // 0

  task_elt(task, "sectname"); // section_64[0].sectname
  task_out_v16u8(task, (V16U8){.str = u8"__text"});
  task_elt(task, "segname"); // section_64[0].segname
  task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});
  task_elt(task, "addr"); // section_64[0].addr
  task_out_u64(task, u64(0x00000001'00000460));
  task_elt(task, "size"); // section_64[0].size
  task_out_u64(task, u64(0x00000000'0000003c));
  task_elt(task, "offset"); // section_64[0].offset
  task_out_u32(task, u32(0x00000460));
  task_elt(task, "align"); // section_64[0].align
  task_out_u32(task, u32(0x00000002));

  task_elt(task, "reloff"); // section_64[0].reloff
  task_out_u32(task, u32(0x00000000));
  task_elt(task, "nreloc"); // section_64[0].nreloc
  task_out_u32(task, u32(0x00000000));

  task_elt(task, "flags"); // section_64[0].flags
  task_out_u32(task, must_be_same(
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

  task_elt(task, "reserved1"); // section_64[0].reserved1
  task_out_u32(task, u32(0x00000000));
  task_elt(task, "reserved2"); // section_64[0].reserved2
  task_out_u32(task, u32(0x00000000));
  task_elt(task, "reserved3"); // section_64[0].reserved3
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "section_64"); // 0

  task_beg_elt(task, "section_64"); // 1

  task_elt(task, "sectname"); // section_64[1].sectname
  task_out_v16u8(task, (V16U8){.str = u8"__stubs"});
  task_elt(task, "segname"); // section_64[1].segname
  task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});
  task_elt(task, "addr"); // section_64[1].addr
  task_out_u64(task, u64(0x00000001'0000049c));
  task_elt(task, "size"); // section_64[1].size
  task_out_u64(task, u64(0x00000000'0000000c));
  task_elt(task, "offset"); // section_64[1].offset
  task_out_u32(task, u32(0x0000049c));
  task_elt(task, "align"); // section_64[1].align
  task_out_u32(task, u32(0x00000002));

  task_elt(task, "reloff"); // section_64[1].reloff
  task_out_u32(task, u32(0x00000000));
  task_elt(task, "nreloc"); // section_64[1].nreloc
  task_out_u32(task, u32(0x00000000));

  task_elt(task, "flags"); // section_64[1].flags
  task_out_u32(task, must_be_same(
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
  task_elt(task, "reserved1"); // section_64[1].reserved1
  task_out_u32(task, u32(0x00000000));
  task_elt(task, "reserved2"); // section_64[1].reserved2
  task_elt(task, "stub_size"); // section_64[1].stub_size
  task_out_u32(task, u32(0x0000000c));
  task_elt(task, "reserved3"); // section_64[1].reserved3
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "section_64"); // 1

  task_beg_elt(task, "section_64"); // 2

  task_out_v16u8(task, (V16U8){.str = u8"__cstring"});
  task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});
  task_out_u64(task, u64(0x00000001'000004a8));
  task_out_u64(task, u64(0x00000000'00000005));
  task_out_u32(task, u32(0x000004a8));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "section_64"); // 2

  task_beg_elt(task, "section_64"); // 3

  task_out_v16u8(task, (V16U8){.str = u8"__unwind_info"});
  task_out_v16u8(task, (V16U8){.str = u8"__TEXT"});
  task_out_u64(task, u64(0x00000001'000004b0));
  task_out_u64(task, u64(0x00000000'00000058));
  task_out_u32(task, u32(0x000004b0));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "section_64"); // 3

  task_end_elt(task, "segment_command_64"); // 1

  // command 3
  task_beg_elt(task, "segment_command_64"); // 2

  task_out_u32(task, must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));
  task_out_u32(task, u32(0x00000098));
  task_out_v16u8(task, (V16U8){.str = u8"__DATA_CONST"});
  task_out_u64(task, u64(0x00000001'00004000));
  task_out_u64(task, u64(0x00000000'00004000));
  task_out_u64(task, u64(0x00000000'00004000));
  task_out_u64(task, u64(0x00000000'00004000));
  task_out_u32(task, u32(0x00000003));
  task_out_u32(task, u32(0x00000003));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x00000010));

  task_out_v16u8(task, (V16U8){.str = u8"__got"});
  task_out_v16u8(task, (V16U8){.str = u8"__DATA_CONST"});
  task_out_u64(task, u64(0x00000001'00004000));
  task_out_u64(task, u64(0x00000000'00000008));
  task_out_u32(task, u32(0x00004000));
  task_out_u32(task, u32(0x00000003));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000006));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));

  task_end_elt(task, "segment_command_64"); // 2

  // command 4
  task_beg_elt(task, "segment_command_64"); // 3

  task_out_u32(task, must_be_same(u32(0x00000019), U32(LC_SEGMENT_64)));
  task_out_u32(task, u32(0x00000048));
  task_out_v16u8(task, (V16U8){.str = u8"__LINKEDIT"});
  task_out_u64(task, u64(0x00000001'00008000));
  task_out_u64(task, u64(0x00000000'00004000));
  task_out_u64(task, u64(0x00000000'00008000));
  task_out_u64(task, u64(0x00000000'00000298));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x00000001));
  task_out_u64(task, u64(0x00000000));
  task_out_u32(task, u32(0x80000034));

  task_end_elt(task, "segment_command_64"); // 3

  // command 5
  task_beg_elt(task, "prebound_dylib_command"); // 0

  task_elt(task, "cmd"); // prebound_dylib_command[0].cmd
  task_out_u32(task, must_be_same(u32(0x00000010), U32(LC_PREBOUND_DYLIB)));
  task_elt(task, "cmdsize"); // prebound_dylib_command[0].cmdsize
  task_out_u32(task, u32(0x00008000));
  task_elt(task, "name"); // prebound_dylib_command[0].name
  task_out_u32(task, u32(0x00000060));
  task_elt(task, "nmodules"); // prebound_dylib_command[0].nmodules
  task_out_u32(task, u32(0x80000033));
  task_elt(task, "linked_modules"); // prebound_dylib_command[0].linked_modules
  task_out_u32(task, u32(0x00000010));

  task_end_elt(task, "prebound_dylib_command"); // 0

  task_end_elt(task, "load_commands"); // 0

  task_out_u32(task, u32(0x00008060));
  task_out_u32(task, u32(0x00000030));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000018));

  task_out_u32(task, u32(0x00008098));
  task_out_u32(task, u32(0x00000003));

  task_out_u32(task, u32(0x000080d0));
  task_out_u32(task, u32(0x00000028));
  task_out_u32(task, u32(0x0000000b));
  task_out_u32(task, u32(0x00000050));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));

  task_out_u32(task, u32(0x000080c8));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x0000000e));
  task_out_u32(task, u32(0x00000020));
  task_out_u32(task, u32(0x0000000c));

  // "/usr/lib/dyld"
  task_out_u32(task, u32(0x7273752f));
  task_out_u32(task, u32(0x62696c2f));
  task_out_u32(task, u32(0x6c79642f));

  task_out_u32(task, u32(0x00000064));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x0000001b));
  task_out_u32(task, u32(0x00000018));

  task_out_u32(task, u32(0xfd260cec));
  task_out_u32(task, u32(0x253118de));
  task_out_u32(task, u32(0x528214bb));
  task_out_u32(task, u32(0xd9594302));
  task_out_u32(task, u32(0x00000032));
  task_out_u32(task, u32(0x00000020));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x000f0000));
  task_out_u32(task, u32(0x000f0500));
  task_out_u32(task, u32(0x00000001));
  task_out_u32(task, u32(0x00000003));
  task_out_u32(task, u32(0x048f0500));
  task_out_u32(task, u32(0x0000002a));
  task_out_u32(task, u32(0x00000010));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x80000028));

  task_out_u32(task, u32(0x00000018));
  task_out_u32(task, u32(0x00000460));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x0000000c));
  task_out_u32(task, u32(0x00000038));
  task_out_u32(task, u32(0x00000018));
  task_out_u32(task, u32(0x00000002));
  task_out_u32(task, u32(0x05470000));
  task_out_u32(task, u32(0x00010000));

  // "/usr/lib/libSystem.B.dylib"
  task_out_u32(task, u32(0x7273752f));
  task_out_u32(task, u32(0x62696c2f));
  task_out_u32(task, u32(0x62696c2f));
  task_out_u32(task, u32(0x74737953));
  task_out_u32(task, u32(0x422e6d65));
  task_out_u32(task, u32(0x6c79642e));
  task_out_u32(task, u32(0x00006269));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000026));
  task_out_u32(task, u32(0x00000010));

  task_out_u32(task, u32(0x00008090));
  task_out_u32(task, u32(0x00000008));
  task_out_u32(task, u32(0x00000029));
  task_out_u32(task, u32(0x00000010));

  task_out_u32(task, u32(0x00008098));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x0000001d));
  task_out_u32(task, u32(0x00000010));
  task_out_u32(task, u32(0x00008100));
  task_out_u32(task, u32(0x00000198));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0xd100c3ff));
  task_out_u32(task, u32(0xa9027bfd));
  task_out_u32(task, u32(0x910083fd));
  task_out_u32(task, u32(0x52800008));
  task_out_u32(task, u32(0xb9000fe8));
  task_out_u32(task, u32(0xb81fc3bf));
  task_out_u32(task, u32(0xb81f83a0));
  task_out_u32(task, u32(0xf9000be1));
  task_out_u32(task, u32(0x90000000));
  task_out_u32(task, u32(0x9112a000));
  task_out_u32(task, u32(0x94000005));
  task_out_u32(task, u32(0xb9400fe0));
  task_out_u32(task, u32(0xa9427bfd));
  task_out_u32(task, u32(0x9100c3ff));
  task_out_u32(task, u32(0xd65f03c0));
  task_out_u32(task, u32(0x90000030));
  task_out_u32(task, u32(0xf9400210));
  task_out_u32(task, u32(0xd61f0200));

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

  task_out_u64(task, u64(0x80000000'00000000));

  // buf_skip(&BUF, +0x3FFC);
  task_out_pad(task, 0x8000);

  // 16 KiB of zeros

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
  task_out_u32(task, u32(0x75705f00));
  task_out_u32(task, u32(0x00007374));

  task_out_u32(task, u32(0x00000000));

  // "_"
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

  task_out_u32(task, u32(0xc00cdefa));
  task_out_u32(task, u32(0x95010000));
  task_out_u32(task, u32(0x01000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x14000000));

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

  task_out_u32(task, u32(0x3c000000));
  task_out_u32(task, u32(0x00000000));
  task_out_u32(task, u32(0x01000000));

  // "reow"
  task_out_u32(task, u32(0x776f6572));
  // ".bin"
  task_out_u32(task, u32(0x6e69622e));

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

  task_end_elt(task, "mach_object"); // 0

  if (fat_binary_enabled) {
    task_end_elt(task, "fat_binary"); // 0
  }

  task_end_elt(task, "file"); // 0

  task_end(task);

  return true;

}


//  Count the number of elements in the program
////////////////////////////////////////////////////////////////

struct_type(NumEltsTask);

struct NumEltsTask {
  TaskVar  task;
  SizeVar  begs;
  SizeVar  depth;
  SizeVar  leaves;
  SizeVar  ends;
};

static inline Bool num_elts_beg_elt(
  TaskVarRef task,
  [[maybe_unused]] Tag tag
  ) {
  assert(task != nullptr);
  NumEltsTaskVarRef self = (NumEltsTaskVarRef)task;
  assert(self->begs < SIZE_MAX);
  assert(self->depth < SIZE_MAX);
  return
    ++self->begs,
    ++self->depth,
    true;
}

static inline Bool num_elts_elt(
  TaskVarRef task,
  [[maybe_unused]] Tag tag
  ) {
  assert(task != nullptr);
  NumEltsTaskVarRef self = (NumEltsTaskVarRef)task;
  assert(self->leaves < SIZE_MAX);
  return
    ++self->leaves,
    true;
}

static inline Bool num_elts_end_elt(
  TaskVarRef task,
  Tag tag
) {
  assert(task != nullptr);
  NumEltsTaskVarRef self = (NumEltsTaskVarRef)task;
  assert(self->ends < SIZE_MAX);
  return
    self->depth > 0 ? (
      ++self->ends,
      --self->depth,
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
        self->begs,
        self->ends,
        self->depth
      ),
      false
    );
}

static inline Bool num_elts_end(
  TaskVarRef task
) {
  assert(task != nullptr);
  NumEltsTaskVarRef self = (NumEltsTaskVarRef)task;
  return
    self->depth == 0 and
    self->begs == self->ends
    or (
      error(
        "missing end tag; "
        "begs: %zu, "
        "depth: %zu, "
        "leaves: %zu, "
        "ends: %zu",
        self->begs,
        self->depth,
        self->leaves,
        self->ends
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
  SizeVar  size;
  SizeVar  null;
  SizeVar  padding;
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

static inline Bool num_tag_size_beg_elt(
  TaskVarRef task,
  Tag tag
) {
  assert(task != nullptr);
  NumTagSizeTaskVarRef self = (NumTagSizeTaskVarRef)task;
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

static inline Bool num_tags_beg_elt(
  TaskVarRef task,
  Tag tag
) {
  assert(task != nullptr);
  assert(tag != nullptr);
  NumTagsTaskVarRef self = (NumTagsTaskVarRef)task;
  assert(self->num <= self->end);
  for (IdxVar i = 0; i < self->num; ++i) {
    if (strcmp(self->set[i].tag, tag) == 0) {
      ++self->set[i].num;
      return true;
    }
  }
  assert(self->num < self->end);
  self->set[self->num].tag = tag;
  self->set[self->num].num = 1;
  ++self->num;
  return true;
}


//  Generate output
////////////////////////////////////////////////////////////////

struct_type(OutputTask);

struct OutputTask {
  TaskVar  task;
  BufVar   buf;
};

static inline Bool output_out_u32(TaskVarRef task, U32 val) {
  assert(task != nullptr);
  OutputTaskVarRef self = (OutputTaskVarRef)task;
  buf_out_u32(&self->buf, val);
  return true;
}

static inline Bool output_out_u64(TaskVarRef task, U64 val) {
  assert(task != nullptr);
  OutputTaskVarRef self = (OutputTaskVarRef)task;
  buf_out_u64(&self->buf, val);
  return true;
}

static inline Bool output_out_v16u8(TaskVarRef task, V16U8 val) {
  assert(task != nullptr);
  OutputTaskVarRef self = (OutputTaskVarRef)task;
  buf_out_v16u8(&self->buf, val);
  return true;
}

static inline Bool output_out_pad(TaskVarRef task, Size size) {
  assert(task != nullptr);
  OutputTaskVarRef self = (OutputTaskVarRef)task;
  buf_out_pad(&self->buf, size);
  return true;
}


//  Run compilation passes
////////////////////////////////////////////////////////////////

Bool nb(
  [[maybe_unused]] Str pgm,
  Num arg_num,
  Args args
) {

  if (arg_num != 1) return false;

  NumEltsTaskVar num_elts = (NumEltsTaskVar){
    .task = (Task){
      .beg_elt  = num_elts_beg_elt  ,
      .elt      = num_elts_elt      ,
      .end_elt  = num_elts_end_elt  ,
      .end      = num_elts_end      ,
    },
    .begs   = 0,
    .depth  = 1,
    .leaves = 0,
    .ends   = 0,
  };
  if (not work((TaskVarRef)&num_elts)) return false;
  trace(
    "counted (%zu = %zu) branches + %zu leaves = %zu elements",
    num_elts.begs,
    num_elts.ends,
    num_elts.leaves,
    num_elts.ends + num_elts.leaves
  );

  NumTagSizeTaskVar num_tag_size = (NumTagSizeTaskVar){
    .task = (Task){
      .beg_elt = num_tag_size_beg_elt,
    },
    .size = 0,
    .null = 0,
    .padding = 0,
  };
  if (not work((TaskVarRef)&num_tag_size)) return false;
  trace("counted %zu tag bytes", num_tag_size.size);
  trace("counted %zu NUL bytes", num_tag_size.null);
  trace("counted %zu pad bytes", num_tag_size.padding);
  Size tag_size
    = num_tag_size.size
    + num_tag_size.null
    + num_tag_size.padding;
  trace("counted %zu total bytes", tag_size);

  NumTagsTaskVar num_tags = (NumTagsTaskVar){
    .task = (Task){
      .beg_elt = num_tags_beg_elt,
    },
    .set = calloc(num_elts.ends, sizeof num_tags.set[0]),
    .num = 0,
    .end = num_elts.ends,
  };
  assert(num_tags.set != nullptr);
  if (not work((TaskVarRef)&num_tags)) return false;
  trace("counted %zu unique tags", num_tags.num);

  free(num_tags.set);

  FILE *o = fopen(args[0], "wb");
  assert(o);

  OutputTaskVar output = (OutputTaskVar){
    .task = (Task){
      .out_u32   = output_out_u32    ,
      .out_u64   = output_out_u64    ,
      .out_v16u8 = output_out_v16u8  ,
      .out_pad   = output_out_pad    ,
    },
    .buf = (Buf){
      .in = &reow[0],
      .at = 0,
      .end = numof(reow)
    }
  };
  if (not work((TaskVarRef)&output)) return false;
  assert(output.buf.at <= output.buf.end);
  Size size = output.buf.at;
  trace("output %zu bytes", size);
  if (size != sizeof reow) warn(
    "final size %zu is less than wanted size %zu",
    size,
    sizeof reow
  );
  fwrite((void *)&reow[0], 1, size, o);
  fclose(o);

  trace("good");
  return true;

}


//  Unit tests
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
