#include <assert.h>
#include <inttypes.h>
#include <iso646.h>
#include <stdarg.h>
// #include <stdbit.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <mach-o/loader.h>
#include <mach/vm_page_size.h>

typedef int ExitStatus;
typedef int Argc;
typedef char **Argv;

typedef char const *StrVar;
typedef StrVar const Str;

typedef unsigned _BitInt(  1)  U1Var                  ;
typedef unsigned _BitInt(  8)  U8Var                  ;
typedef unsigned _BitInt( 16)  U16Var                 ;
typedef unsigned _BitInt( 24)  U24Var                 ;
typedef unsigned _BitInt( 32)  U32Var                 ;
typedef unsigned _BitInt( 64)  U64Var                 ;
typedef unsigned _BitInt(128)  U128Var                ;

typedef                        U1Var      const U1    ;
typedef                        U8Var      const U8    ;
typedef                        U16Var     const U16   ;
typedef                        U24Var     const U24   ;
typedef                        U32Var     const U32   ;
typedef                        U64Var     const U64   ;
typedef                        U128Var    const U128  ;

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

[[maybe_unused]] static inline U32 l32(U32 i) {
  return 0
    | ((i & u32(0x000000FF)) << 03'0)
    | ((i & u32(0x0000FF00)) << 01'0)
    | ((i & u32(0x00FF0000)) >> 01'0)
    | ((i & u32(0xFF000000)) >> 03'0);
}

static U8Var reow[33432];

typedef enum RefType {
  RefTypeU32,
  RefTypeU64,
} RefTypeVar; typedef RefTypeVar const RefType;

typedef struct U32Ref {
  U32Var *ptr;
  Str lbl;
} U32RefVar; typedef U32RefVar const U32Ref;

typedef union Ref {
  U32Ref u32;
} RefVar; typedef RefVar const Ref;

typedef void OnSetCallback(Ref ref);

typedef struct OnSet {
  Ref ref;
  OnSetCallback *callback;
} OnSetVar; typedef OnSetVar const OnSet;

[[maybe_unused]]
static inline U32 rl32(U8Var const *const there) {
  return
    ( U32(there[0]) << 00'0
    | U32(there[1]) << 01'0
    | U32(there[2]) << 02'0
    | U32(there[3]) << 03'0
    );
}

[[maybe_unused]]
static inline U64 rl64(U8Var const *const there) {
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

static inline void ol32_(U8Var **const there, U32 i) {
  U8Var *const here = *there;
  here[0] = (i & u32(0x000000FF)) >> 00'0;
  here[1] = (i & u32(0x0000FF00)) >> 01'0;
  here[2] = (i & u32(0x00FF0000)) >> 02'0;
  here[3] = (i & u32(0xFF000000)) >> 03'0;
  *there = here + sizeof i;
}

static inline void ol64_(U8Var **const there, U64 i) {
  U8Var *const here = *there;
  here[0] = (i & u64(0x00000000'000000FF)) >> 00'0;
  here[1] = (i & u64(0x00000000'0000FF00)) >> 01'0;
  here[2] = (i & u64(0x00000000'00FF0000)) >> 02'0;
  here[3] = (i & u64(0x00000000'FF000000)) >> 03'0;
  here[4] = (i & u64(0x000000FF'00000000)) >> 04'0;
  here[5] = (i & u64(0x0000FF00'00000000)) >> 05'0;
  here[6] = (i & u64(0x00FF0000'00000000)) >> 06'0;
  here[7] = (i & u64(0xFF000000'00000000)) >> 07'0;
  *there = here + sizeof i;
}

typedef union V16U8 {
  U8 vec[16];
  unsigned char str[16];
} V16U8Var; typedef V16U8Var const V16U8;

static inline void ov16u8_(U8Var **const there, V16U8 v) {
  static_assert(sizeof v.vec == 16);
  U8Var *const here = *there;
  memcpy((void *)&here[0], (void *)&v.vec[0], sizeof v.vec);
  *there = here + sizeof v.vec;
}

[[maybe_unused]]
static inline void ol128_(U8Var **const there, U128 i) {
  U8Var *const here = *there;
  here[0x0] = (i & u128(u64(0x00000000'00000000), u64(0x00000000'000000FF))) >> 000'0;
  here[0x1] = (i & u128(u64(0x00000000'00000000), u64(0x00000000'0000FF00))) >> 001'0;
  here[0x2] = (i & u128(u64(0x00000000'00000000), u64(0x00000000'00FF0000))) >> 002'0;
  here[0x3] = (i & u128(u64(0x00000000'00000000), u64(0x00000000'FF000000))) >> 003'0;
  here[0x4] = (i & u128(u64(0x00000000'00000000), u64(0x000000FF'00000000))) >> 004'0;
  here[0x5] = (i & u128(u64(0x00000000'00000000), u64(0x0000FF00'00000000))) >> 005'0;
  here[0x6] = (i & u128(u64(0x00000000'00000000), u64(0x00FF0000'00000000))) >> 006'0;
  here[0x7] = (i & u128(u64(0x00000000'00000000), u64(0xFF000000'00000000))) >> 007'0;
  here[0x8] = (i & u128(u64(0x00000000'000000FF), u64(0x00000000'00000000))) >> 010'0;
  here[0x9] = (i & u128(u64(0x00000000'0000FF00), u64(0x00000000'00000000))) >> 011'0;
  here[0xA] = (i & u128(u64(0x00000000'00FF0000), u64(0x00000000'00000000))) >> 012'0;
  here[0xB] = (i & u128(u64(0x00000000'FF000000), u64(0x00000000'00000000))) >> 013'0;
  here[0xC] = (i & u128(u64(0x000000FF'00000000), u64(0x00000000'00000000))) >> 014'0;
  here[0xD] = (i & u128(u64(0x0000FF00'00000000), u64(0x00000000'00000000))) >> 015'0;
  here[0xE] = (i & u128(u64(0x00FF0000'00000000), u64(0x00000000'00000000))) >> 016'0;
  here[0xF] = (i & u128(u64(0xFF000000'00000000), u64(0x00000000'00000000))) >> 017'0;
  *there = here + sizeof i;
}

#define ol32(x) ol32_(&here, x)
#define ol64(x) ol64_(&here, x)
#define ol128(x) ol128_(&here, x)
#define ov16u8(x) ov16u8_(&here, x)
#define o8(x) do *here++ = (x); while (false)
#define o8s(i, n, x) \
  do \
    for (size_t i = 0; i < (n); ++i) \
      *here++ = (x); \
  while (false)

#define till(to) \
  while (((size_t)(here - file_begin) % (to)) != (size_t)0)

typedef unsigned long LineVar;
typedef LineVar const Line;
#define LineFmt "d"

#define id(a, b)                                               \
  (                                                             \
    (a) == (b) ?                                                \
    (a) :                                                       \
    (fputs((#a " != " #b), stderr), abort(), (b))               \
  )

#define id_(typ, fmt, a, b)                                    \
  (                                                             \
    (a) == (b) ? (a) : (                                        \
      fprintf(                                                  \
        stderr,                                                 \
        "%s:%"LineFmt": id_(%s, %s): %"fmt" != %"fmt"\n",      \
        __FILE__,                                               \
        __LINE__,                                               \
        #a,                                                     \
        #b,                                                     \
        (typ)(a),                                               \
        (typ)(b)                                                \
      ),                                                        \
      abort(),                                                  \
      (b)                                                       \
    )                                                           \
  )

#define idu24(a, b)                                            \
  id_(uint32_t, PRIX32, a, b)

#define idu32(a, b)                                            \
  id_(uint32_t, PRIX32, a, b)

#define idu64(a, b)                                            \
  id_(uint64_t, PRIX64, a, b)

#define lblu32(lbl, exp) \
  (exp)

ExitStatus
main(
  Argc argc,
  Argv argv
) {
  assert(argc == 2);
  assert(argv);
  FILE *o = fopen(argv[1], "wb");
  assert(o);

  U8Var *here = &reow[0];

#define label(name, idx)                                        \
  [[maybe_unused]] U8Var *const name##_##idx = here

#define field(name, idx, sub)                                   \
  label(name, idx##_##sub)

#define begin(name, idx)                                        \
  label(name##_begin, idx)

#define end(name, idx)                                          \
  label(name##_end, idx)

  begin(file, 0);

  //  fill with sentinel bytes
  //  memset((void *)file_begin_0, 0xBA, sizeof reow);

  /*  struct mach_header_64 header = (struct mach_header_64) {  */
  /*    .magic = MH_MAGIC_64,  */
  /*    .cputype = CPU_TYPE_ARM64 | CPU_TYPE_ARM,  */
  /*    .cpusubtype = CPU_SUBTYPE_ARM64_ALL,  */
  /*    .filetype = MH_OBJECT,  */
  /*    uint32_t	filetype;	/\* type of file *\/  */
  /*    uint32_t	ncmds;		/\* number of load commands *\/  */
  /*    uint32_t	sizeofcmds;	/\* the size of all the load commands *\/  */
  /*    uint32_t	flags;		/\* flags *\/  */
  /*    uint32_t	reserved;	/\* reserved *\/  */
  /*  };  */

  begin(fat_binary, 0);

  /*  [[maybe_unused]] U32 nb_object_flags_MH_PIE        = U32(u1(1)) << 02'5;  */
  /*  [[maybe_unused]] U32 nb_object_flags_MH_TWOLEVEL   = U32(u1(1)) << 00'7;  */
  /*  [[maybe_unused]] U32 nb_object_flags_MH_LAZY_INIT  = U32(u1(1)) << 00'2;  */
  /*  [[maybe_unused]] U32 nb_object_flags_MH_NOUNDEFS   = U32(u1(1)) << 00'0;  */

  /*  if (false) {  */
  /*    */
  /*    begin(fat_header, 0);  */
  /*    {  */
  /*    */
  /*      U32 nb_FAT_MAGIC = u32(0xCAFEBABE);  */
  /*      U32 magic = nb_FAT_MAGIC;  */
  /*      ol32(idu32(magic, u32(0xCAFEBABE)));  */
  /*    */
  /*      U32 nfat_arch = u32(1);  */
  /*      ol32(nfat_arch);  */
  /*    */
  /*    }  */
  /*    end(fat_header, 0);  */
  /*    */
  /*    begin(fat_arch, 0);  */
  /*    {  */
  /*    */
  /*      U32 cputype = CPU_TYPE_ARM64;  */
  /*      ol32(cputype);  */
  /*    */
  /*      U32 cpusubtype = CPU_SUBTYPE_ARM64_ALL;  */
  /*      ol32(cpusubtype);  */
  /*    */
  /*      U32 offset = 0; // TODO: object_1.begin  */
  /*      ol32(offset);  */
  /*    */
  /*      U32 size = 0; // TODO: fat_binary.end  */
  /*      ol32(size);  */
  /*    */
  /*      // mach/vm_page_size.h:vm_page_shift  */
  /*      U32 nb_PAGE_SHIFT = idu32(vm_page_shift, u32(14));  */
  /*      U32 align = nb_PAGE_SHIFT;  */
  /*      ol32(align);  */
  /*    */
  /*    }  */
  /*    end(fat_arch, 0);  */
  /*    */
  /*    // pad up to nb_PAGE_SIZE with u8(0x00)  */
  /*    // mach/vm_page_size.h:vm_page_size  */
  /*    U32 nb_PAGE_SIZE = idu32(vm_page_size, u32(0x4000));  */
  /*    till(nb_PAGE_SIZE)  */
  /*      o8(u8(0x00));  */
  /*    */
  /*  }  */

  /*  U32 MH_MAGIC = idu32(u32(0xFEEDFACE), MH_MAGIC);  */
  /*  U32 MH_MAGIC_64 = idu32(u32(0xFEEDFACF), idu32(MH_MAGIC | 1, MH_MAGIC_64));  */
  /*  [[maybe_unused]] U32 MH_OBJECT = u32(1);  */
  /*  [[maybe_unused]] U32 MH_EXECUTE = idu32(u32(2), MH_EXECUTE);  */

  begin(mach_object, 0);
  begin(mach_header_64, 0);

  field(mach_header_64, 0, magic);
  ol32(idu32(u32(0xFEEDFACF), MH_MAGIC_64));

  /*  U8 CPU_ARCH_ABI64 = u8(0x01);  */
  /*  U24 CPU_TYPE_ARM = u24(12);  */
  /*  [[maybe_unused]] U32 nb_CPU_ARCH_MASK = u32(0xFF000000);  */
  /*  [[maybe_unused]] U32 nb_CPU_TYPE_MASK = u32(0x00FFFFFF);  */
  /*  U32 nb_CPU_TYPE_ARM64  */
  /*    = U32(nb_CPU_ARCH_ABI64) << 03'0  */
  /*    | U32(nb_CPU_TYPE_ARM) << 00'0;  */
  /*  U32 nb_CPU_SUBTYPE_ARM64_ALL = u32(0);  */

  field(mach_header_64, 0, cputype);
  U32 CPU_TYPE_MASK = compl U32(CPU_ARCH_MASK);
  ol32(idu32(
    u32(0x0100000C),
    idu32(
      U32(CPU_TYPE_ARM64),
      ( ( U32(idu32(u32(0x01000000), U32(CPU_ARCH_ABI64)))
        & idu32(u32(0xFF000000), U32(CPU_ARCH_MASK))
        )
      | ( U32(idu24(u24(12), U24(CPU_TYPE_ARM)))
        & idu32(u32(0x00FFFFFF), U32(CPU_TYPE_MASK))
        )
      )
    )
  ));

  field(mach_header_64, 0, cpusubtype);
  ol32(idu32(u32(0x00000000), U32(CPU_SUBTYPE_ARM64_ALL)));

  field(mach_header_64, 0, filetype);
  ol32(idu32(u32(0x00000002), U32(MH_EXECUTE)));

  field(mach_header_64, 0, ncmds);
  ol32(idu32(u32(0x00000011), u32(17)));

  field(mach_header_64, 0, sizeofcmds);
  ol32(idu32(u32(0x00000420), u32(1056)));

  field(mach_header_64, 0, flags);
  ol32(idu32(
    u32(0x00200085),
    ( idu32(idu32(u32(0x00200000), U32(MH_PIE)     ), u32(1) << 02'5)
    | idu32(idu32(u32(0x00000080), U32(MH_TWOLEVEL)), u32(1) << 00'7)
    | idu32(idu32(u32(0x00000004), U32(MH_DYLDLINK)), u32(1) << 00'2)
    | idu32(idu32(u32(0x00000001), U32(MH_NOUNDEFS)), u32(1) << 00'0)
    )
  ));

  field(mach_header_64, 0, reserved);
  ol32(u32(0x00000000));

  end(mach_header_64, 0);

  // TODO: on set load_commands_end: assert: sizeofcmds  = load_commands_end - load_commands_begin

  begin(load_commands, 0);

  // command 1
  begin(segment_command_64, 0);

  field(segment_command_64, 0, cmd);
  ol32(idu32(u32(0x00000019), U32(LC_SEGMENT_64)));

  field(segment_command_64, 0, cmdsize);
  ol32(u32(0x00000048));

  field(segment_command_64, 0, segname);
  ov16u8((V16U8){.str = u8"__PAGEZERO"});

  field(segment_command_64, 0, vmaddr);
  ol64(u64(0x00000000'00000000));

  field(segment_command_64, 0, vmsize);
  ol64(u64(0x00000001'00000000));

  field(segment_command_64, 0, fileoff);
  ol64(u64(0x00000000'00000000));

  field(segment_command_64, 0, filesize);
  ol64(u64(0x00000000'00000000));

  field(segment_command_64, 0, maxprot);
  ol32(u32(0x00000000));

  field(segment_command_64, 0, initprot);
  ol32(u32(0x00000000));

  field(segment_command_64, 0, nsects);
  ol32(u32(0x00000000));

  field(segment_command_64, 0, flags);
  ol32(u32(0x00000000));

  end(segment_command_64, 0);

  // command 2
  begin(segment_command_64, 1);

  field(segment_command_64, 1, cmd);
  ol32(idu32(u32(0x00000019), U32(LC_SEGMENT_64)));

  field(segment_command_64, 1, cmdsize);
  ol32(u32(0x00000188));

  field(segment_command_64, 1, segname);
  //ol128(u128(u64(0x45545F5F'00005458), u64(0x00000000'00000000)));
  ov16u8((V16U8){.str = u8"__TEXT"});

  label(segment_command_64_1, vmaddr);
  ol64(u64(0x00000001'00000000));

  field(segment_command_64, 1, vmsize);
  ol64(u64(0x00000000'00004000));

  field(segment_command_64, 1, fileoff);
  ol64(u64(0x00000000'00000000));

  field(segment_command_64, 1, filesize);
  ol64(u64(0x00000000'00004000));

  field(segment_command_64, 1, maxprot);
  ol32(u32(0x00000005));

  field(segment_command_64, 1, initprot);
  ol32(u32(0x00000005));

  field(segment_command_64, 1, nsects);
  ol32(u32(0x00000004));

  field(segment_command_64, 1, flags);
  ol32(u32(0x00000000));

  begin(section_64, 0);

  field(section_64, 0, sectname);
  ov16u8((V16U8){.str = u8"__text"});
  field(section_64, 0, segname);
  ov16u8((V16U8){.str = u8"__TEXT"});
  field(section_64, 0, addr);
  ol64(u64(0x00000001'00000460));
  field(section_64, 0, size);
  ol64(u64(0x00000000'0000003c));
  field(section_64, 0, offset);
  ol32(u32(0x00000460));
  field(section_64, 0, align);
  ol32(u32(0x00000002));

  field(section_64, 0, reloff);
  ol32(u32(0x00000000));
  field(section_64, 0, nreloc);
  ol32(u32(0x00000000));

  field(section_64, 0, flags);
  ol32(idu32(
    u32(0x80000400),
    ( ( idu32(u32(0x000000FF), U32(SECTION_TYPE))
      & idu32(u32(0x00000000), U32(S_REGULAR))
      )
    | ( idu32(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
      & ( idu32(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
        | idu32(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
        )
      )
    )
  ));

  field(section_64, 0, reserved1);
  ol32(u32(0x00000000));
  field(section_64, 0, reserved2);
  ol32(u32(0x00000000));
  field(section_64, 0, reserved3);
  ol32(u32(0x00000000));

  end(section_64, 0);

  begin(section_64, 1);

  field(section_64, 1, sectname);
  ov16u8((V16U8){.str = u8"__stubs"});
  field(section_64, 1, segname);
  ov16u8((V16U8){.str = u8"__TEXT"});
  field(section_64, 1, addr);
  ol64(u64(0x00000001'0000049c));
  field(section_64, 1, size);
  ol64(u64(0x00000000'0000000c));
  field(section_64, 1, offset);
  ol32(u32(0x0000049c));
  field(section_64, 1, align);
  ol32(u32(0x00000002));

  field(section_64, 1, reloff);
  ol32(u32(0x00000000));
  field(section_64, 1, nreloc);
  ol32(u32(0x00000000));

  field(section_64, 1, flags);
  ol32(idu32(
    u32(0x80000408),
    ( ( idu32(u32(0x000000FF), U32(SECTION_TYPE))
      & idu32(u32(0x00000008), U32(S_SYMBOL_STUBS))
      )
    | ( idu32(u32(0xFFFFFF00), U32(SECTION_ATTRIBUTES))
      & ( idu32(u32(0x00000400), U32(S_ATTR_SOME_INSTRUCTIONS))
        | idu32(u32(0x80000000), U32(S_ATTR_PURE_INSTRUCTIONS))
        )
      )
    )
  ));
  field(section_64, 1, reserved1);
  ol32(u32(0x00000000));
  field(section_64, 1, reserved2);
  field(section_64, 1, stub_size);
  ol32(u32(0x0000000c));
  field(section_64, 1, reserved3);
  ol32(u32(0x00000000));

  end(section_64, 1);

  begin(section_64, 2);

  ov16u8((V16U8){.str = u8"__cstring"});
  ov16u8((V16U8){.str = u8"__TEXT"});
  ol64(u64(0x00000001'000004a8));
  ol64(u64(0x00000000'00000005));
  ol32(u32(0x000004a8));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000002));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  end(section_64, 2);

  begin(section_64, 3);

  ov16u8((V16U8){.str = u8"__unwind_info"});
  ov16u8((V16U8){.str = u8"__TEXT"});
  ol64(u64(0x00000001'000004b0));
  ol64(u64(0x00000000'00000058));
  ol32(u32(0x000004b0));
  ol32(u32(0x00000002));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  end(section_64, 3);

  end(segment_command_64, 1);

  // command 3
  begin(segment_command_64, 2);

  ol32(idu32(u32(0x00000019), U32(LC_SEGMENT_64)));
  ol32(u32(0x00000098));
  ov16u8((V16U8){.str = u8"__DATA_CONST"});
  ol64(u64(0x00000001'00004000));
  ol64(u64(0x00000000'00004000));
  ol64(u64(0x00000000'00004000));
  ol64(u64(0x00000000'00004000));
  ol32(u32(0x00000003));
  ol32(u32(0x00000003));
  ol32(u32(0x00000001));
  ol32(u32(0x00000010));

  ov16u8((V16U8){.str = u8"__got"});
  ov16u8((V16U8){.str = u8"__DATA_CONST"});
  ol64(u64(0x00000001'00004000));
  ol64(u64(0x00000000'00000008));
  ol32(u32(0x00004000));
  ol32(u32(0x00000003));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000006));
  ol32(u32(0x00000001));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  end(segment_command_64, 2);

  // command 4
  begin(segment_command_64, 3);

  ol32(idu32(u32(0x00000019), U32(LC_SEGMENT_64)));
  ol32(u32(0x00000048));
  ov16u8((V16U8){.str = u8"__LINKEDIT"});
  ol64(u64(0x00000001'00008000));
  ol64(u64(0x00000000'00004000));
  ol64(u64(0x00000000'00008000));
  ol64(u64(0x00000000'00000298));
  ol32(u32(0x00000001));
  ol32(u32(0x00000001));
  ol64(u64(0x00000000));
  ol32(u32(0x80000034));

  end(segment_command_64, 3);

  // command 5
  begin(prebound_dylib_command, 0);

  field(prebound_dylib_command, 0, cmd);
  ol32(idu32(u32(0x00000010), U32(LC_PREBOUND_DYLIB)));
  field(prebound_dylib_command, 0, cmdsize);
  ol32(u32(0x00008000));
  field(prebound_dylib_command, 0, name);
  ol32(u32(0x00000060));
  field(prebound_dylib_command, 0, nmodules);
  ol32(u32(0x80000033));
  field(prebound_dylib_command, 0, linked_modules);
  ol32(u32(0x00000010));

  end(prebound_dylib_command, 0);

  end(load_commands, 0);

  ol32(u32(0x00008060));
  ol32(u32(0x00000030));
  ol32(u32(0x00000002));
  ol32(u32(0x00000018));

  ol32(u32(0x00008098));
  ol32(u32(0x00000003));

  ol32(u32(0x000080d0));
  ol32(u32(0x00000028));
  ol32(u32(0x0000000b));
  ol32(u32(0x00000050));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000002));
  ol32(u32(0x00000002));
  ol32(u32(0x00000001));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  ol32(u32(0x000080c8));
  ol32(u32(0x00000002));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x0000000e));
  ol32(u32(0x00000020));
  ol32(u32(0x0000000c));

  // "/usr/lib/dyld"
  ol32(u32(0x7273752f));
  ol32(u32(0x62696c2f));
  ol32(u32(0x6c79642f));

  ol32(u32(0x00000064));
  ol32(u32(0x00000000));
  ol32(u32(0x0000001b));
  ol32(u32(0x00000018));

  ol32(u32(0xfd260cec));
  ol32(u32(0x253118de));
  ol32(u32(0x528214bb));
  ol32(u32(0xd9594302));
  ol32(u32(0x00000032));
  ol32(u32(0x00000020));
  ol32(u32(0x00000001));
  ol32(u32(0x000f0000));
  ol32(u32(0x000f0500));
  ol32(u32(0x00000001));
  ol32(u32(0x00000003));
  ol32(u32(0x048f0500));
  ol32(u32(0x0000002a));
  ol32(u32(0x00000010));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x80000028));

  ol32(u32(0x00000018));
  ol32(u32(0x00000460));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x0000000c));
  ol32(u32(0x00000038));
  ol32(u32(0x00000018));
  ol32(u32(0x00000002));
  ol32(u32(0x05470000));
  ol32(u32(0x00010000));

  // "/usr/lib/libSystem.B.dylib"
  ol32(u32(0x7273752f));
  ol32(u32(0x62696c2f));
  ol32(u32(0x62696c2f));
  ol32(u32(0x74737953));
  ol32(u32(0x422e6d65));
  ol32(u32(0x6c79642e));
  ol32(u32(0x00006269));
  ol32(u32(0x00000000));
  ol32(u32(0x00000026));
  ol32(u32(0x00000010));

  ol32(u32(0x00008090));
  ol32(u32(0x00000008));
  ol32(u32(0x00000029));
  ol32(u32(0x00000010));

  ol32(u32(0x00008098));
  ol32(u32(0x00000000));
  ol32(u32(0x0000001d));
  ol32(u32(0x00000010));
  ol32(u32(0x00008100));
  ol32(u32(0x00000198));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0xd100c3ff));
  ol32(u32(0xa9027bfd));
  ol32(u32(0x910083fd));
  ol32(u32(0x52800008));
  ol32(u32(0xb9000fe8));
  ol32(u32(0xb81fc3bf));
  ol32(u32(0xb81f83a0));
  ol32(u32(0xf9000be1));
  ol32(u32(0x90000000));
  ol32(u32(0x9112a000));
  ol32(u32(0x94000005));
  ol32(u32(0xb9400fe0));
  ol32(u32(0xa9427bfd));
  ol32(u32(0x9100c3ff));
  ol32(u32(0xd65f03c0));
  ol32(u32(0x90000030));
  ol32(u32(0xf9400210));
  ol32(u32(0xd61f0200));

  // "reow"
  ol32(u32(0x776f6572));
  ol32(u32(0x00000000));
  ol32(u32(0x00000001));
  ol32(u32(0x0000001c));
  ol32(u32(0x00000000));
  ol32(u32(0x0000001c));
  ol32(u32(0x00000000));
  ol32(u32(0x0000001c));
  ol32(u32(0x00000002));
  ol32(u32(0x00000460));
  ol32(u32(0x00000040));
  ol32(u32(0x00000040));
  ol32(u32(0x0000049c));
  ol32(u32(0x00000000));
  ol32(u32(0x00000040));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000003));
  ol32(u32(0x0001000c));
  ol32(u32(0x00010010));
  ol32(u32(0x00000000));
  ol32(u32(0x04000000));

  here += 0x3B00;
  //  14 3/4 KiB of zeros

  ol32(u32(0x80000000));
  here += 0x3FFC;
  // 16 KiB of zeros

  ol32(u32(0x00000020));
  ol32(u32(0x00000050));
  ol32(u32(0x00000054));
  ol32(u32(0x00000001));
  ol32(u32(0x00000001));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000004));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000018));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000018));
  ol32(u32(0x00064000));
  ol32(u32(0x00004000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000001));
  ol32(u32(0x00000201));

  // "_puts"
  ol32(u32(0x75705f00));
  ol32(u32(0x00007374));

  ol32(u32(0x00000000));

  // "_"
  ol32(u32(0x005f0100));
  ol32(u32(0x00000012));
  ol32(u32(0x00000200));
  ol32(u32(0xe0000300));
  ol32(u32(0x02000008));

  // "_mh_execute_header"
  // "main"
  ol32(u32(0x5f686d5f));
  ol32(u32(0x63657865));
  ol32(u32(0x5f657475));
  ol32(u32(0x64616568));
  ol32(u32(0x09007265));
  ol32(u32(0x6e69616d));

  ol32(u32(0x00000d00));
  ol32(u32(0x000008e0));
  ol32(u32(0x00000000));
  ol32(u32(0x00000002));
  ol32(u32(0x0010010f));
  ol32(u32(0x00000000));
  ol32(u32(0x00000001));
  ol32(u32(0x00000016));
  ol32(u32(0x0000010f));
  ol32(u32(0x00000460));
  ol32(u32(0x00000001));
  ol32(u32(0x0000001c));
  ol32(u32(0x01000001));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000002));
  ol32(u32(0x00000002));

  // "__mh_execute_header"
  // "_main"
  // "_puts"
  ol32(u32(0x5f5f0020));
  ol32(u32(0x655f686d));
  ol32(u32(0x75636578));
  ol32(u32(0x685f6574));
  ol32(u32(0x65646165));
  ol32(u32(0x6d5f0072));
  ol32(u32(0x006e6961));
  ol32(u32(0x7475705f));
  ol32(u32(0x00000073));

  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  ol32(u32(0xc00cdefa));
  ol32(u32(0x95010000));
  ol32(u32(0x01000000));
  ol32(u32(0x00000000));
  ol32(u32(0x14000000));

  ol32(u32(0x020cdefa));
  ol32(u32(0x81010000));
  ol32(u32(0x00040200));
  ol32(u32(0x02000200));
  ol32(u32(0x61000000));
  ol32(u32(0x58000000));
  ol32(u32(0x00000000));
  ol32(u32(0x09000000));
  ol32(u32(0x00810000));
  ol32(u32(0x0c000220));

  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));
  ol32(u32(0x00000000));

  ol32(u32(0x3c000000));
  ol32(u32(0x00000000));
  ol32(u32(0x01000000));

  // "reow"
  ol32(u32(0x776f6572));
  // ".bin"
  ol32(u32(0x6e69622e));

  ol32(u32(0xa3d84c00));
  ol32(u32(0xf17b0c0b));
  ol32(u32(0xed0e7b23));
  ol32(u32(0xc02a8a13));
  ol32(u32(0xfd8bf22a));
  ol32(u32(0x5c0dea5d));
  ol32(u32(0xa78ff427));
  ol32(u32(0xc21f4fc1));
  ol32(u32(0xac7fadf1));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xac7fada7));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xac7fada7));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xebd5dfa7));
  ol32(u32(0x6695f186));
  ol32(u32(0x062ca103));
  ol32(u32(0x1f63f436));
  ol32(u32(0x0b0df166));
  ol32(u32(0xa3eed4b8));
  ol32(u32(0xe0825bd2));
  ol32(u32(0xb40292e5));
  ol32(u32(0xac7faded));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xac7fada7));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xac7fada7));
  ol32(u32(0xc66f58b2));
  ol32(u32(0x04c066e9));
  ol32(u32(0x6bd1d1d7));
  ol32(u32(0x05584f02));
  ol32(u32(0x7cb47cff));
  ol32(u32(0xbdda857a));
  ol32(u32(0x2c89488b));
  ol32(u32(0xb72601a7));
  ol32(u32(0x5edb6ef7));
  ol32(u32(0x650adc99));
  ol32(u32(0x98549d4b));
  ol32(u32(0x5f8a3929));
  ol32(u32(0x946de112));
  ol32(u32(0x614d53eb));
  ol32(u32(0x3f1ecea2));

  ol32(u32(0x00000041));

        /*  U32 LC_SEGMENT_64 = u32(0x19);  */
        /*  U32 cmd = LC_SEGMENT_64;  */
        /*  ol32(cmd);  */
        /*    */
        /*  U32 cmdsize = u32(0x48);  */
        /*  ol32(cmdsize);  */
        /*    */
        /*  char const segname[16] = "__PAGEZERO\0\0\0\0\0\0";  */
        /*  o8s(i, sizeof segname, U8(segname[i]));  */
        /*    */
        /*  U64 vmaddr = u64(0x00000000'00000000);  */
        /*  ol64(vmaddr);  */
        /*    */
        /*  U64 vmsize = u64(0x00000001'00000000);  */
        /*  ol64(vmsize);  */
        /*    */
        /*  U64 fileoff = u64(0x00000000'00000000);  */
        /*  ol64(fileoff);  */
        /*    */
        /*  U64 filesize = u64(0x00000000'00000000);  */
        /*  ol64(filesize);  */
        /*    */
        /*  U32 VM_PROT_NONE = u32(0x00);  */
        /*  [[maybe_unused]] U32 VM_PROT_READ = u32(0x01);  */
        /*  [[maybe_unused]] U32 VM_PROT_NO_CHANGE_LEGACY = u32(0x08);  */
        /*  [[maybe_unused]] U32 VM_PROT_COPY = u32(0x10);  */
        /*    */
        /*  U32 maxprot = VM_PROT_NONE;  */
        /*  ol32(maxprot);  */
        /*    */
        /*  U32 initprot  */
        /*    //= VM_PROT_NONE;  */
        /*    = VM_PROT_READ  */
        /*    | VM_PROT_NO_CHANGE_LEGACY  */
        /*    | VM_PROT_COPY;  */
        /*  ol32(initprot);  */
        /*    */
        /*  [[maybe_unused]] U32 nsects = u32(0);  */
        /*  ol32(nsects);  */
        /*    */
        /*  [[maybe_unused]] U32 SG_HIGHVM               = u32(0x1);  */
        /*  [[maybe_unused]] U32 SG_FVMLIB               = u32(0x2);  */
        /*  [[maybe_unused]] U32 SG_NORELOC              = u32(0x4);  */
        /*  [[maybe_unused]] U32 SG_PROTECTED_VERSION_1  = u32(0x8);  */
        /*  [[maybe_unused]] U32 SG_READ_ONLY            = u32(0x10);  */
        /*    */
        /*  U32 flags = u32(0);  */
        /*  ol32(flags);  */

  end(mach_object, 0);
  end(fat_binary, 0);
  end(file, 0);

  assert(here >= &reow[0]);
  assert(here <= &reow[sizeof reow]);

#define warn(fmt, ...)                                          \
  fprintf(                                                      \
    stderr,                                                     \
    "nb: %s:%"LineFmt": warning: " fmt "\n",                    \
    __FILE__,                                                   \
    __LINE__ __VA_OPT__(,)                                      \
    __VA_ARGS__                                                 \
  )

  size_t const size = (size_t)(here - file_begin_0);
  if (size != sizeof reow) warn(
    "final size %zu is less than wanted size %zu",
    size,
    sizeof reow
  );
  fwrite((void *)&reow[0], 1, size, o);
  fclose(o);
  return 0;
}
