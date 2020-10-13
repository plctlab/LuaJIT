/*
** Definitions for RISCV CPUs.
** Copyright (C) 2005-2020 Mike Pall. See Copyright Notice in luajit.h
*/

#ifndef _LJ_TARGET_RISCV_H
#define _LJ_TARGET_RISCV_H

/* -- Registers IDs ------------------------------------------------------- */

#if LJ_ARCH_EMBEDDED
#define GPRDEF(_) \
  _(R0) _(RA) _(SP) _(R3) _(R4) _(R5) _(R6) _(R7) \
  _(R8) _(R9) _(R10) _(R11) _(R12) _(R13) _(R14) _(R15)
#else
#define GPRDEF(_) \
  _(R0) _(RA) _(SP) _(R3) _(R4) _(R5) _(R6) _(R7) \
  _(R8) _(R9) _(R10) _(R11) _(R12) _(R13) _(R14) _(R15) \
  _(R16) _(R17) _(R18) _(R19) _(R20) _(R21) _(R22) _(R23) \
  _(R24) _(R25) _(R26) _(R27) _(R28) _(R29) _(R30) _(R31) _(PC)
#endif
#if LJ_SOFTFP
#define FPRDEF(_)
#else
#define FPRDEF(_) \
  _(F0) _(F1) _(F2) _(F3) _(F4) _(F5) _(F6) _(F7) \
  _(F8) _(F9) _(F10) _(F11) _(F12) _(F13) _(F14) _(F15) \
  _(F16) _(F17) _(F18) _(F19) _(F20) _(F21) _(F22) _(F23) \
  _(F24) _(F25) _(F26) _(F27) _(F28) _(F29) _(F30) _(F31) _(FCSR)
#endif
#define VRIDDEF(_)

#define RIDENUM(name)	RID_##name,

enum {
  GPRDEF(RIDENUM)		/* General-purpose registers (GPRs). */
  FPRDEF(RIDENUM)		/* Floating-point registers (FPRs). */
  RID_MAX,
  RID_ZERO = RID_R0,
  RID_TMP = RID_RA,
  RID_GP = RID_R3,
  RID_TP = RID_R4,

  /* Calling conventions. */
  RID_RET = RID_R10,
#if LJ_LE
  RID_RETHI = RID_R11,
  RID_RETLO = RID_R10,
#else
  RID_RETHI = RID_R10,
  RID_RETLO = RID_R11,
#endif
#if LJ_SOFTFP
  RID_FPRET = RID_R10,
#else
  RID_FPRET = RID_F10,
#endif

  /* These definitions must match with the *.dasc file(s): */
  RID_BASE = RID_R18,		/* Interpreter BASE. */
  RID_LPC = RID_R20,		/* Interpreter PC. */
  RID_DISPATCH = RID_R21,	/* Interpreter DISPATCH table. */
  RID_LREG = RID_R22,		/* Interpreter L. */
  RID_JGL = RID_R23,		/* On-trace: global_State + 32768. */

  /* Register ranges [min, max) and number of registers. */
  RID_MIN_GPR = RID_R0,
  RID_MAX_GPR = RID_R31+1,
  RID_MIN_FPR = RID_MAX_GPR,
#if LJ_SOFTFP
  RID_MAX_FPR = RID_MIN_FPR,
#else
  RID_MAX_FPR = RID_F31+1,
#endif
  RID_NUM_GPR = RID_MAX_GPR - RID_MIN_GPR,
  RID_NUM_FPR = RID_MAX_FPR - RID_MIN_FPR	/* Only even regs are used. */
};

#define RID_NUM_KREF		RID_NUM_GPR
#define RID_MIN_KREF		RID_R0

/* -- Register sets ------------------------------------------------------- */

/* Make use of all registers, except ZERO, TMP, SP, GP, TP and JGL. */
#define RSET_FIXED \
  (RID2RSET(RID_ZERO)|RID2RSET(RID_TMP)|RID2RSET(RID_SP)|\
   RID2RSET(RID_GP)|RID2RSET(RID_TP)|RID2RSET(RID_JGL))
#define RSET_GPR	(RSET_RANGE(RID_MIN_GPR, RID_MAX_GPR) - RSET_FIXED)
#if LJ_SOFTFP
#define RSET_FPR	0
#else
#define RSET_FPR	RSET_RANGE(RID_MIN_FPR, RID_MAX_FPR)
#endif

#define RSET_ALL	(RSET_GPR|RSET_FPR)
#define RSET_INIT	RSET_ALL

#define RSET_SCRATCH_GPR \
  (RID2RSET(RID_R1)|RSET_RANGE(RID_R5, RID_R7)|\
   RSET_RANGE(RID_R10, RID_R17)|RSET_RANGE(RID_R28, RID_R31))

#if LJ_SOFTFP
#define RSET_SCRATCH_FPR	0
#else
#define RSET_SCRATCH_FPR \
  (RSET_RANGE(RID_F0, RID_F7)|RSET_RANGE(RID_F10, RID_F17)|\
   RSET_RANGE(RID_F28, RID_F31))
#endif
#define RSET_SCRATCH		(RSET_SCRATCH_GPR|RSET_SCRATCH_FPR)

#define REGARG_FIRSTGPR		RID_R10
#define REGARG_LASTGPR		RID_R17
#define REGARG_NUMGPR		8

#if LJ_ABI_SOFTFP
#define REGARG_FIRSTFPR		0
#define REGARG_LASTFPR		0
#define REGARG_NUMFPR		0
#else
#define REGARG_FIRSTFPR		RID_F10
#define REGARG_LASTFPR		RID_F17
#define REGARG_NUMFPR		8
#endif

/* -- Spill slots --------------------------------------------------------- */

/* Spill slots are 32 bit wide. An even/odd pair is used for FPRs.
**
** SPS_FIXED: Available fixed spill slots in interpreter frame.
** This definition must match with the *.dasc file(s).
**
** SPS_FIRST: First spill slot for general use.
*/
#if LJ_32
#define SPS_FIXED	5
#else
#define SPS_FIXED	4
#endif
#define SPS_FIRST	4

#define SPOFS_TMP	0

#define sps_scale(slot)		(4 * (int32_t)(slot))
#define sps_align(slot)		(((slot) - SPS_FIXED + 1) & ~1)

/* -- Exit state ---------------------------------------------------------- */
/* This definition must match with the *.dasc file(s). */
typedef struct {
#if !LJ_SOFTFP
  lua_Number fpr[RID_NUM_FPR];	/* Floating-point registers. */
#endif
  intptr_t gpr[RID_NUM_GPR];	/* General-purpose registers. */
  int32_t spill[256];		/* Spill slots. */
} ExitState;

/* Highest exit + 1 indicates stack check. */
#define EXITSTATE_CHECKEXIT	1

/* Return the address of a per-trace exit stub. */
static LJ_AINLINE uint32_t *exitstub_trace_addr_(uint32_t *p)
{
  while (*p == 0x00000000) p++;  /* Skip MIPSI_NOP. */
  return p;
}
/* Avoid dependence on lj_jit.h if only including lj_target.h. */
#define exitstub_trace_addr(T, exitno) \
  exitstub_trace_addr_((MCode *)((char *)(T)->mcode + (T)->szmcode))

/* -- Instructions -------------------------------------------------------- */

/* Instruction fields. */
#define RISCVF_D(d)	((d) << 7)
#define RISCVF_RS1(r)	((r) << 15)
#define RISCVF_RS2(r)	((r) << 20)

typedef enum RISCVIns {

  /* Type U */
  RISCVI_LUI = 0x00000037,
  RISCVI_AUIPC = 0x00000017,

  /* Type J */
  RISCVI_JAL = 0x0000006f,

  /* Integer instructions. */
  RISCVI_JALR = 0x00000067,

  RISCVI_ADDI = 0x00000013,
  RISCVI_SLTI = 0x00002013,
  RISCVI_SLTIU = 0x00003013,
  RISCVI_XORI = 0x00004013,
  RISCVI_ORI = 0x00006013,
  RISCVI_ANDI = 0x00007013,

  RISCVI_SLLI = 0x00001013,
  RISCVI_SRLI = 0x00005013,
  RISCVI_SRAI = 0x40005013,

  RISCVI_ADD = 0x00000033,
  RISCVI_SUB = 0x40000033,
  RISCVI_SLL = 0x00001033,
  RISCVI_SLT = 0x00002033,
  RISCVI_SLTU = 0x00003033,
  RISCVI_XOR = 0x00004033,
  RISCVI_SRL = 0x00005033,
  RISCVI_SRA = 0x40005033,
  RISCVI_OR = 0x00006033,
  RISCVI_AND = 0x00007033,

  /* Load/store instructions. */
  RISCVI_LB = 0x00000003,
  RISCVI_LH = 0x00001003,
  RISCVI_LW = 0x00002003,
  RISCVI_LBU = 0x00004003,
  RISCVI_LHU = 0x00005003,
  RISCVI_SB = 0x00000023,
  RISCVI_SH = 0x00001023,
  RISCVI_SW = 0x00002023,

  /* Branch instructions */
  RISCVI_BEQ = 0x00000063,
  RISCVI_BNE = 0x00001063,
  RISCVI_BLT = 0x00004063,
  RISCVI_BGE = 0x00005063,
  RISCVI_BLTU = 0x00006063,
  RISCVI_BGEU = 0x00007063,

  /* special instructions */
  RISCVI_FENCE = 0x0000000f,
  RISCVI_FENCE_I = 0x0000100f,
  RISCVI_ECALL = 0x00000073,
  RISCVI_EBREAK = 0x00100073,
  RISCVI_CSRRW = 0x00001073,
  RISCVI_CSRRS = 0x00002073,
  RISCVI_CSRRC = 0x00003073,
  RISCVI_CSRRWI = 0x00005073,
  RISCVI_CSRRSI = 0x00006073,
  RISCVI_CSRRCI = 0x00007073,


} RISCVIns;

#endif
