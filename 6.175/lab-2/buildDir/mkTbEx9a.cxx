/*
 * Generated by Bluespec Compiler, version 2023.01 (build 52adafa5)
 * 
 * On Sun Jan 28 16:09:31 UTC 2024
 * 
 */
#include "bluesim_primitives.h"
#include "mkTbEx9a.h"
#include "imported_BDPI_functions.h"


/* String declarations */
static std::string const __str_literal_2("    if signed: %0d * %0d DUT gave %0d", 37u);
static std::string const __str_literal_5("    if signed: %0d * %0d DUT gave %0d instead of %0d",
					 52u);
static std::string const __str_literal_3("    if unsigned: %0d * %0d DUT gave %0d", 39u);
static std::string const __str_literal_6("    if unsigned: %0d * %0d DUT gave %0d instead of %0d",
					 54u);
static std::string const __str_literal_4("FAILED case %0d", 15u);
static std::string const __str_literal_8("FAILED due to cycle limit", 25u);
static std::string const __str_literal_7("PASSED %0d test cases in %0d cycles", 35u);
static std::string const __str_literal_1("PASSED case %0d", 15u);


/* Constructor */
MOD_mkTbEx9a::MOD_mkTbEx9a(tSimStateHdl simHdl, char const *name, Module *parent)
  : Module(simHdl, name, parent),
    __clk_handle_0(BAD_CLOCK_HANDLE),
    INST_dut_busy(simHdl, "dut_busy", this, 1u, (tUInt8)0u, (tUInt8)0u),
    INST_dut_i(simHdl, "dut_i", this, 4u, (tUInt8)0u, (tUInt8)0u),
    INST_dut_m_neg(simHdl, "dut_m_neg", this, 18u, 0u, (tUInt8)0u),
    INST_dut_m_pos(simHdl, "dut_m_pos", this, 18u, 0u, (tUInt8)0u),
    INST_dut_p(simHdl, "dut_p", this, 18u, 0u, (tUInt8)0u),
    INST_tb_cycle(simHdl, "tb_cycle", this, 32u, 0u, (tUInt8)0u),
    INST_tb_feed_count(simHdl, "tb_feed_count", this, 32u, 0u, (tUInt8)0u),
    INST_tb_operands_fifo(simHdl, "tb_operands_fifo", this, 16u, 4u, (tUInt8)1u, 0u),
    INST_tb_randomA_ignore(simHdl, "tb_randomA_ignore", this, 8u, (tUInt8)0u),
    INST_tb_randomA_initialized(simHdl, "tb_randomA_initialized", this, 1u, (tUInt8)0u, (tUInt8)0u),
    INST_tb_randomA_zaz(simHdl, "tb_randomA_zaz", this, 8u, (tUInt8)0u),
    INST_tb_randomB_ignore(simHdl, "tb_randomB_ignore", this, 8u, (tUInt8)0u),
    INST_tb_randomB_initialized(simHdl, "tb_randomB_initialized", this, 1u, (tUInt8)0u, (tUInt8)0u),
    INST_tb_randomB_zaz(simHdl, "tb_randomB_zaz", this, 8u, (tUInt8)0u),
    INST_tb_read_count(simHdl, "tb_read_count", this, 32u, 0u, (tUInt8)0u),
    PORT_RST_N((tUInt8)1u),
    DEF_v__h1262(2863311530u),
    DEF_v__h885(2863311530u)
{
  symbol_count = 46u;
  symbols = new tSym[symbol_count];
  init_symbols_0();
}


/* Symbol init fns */

void MOD_mkTbEx9a::init_symbols_0()
{
  init_symbol(&symbols[0u],
	      "CAN_FIRE_RL_dut_booth_step",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_dut_booth_step,
	      1u);
  init_symbol(&symbols[1u], "CAN_FIRE_RL_tb_feed", SYM_DEF, &DEF_CAN_FIRE_RL_tb_feed, 1u);
  init_symbol(&symbols[2u],
	      "CAN_FIRE_RL_tb_monitor_test",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_tb_monitor_test,
	      1u);
  init_symbol(&symbols[3u],
	      "CAN_FIRE_RL_tb_randomA_every",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_tb_randomA_every,
	      1u);
  init_symbol(&symbols[4u],
	      "CAN_FIRE_RL_tb_randomA_every_1",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_tb_randomA_every_1,
	      1u);
  init_symbol(&symbols[5u],
	      "CAN_FIRE_RL_tb_randomB_every",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_tb_randomB_every,
	      1u);
  init_symbol(&symbols[6u],
	      "CAN_FIRE_RL_tb_randomB_every_1",
	      SYM_DEF,
	      &DEF_CAN_FIRE_RL_tb_randomB_every_1,
	      1u);
  init_symbol(&symbols[7u], "CAN_FIRE_RL_tb_read", SYM_DEF, &DEF_CAN_FIRE_RL_tb_read, 1u);
  init_symbol(&symbols[8u], "dut_busy", SYM_MODULE, &INST_dut_busy);
  init_symbol(&symbols[9u], "dut_i", SYM_MODULE, &INST_dut_i);
  init_symbol(&symbols[10u], "dut_m_neg", SYM_MODULE, &INST_dut_m_neg);
  init_symbol(&symbols[11u], "dut_m_pos", SYM_MODULE, &INST_dut_m_pos);
  init_symbol(&symbols[12u], "dut_p", SYM_MODULE, &INST_dut_p);
  init_symbol(&symbols[13u], "RL_dut_booth_step", SYM_RULE);
  init_symbol(&symbols[14u], "RL_tb_feed", SYM_RULE);
  init_symbol(&symbols[15u], "RL_tb_monitor_test", SYM_RULE);
  init_symbol(&symbols[16u], "RL_tb_randomA_every", SYM_RULE);
  init_symbol(&symbols[17u], "RL_tb_randomA_every_1", SYM_RULE);
  init_symbol(&symbols[18u], "RL_tb_randomB_every", SYM_RULE);
  init_symbol(&symbols[19u], "RL_tb_randomB_every_1", SYM_RULE);
  init_symbol(&symbols[20u], "RL_tb_read", SYM_RULE);
  init_symbol(&symbols[21u], "tb_cycle", SYM_MODULE, &INST_tb_cycle);
  init_symbol(&symbols[22u], "tb_feed_count", SYM_MODULE, &INST_tb_feed_count);
  init_symbol(&symbols[23u], "tb_operands_fifo", SYM_MODULE, &INST_tb_operands_fifo);
  init_symbol(&symbols[24u], "tb_randomA_ignore", SYM_MODULE, &INST_tb_randomA_ignore);
  init_symbol(&symbols[25u], "tb_randomA_initialized", SYM_MODULE, &INST_tb_randomA_initialized);
  init_symbol(&symbols[26u], "tb_randomA_zaz", SYM_MODULE, &INST_tb_randomA_zaz);
  init_symbol(&symbols[27u], "tb_randomB_ignore", SYM_MODULE, &INST_tb_randomB_ignore);
  init_symbol(&symbols[28u], "tb_randomB_initialized", SYM_MODULE, &INST_tb_randomB_initialized);
  init_symbol(&symbols[29u], "tb_randomB_zaz", SYM_MODULE, &INST_tb_randomB_zaz);
  init_symbol(&symbols[30u], "tb_read_count", SYM_MODULE, &INST_tb_read_count);
  init_symbol(&symbols[31u], "v__h1335", SYM_DEF, &DEF_v__h1335, 8u);
  init_symbol(&symbols[32u], "v__h959", SYM_DEF, &DEF_v__h959, 8u);
  init_symbol(&symbols[33u],
	      "WILL_FIRE_RL_dut_booth_step",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_dut_booth_step,
	      1u);
  init_symbol(&symbols[34u], "WILL_FIRE_RL_tb_feed", SYM_DEF, &DEF_WILL_FIRE_RL_tb_feed, 1u);
  init_symbol(&symbols[35u],
	      "WILL_FIRE_RL_tb_monitor_test",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_tb_monitor_test,
	      1u);
  init_symbol(&symbols[36u],
	      "WILL_FIRE_RL_tb_randomA_every",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_tb_randomA_every,
	      1u);
  init_symbol(&symbols[37u],
	      "WILL_FIRE_RL_tb_randomA_every_1",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_tb_randomA_every_1,
	      1u);
  init_symbol(&symbols[38u],
	      "WILL_FIRE_RL_tb_randomB_every",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_tb_randomB_every,
	      1u);
  init_symbol(&symbols[39u],
	      "WILL_FIRE_RL_tb_randomB_every_1",
	      SYM_DEF,
	      &DEF_WILL_FIRE_RL_tb_randomB_every_1,
	      1u);
  init_symbol(&symbols[40u], "WILL_FIRE_RL_tb_read", SYM_DEF, &DEF_WILL_FIRE_RL_tb_read, 1u);
  init_symbol(&symbols[41u], "x__h1932", SYM_DEF, &DEF_x__h1932, 32u);
  init_symbol(&symbols[42u], "x__h2488", SYM_DEF, &DEF_x__h2488, 32u);
  init_symbol(&symbols[43u], "x__h417", SYM_DEF, &DEF_x__h417, 4u);
  init_symbol(&symbols[44u], "x_wget__h1205", SYM_DEF, &DEF_x_wget__h1205, 8u);
  init_symbol(&symbols[45u], "x_wget__h828", SYM_DEF, &DEF_x_wget__h828, 8u);
}


/* Rule actions */

void MOD_mkTbEx9a::RL_dut_booth_step()
{
  tUInt8 DEF_x__h413;
  tUInt32 DEF_x__h247;
  tUInt32 DEF_p_next__h354;
  tUInt32 DEF_p_next__h381;
  tUInt32 DEF_p_next__h343;
  tUInt32 DEF_p_next__h332;
  tUInt32 DEF_a__h268;
  tUInt8 DEF_pr__h232;
  tUInt32 DEF_dut_m_neg_BITS_16_TO_0___h403;
  tUInt32 DEF_dut_m_pos_BITS_16_TO_0___h376;
  tUInt32 DEF__read__h57;
  tUInt32 DEF__read__h90;
  DEF_dut_p__h2034 = INST_dut_p.METH_read();
  DEF__read__h90 = INST_dut_m_neg.METH_read();
  DEF__read__h57 = INST_dut_m_pos.METH_read();
  DEF_x__h417 = INST_dut_i.METH_read();
  DEF_dut_m_pos_BITS_16_TO_0___h376 = (tUInt32)(131071u & DEF__read__h57);
  DEF_dut_m_neg_BITS_16_TO_0___h403 = (tUInt32)(131071u & DEF__read__h90);
  DEF_pr__h232 = (tUInt8)((tUInt8)7u & DEF_dut_p__h2034);
  DEF_p_next__h332 = 262143u & (DEF_dut_p__h2034 + DEF__read__h57);
  DEF_p_next__h343 = 262143u & (DEF_dut_p__h2034 + DEF__read__h90);
  DEF_p_next__h381 = 262143u & (DEF_dut_p__h2034 + (262143u & ((DEF_dut_m_neg_BITS_16_TO_0___h403 << 1u) | (tUInt32)((tUInt8)0u))));
  DEF_p_next__h354 = 262143u & (DEF_dut_p__h2034 + (262143u & ((DEF_dut_m_pos_BITS_16_TO_0___h376 << 1u) | (tUInt32)((tUInt8)0u))));
  switch (DEF_pr__h232) {
  case (tUInt8)1u:
  case (tUInt8)2u:
    DEF_a__h268 = DEF_p_next__h332;
    break;
  case (tUInt8)5u:
  case (tUInt8)6u:
    DEF_a__h268 = DEF_p_next__h343;
    break;
  case (tUInt8)3u:
    DEF_a__h268 = DEF_p_next__h354;
    break;
  case (tUInt8)4u:
    DEF_a__h268 = DEF_p_next__h381;
    break;
  default:
    DEF_a__h268 = DEF_dut_p__h2034;
  }
  DEF_x__h247 = primShiftRA32(18u, 18u, (tUInt32)(DEF_a__h268), 32u, 2u);
  DEF_x__h413 = (tUInt8)15u & (DEF_x__h417 + (tUInt8)1u);
  INST_dut_p.METH_write(DEF_x__h247);
  INST_dut_i.METH_write(DEF_x__h413);
}

void MOD_mkTbEx9a::RL_tb_randomA_every()
{
  tUInt8 DEF_new_value__h927;
  if (!(PORT_RST_N == (tUInt8)0u))
    DEF_v__h885 = rand32();
  DEF_new_value__h927 = (tUInt8)((tUInt8)255u & DEF_v__h885);
  INST_tb_randomA_zaz.METH_wset(DEF_new_value__h927);
}

void MOD_mkTbEx9a::RL_tb_randomA_every_1()
{
  DEF_x_wget__h828 = INST_tb_randomA_zaz.METH_wget();
  DEF_tb_randomA_zaz_whas____d33 = INST_tb_randomA_zaz.METH_whas();
  DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 = DEF_x_wget__h828;
  DEF_v__h959 = DEF_tb_randomA_zaz_whas____d33 ? DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 : (tUInt8)0u;
  INST_tb_randomA_ignore.METH_wset(DEF_v__h959);
}

void MOD_mkTbEx9a::RL_tb_randomB_every()
{
  tUInt8 DEF_new_value__h1304;
  if (!(PORT_RST_N == (tUInt8)0u))
    DEF_v__h1262 = rand32();
  DEF_new_value__h1304 = (tUInt8)((tUInt8)255u & DEF_v__h1262);
  INST_tb_randomB_zaz.METH_wset(DEF_new_value__h1304);
}

void MOD_mkTbEx9a::RL_tb_randomB_every_1()
{
  DEF_x_wget__h1205 = INST_tb_randomB_zaz.METH_wget();
  DEF_v__h1335 = INST_tb_randomB_zaz.METH_whas() ? DEF_x_wget__h1205 : (tUInt8)0u;
  INST_tb_randomB_ignore.METH_wset(DEF_v__h1335);
}

void MOD_mkTbEx9a::RL_tb_feed()
{
  tUInt32 DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d61;
  tUInt32 DEF_x__h1767;
  tUInt32 DEF_x__h1642;
  tUInt32 DEF_x__h1889;
  tUInt32 DEF_x__h1913;
  tUInt8 DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60;
  tUInt8 DEF__1__h1727;
  tUInt8 DEF_IF_tb_randomA_zaz_whas__3_THEN_NEG_IF_tb_rando_ETC___d65;
  tUInt8 DEF__1__h1843;
  DEF_x__h1932 = INST_tb_feed_count.METH_read();
  DEF_x_wget__h1205 = INST_tb_randomB_zaz.METH_wget();
  DEF_x_wget__h828 = INST_tb_randomA_zaz.METH_wget();
  DEF_tb_randomA_zaz_whas____d33 = INST_tb_randomA_zaz.METH_whas();
  DEF_v__h1335 = INST_tb_randomB_zaz.METH_whas() ? DEF_x_wget__h1205 : (tUInt8)0u;
  DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 = DEF_x_wget__h828;
  DEF_IF_tb_randomA_zaz_whas__3_THEN_NEG_IF_tb_rando_ETC___d65 = DEF_tb_randomA_zaz_whas____d33 ? (tUInt8)255u & -DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 : (tUInt8)0u;
  DEF__1__h1843 = (tUInt8)(DEF_IF_tb_randomA_zaz_whas__3_THEN_NEG_IF_tb_rando_ETC___d65 >> 7u);
  DEF_v__h959 = DEF_tb_randomA_zaz_whas____d33 ? DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 : (tUInt8)0u;
  DEF__1__h1727 = (tUInt8)(DEF_v__h959 >> 7u);
  DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44 = DEF_v__h959 == (tUInt8)128u;
  DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45 = DEF_v__h1335 == (tUInt8)128u;
  DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60 = !DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44 && !DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45;
  DEF_x__h1913 = DEF_x__h1932 + 1u;
  DEF_x__h1642 = 262143u & ((((tUInt32)(DEF__1__h1727)) << 17u) | (((tUInt32)(DEF_v__h959)) << 9u));
  DEF_x__h1889 = 262143u & ((((tUInt32)(DEF_v__h1335)) << 1u) | (tUInt32)((tUInt8)0u));
  DEF_x__h1767 = 262143u & ((((tUInt32)(DEF__1__h1843)) << 17u) | (((tUInt32)(DEF_IF_tb_randomA_zaz_whas__3_THEN_NEG_IF_tb_rando_ETC___d65)) << 9u));
  DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d61 = 65535u & ((((tUInt32)(DEF_v__h959)) << 8u) | (tUInt32)(DEF_v__h1335));
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_tb_operands_fifo.METH_enq(DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d61);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_dut_busy.METH_write((tUInt8)1u);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_dut_i.METH_write((tUInt8)0u);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_dut_m_pos.METH_write(DEF_x__h1642);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_dut_m_neg.METH_write(DEF_x__h1767);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_dut_p.METH_write(DEF_x__h1889);
  if (DEF_NOT_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_rando_ETC___d60)
    INST_tb_feed_count.METH_write(DEF_x__h1913);
}

void MOD_mkTbEx9a::RL_tb_read()
{
  tUInt32 DEF_x__h2364;
  tUInt8 DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89;
  tUInt32 DEF_tb_operands_fifo_first____d78;
  tUInt8 DEF_b__h1952;
  tUInt8 DEF_signed_tb_operands_fifo_first__8_BITS_7_TO_0_1___d87;
  tUInt8 DEF_a__h1951;
  tUInt8 DEF_signed_tb_operands_fifo_first__8_BITS_15_TO_8_9___d86;
  tUInt32 DEF_v__h1976;
  tUInt32 DEF_signed_dut_p_BITS_16_TO_1_7___d88;
  tUInt32 DEF_expected__h2039;
  tUInt32 DEF_signed_SEXT_tb_operands_fifo_first__8_BITS_15_ETC___d90;
  tUInt8 DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85;
  DEF_x__h2488 = INST_tb_read_count.METH_read();
  DEF_dut_p__h2034 = INST_dut_p.METH_read();
  DEF_v__h1976 = (tUInt32)(65535u & (DEF_dut_p__h2034 >> 1u));
  DEF_signed_dut_p_BITS_16_TO_1_7___d88 = DEF_v__h1976;
  DEF_tb_operands_fifo_first____d78 = INST_tb_operands_fifo.METH_first();
  DEF_a__h1951 = (tUInt8)(DEF_tb_operands_fifo_first____d78 >> 8u);
  DEF_signed_tb_operands_fifo_first__8_BITS_15_TO_8_9___d86 = DEF_a__h1951;
  DEF_b__h1952 = (tUInt8)((tUInt8)255u & DEF_tb_operands_fifo_first____d78);
  DEF_expected__h2039 = (tUInt32)(65535u & (primSignExt32(16u,
							  8u,
							  (tUInt8)(DEF_a__h1951)) * primSignExt32(16u,
												  8u,
												  (tUInt8)(DEF_b__h1952))));
  DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85 = DEF_v__h1976 == DEF_expected__h2039;
  DEF_signed_SEXT_tb_operands_fifo_first__8_BITS_15_ETC___d90 = DEF_expected__h2039;
  DEF_signed_tb_operands_fifo_first__8_BITS_7_TO_0_1___d87 = DEF_b__h1952;
  DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89 = !DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85;
  DEF_x__h2364 = DEF_x__h2488 + 1u;
  INST_tb_operands_fifo.METH_deq();
  INST_dut_busy.METH_write((tUInt8)0u);
  if (!(PORT_RST_N == (tUInt8)0u))
  {
    if (DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85)
      dollar_display(sim_hdl, this, "s,32", &__str_literal_1, DEF_x__h2488);
    if (DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85)
      dollar_display(sim_hdl,
		     this,
		     "s,-8,-8,-16",
		     &__str_literal_2,
		     DEF_signed_tb_operands_fifo_first__8_BITS_15_TO_8_9___d86,
		     DEF_signed_tb_operands_fifo_first__8_BITS_7_TO_0_1___d87,
		     DEF_signed_dut_p_BITS_16_TO_1_7___d88);
    if (DEF_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_fifo__ETC___d85)
      dollar_display(sim_hdl,
		     this,
		     "s,8,8,16",
		     &__str_literal_3,
		     DEF_a__h1951,
		     DEF_b__h1952,
		     DEF_v__h1976);
    if (DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89)
      dollar_display(sim_hdl, this, "s,32", &__str_literal_4, DEF_x__h2488);
    if (DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89)
      dollar_display(sim_hdl,
		     this,
		     "s,-8,-8,-16,-16",
		     &__str_literal_5,
		     DEF_signed_tb_operands_fifo_first__8_BITS_15_TO_8_9___d86,
		     DEF_signed_tb_operands_fifo_first__8_BITS_7_TO_0_1___d87,
		     DEF_signed_dut_p_BITS_16_TO_1_7___d88,
		     DEF_signed_SEXT_tb_operands_fifo_first__8_BITS_15_ETC___d90);
    if (DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89)
      dollar_display(sim_hdl,
		     this,
		     "s,8,8,16,16",
		     &__str_literal_6,
		     DEF_a__h1951,
		     DEF_b__h1952,
		     DEF_v__h1976,
		     DEF_expected__h2039);
    if (DEF_NOT_dut_p_BITS_16_TO_1_7_EQ_SEXT_tb_operands_f_ETC___d89)
      dollar_finish(sim_hdl, "32", 1u);
  }
  INST_tb_read_count.METH_write(DEF_x__h2364);
}

void MOD_mkTbEx9a::RL_tb_monitor_test()
{
  tUInt32 DEF_x__h2717;
  tUInt8 DEF_tb_cycle_2_EQ_0___d93;
  tUInt8 DEF_tb_cycle_2_EQ_16384___d94;
  tUInt32 DEF_x__h2721;
  DEF_x__h2488 = INST_tb_read_count.METH_read();
  DEF_x__h2721 = INST_tb_cycle.METH_read();
  DEF_tb_cycle_2_EQ_16384___d94 = DEF_x__h2721 == 16384u;
  DEF_tb_cycle_2_EQ_0___d93 = DEF_x__h2721 == 0u;
  DEF_tb_read_count_1_EQ_128___d72 = DEF_x__h2488 == 128u;
  DEF_x__h2717 = DEF_x__h2721 + 1u;
  if (DEF_tb_cycle_2_EQ_0___d93)
    INST_tb_randomA_initialized.METH_write((tUInt8)1u);
  if (DEF_tb_cycle_2_EQ_0___d93)
    INST_tb_randomB_initialized.METH_write((tUInt8)1u);
  if (!(PORT_RST_N == (tUInt8)0u))
  {
    if (DEF_tb_read_count_1_EQ_128___d72)
      dollar_display(sim_hdl, this, "s,32,32", &__str_literal_7, DEF_x__h2488, DEF_x__h2721);
    if (DEF_tb_read_count_1_EQ_128___d72)
      dollar_finish(sim_hdl, "32", 1u);
    if (DEF_tb_cycle_2_EQ_16384___d94)
      dollar_display(sim_hdl, this, "s", &__str_literal_8);
    if (DEF_tb_cycle_2_EQ_16384___d94)
      dollar_finish(sim_hdl, "32", 1u);
  }
  INST_tb_cycle.METH_write(DEF_x__h2717);
}


/* Methods */


/* Reset routines */

void MOD_mkTbEx9a::reset_RST_N(tUInt8 ARG_rst_in)
{
  PORT_RST_N = ARG_rst_in;
  INST_tb_read_count.reset_RST(ARG_rst_in);
  INST_tb_randomB_initialized.reset_RST(ARG_rst_in);
  INST_tb_randomA_initialized.reset_RST(ARG_rst_in);
  INST_tb_operands_fifo.reset_RST(ARG_rst_in);
  INST_tb_feed_count.reset_RST(ARG_rst_in);
  INST_tb_cycle.reset_RST(ARG_rst_in);
  INST_dut_p.reset_RST(ARG_rst_in);
  INST_dut_m_pos.reset_RST(ARG_rst_in);
  INST_dut_m_neg.reset_RST(ARG_rst_in);
  INST_dut_i.reset_RST(ARG_rst_in);
  INST_dut_busy.reset_RST(ARG_rst_in);
}


/* Static handles to reset routines */


/* Functions for the parent module to register its reset fns */


/* Functions to set the elaborated clock id */

void MOD_mkTbEx9a::set_clk_0(char const *s)
{
  __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
}


/* State dumping routine */
void MOD_mkTbEx9a::dump_state(unsigned int indent)
{
  printf("%*s%s:\n", indent, "", inst_name);
  INST_dut_busy.dump_state(indent + 2u);
  INST_dut_i.dump_state(indent + 2u);
  INST_dut_m_neg.dump_state(indent + 2u);
  INST_dut_m_pos.dump_state(indent + 2u);
  INST_dut_p.dump_state(indent + 2u);
  INST_tb_cycle.dump_state(indent + 2u);
  INST_tb_feed_count.dump_state(indent + 2u);
  INST_tb_operands_fifo.dump_state(indent + 2u);
  INST_tb_randomA_ignore.dump_state(indent + 2u);
  INST_tb_randomA_initialized.dump_state(indent + 2u);
  INST_tb_randomA_zaz.dump_state(indent + 2u);
  INST_tb_randomB_ignore.dump_state(indent + 2u);
  INST_tb_randomB_initialized.dump_state(indent + 2u);
  INST_tb_randomB_zaz.dump_state(indent + 2u);
  INST_tb_read_count.dump_state(indent + 2u);
}


/* VCD dumping routines */

unsigned int MOD_mkTbEx9a::dump_VCD_defs(unsigned int levels)
{
  vcd_write_scope_start(sim_hdl, inst_name);
  vcd_num = vcd_reserve_ids(sim_hdl, 47u);
  unsigned int num = vcd_num;
  for (unsigned int clk = 0u; clk < bk_num_clocks(sim_hdl); ++clk)
    vcd_add_clock_def(sim_hdl, this, bk_clock_name(sim_hdl, clk), bk_clock_vcd_num(sim_hdl, clk));
  vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_dut_booth_step", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_feed", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_monitor_test", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_randomA_every", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_randomA_every_1", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_randomB_every", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_randomB_every_1", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_RL_tb_read", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35", 8u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45", 1u);
  vcd_write_def(sim_hdl, num++, "RST_N", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_dut_booth_step", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_feed", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_monitor_test", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_randomA_every", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_randomA_every_1", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_randomB_every", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_randomB_every_1", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "WILL_FIRE_RL_tb_read", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "dut_p__h2034", 18u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "tb_randomA_zaz_whas____d33", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "tb_read_count_1_EQ_128___d72", 1u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "v__h1262", 32u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "v__h1335", 8u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "v__h885", 32u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "v__h959", 8u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "x__h1932", 32u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "x__h2488", 32u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "x__h417", 4u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "x_wget__h1205", 8u);
  vcd_set_clock(sim_hdl, num, __clk_handle_0);
  vcd_write_def(sim_hdl, num++, "x_wget__h828", 8u);
  num = INST_dut_busy.dump_VCD_defs(num);
  num = INST_dut_i.dump_VCD_defs(num);
  num = INST_dut_m_neg.dump_VCD_defs(num);
  num = INST_dut_m_pos.dump_VCD_defs(num);
  num = INST_dut_p.dump_VCD_defs(num);
  num = INST_tb_cycle.dump_VCD_defs(num);
  num = INST_tb_feed_count.dump_VCD_defs(num);
  num = INST_tb_operands_fifo.dump_VCD_defs(num);
  num = INST_tb_randomA_ignore.dump_VCD_defs(num);
  num = INST_tb_randomA_initialized.dump_VCD_defs(num);
  num = INST_tb_randomA_zaz.dump_VCD_defs(num);
  num = INST_tb_randomB_ignore.dump_VCD_defs(num);
  num = INST_tb_randomB_initialized.dump_VCD_defs(num);
  num = INST_tb_randomB_zaz.dump_VCD_defs(num);
  num = INST_tb_read_count.dump_VCD_defs(num);
  vcd_write_scope_end(sim_hdl);
  return num;
}

void MOD_mkTbEx9a::dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_mkTbEx9a &backing)
{
  vcd_defs(dt, backing);
  vcd_prims(dt, backing);
}

void MOD_mkTbEx9a::vcd_defs(tVCDDumpType dt, MOD_mkTbEx9a &backing)
{
  unsigned int num = vcd_num;
  if (dt == VCD_DUMP_XS)
  {
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 8u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 18u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 8u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 8u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 4u);
    vcd_write_x(sim_hdl, num++, 8u);
    vcd_write_x(sim_hdl, num++, 8u);
  }
  else
    if (dt == VCD_DUMP_CHANGES)
    {
      if ((backing.DEF_CAN_FIRE_RL_dut_booth_step) != DEF_CAN_FIRE_RL_dut_booth_step)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_dut_booth_step, 1u);
	backing.DEF_CAN_FIRE_RL_dut_booth_step = DEF_CAN_FIRE_RL_dut_booth_step;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_feed) != DEF_CAN_FIRE_RL_tb_feed)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_feed, 1u);
	backing.DEF_CAN_FIRE_RL_tb_feed = DEF_CAN_FIRE_RL_tb_feed;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_monitor_test) != DEF_CAN_FIRE_RL_tb_monitor_test)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_monitor_test, 1u);
	backing.DEF_CAN_FIRE_RL_tb_monitor_test = DEF_CAN_FIRE_RL_tb_monitor_test;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_randomA_every) != DEF_CAN_FIRE_RL_tb_randomA_every)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_randomA_every, 1u);
	backing.DEF_CAN_FIRE_RL_tb_randomA_every = DEF_CAN_FIRE_RL_tb_randomA_every;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_randomA_every_1) != DEF_CAN_FIRE_RL_tb_randomA_every_1)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_randomA_every_1, 1u);
	backing.DEF_CAN_FIRE_RL_tb_randomA_every_1 = DEF_CAN_FIRE_RL_tb_randomA_every_1;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_randomB_every) != DEF_CAN_FIRE_RL_tb_randomB_every)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_randomB_every, 1u);
	backing.DEF_CAN_FIRE_RL_tb_randomB_every = DEF_CAN_FIRE_RL_tb_randomB_every;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_randomB_every_1) != DEF_CAN_FIRE_RL_tb_randomB_every_1)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_randomB_every_1, 1u);
	backing.DEF_CAN_FIRE_RL_tb_randomB_every_1 = DEF_CAN_FIRE_RL_tb_randomB_every_1;
      }
      ++num;
      if ((backing.DEF_CAN_FIRE_RL_tb_read) != DEF_CAN_FIRE_RL_tb_read)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_RL_tb_read, 1u);
	backing.DEF_CAN_FIRE_RL_tb_read = DEF_CAN_FIRE_RL_tb_read;
      }
      ++num;
      if ((backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44) != DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44)
      {
	vcd_write_val(sim_hdl, num, DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44, 1u);
	backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44 = DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44;
      }
      ++num;
      if ((backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35) != DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35)
      {
	vcd_write_val(sim_hdl, num, DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35, 8u);
	backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 = DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35;
      }
      ++num;
      if ((backing.DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45) != DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45)
      {
	vcd_write_val(sim_hdl, num, DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45, 1u);
	backing.DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45 = DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45;
      }
      ++num;
      if ((backing.PORT_RST_N) != PORT_RST_N)
      {
	vcd_write_val(sim_hdl, num, PORT_RST_N, 1u);
	backing.PORT_RST_N = PORT_RST_N;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_dut_booth_step) != DEF_WILL_FIRE_RL_dut_booth_step)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_dut_booth_step, 1u);
	backing.DEF_WILL_FIRE_RL_dut_booth_step = DEF_WILL_FIRE_RL_dut_booth_step;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_feed) != DEF_WILL_FIRE_RL_tb_feed)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_feed, 1u);
	backing.DEF_WILL_FIRE_RL_tb_feed = DEF_WILL_FIRE_RL_tb_feed;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_monitor_test) != DEF_WILL_FIRE_RL_tb_monitor_test)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_monitor_test, 1u);
	backing.DEF_WILL_FIRE_RL_tb_monitor_test = DEF_WILL_FIRE_RL_tb_monitor_test;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_randomA_every) != DEF_WILL_FIRE_RL_tb_randomA_every)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_randomA_every, 1u);
	backing.DEF_WILL_FIRE_RL_tb_randomA_every = DEF_WILL_FIRE_RL_tb_randomA_every;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_randomA_every_1) != DEF_WILL_FIRE_RL_tb_randomA_every_1)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_randomA_every_1, 1u);
	backing.DEF_WILL_FIRE_RL_tb_randomA_every_1 = DEF_WILL_FIRE_RL_tb_randomA_every_1;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_randomB_every) != DEF_WILL_FIRE_RL_tb_randomB_every)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_randomB_every, 1u);
	backing.DEF_WILL_FIRE_RL_tb_randomB_every = DEF_WILL_FIRE_RL_tb_randomB_every;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_randomB_every_1) != DEF_WILL_FIRE_RL_tb_randomB_every_1)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_randomB_every_1, 1u);
	backing.DEF_WILL_FIRE_RL_tb_randomB_every_1 = DEF_WILL_FIRE_RL_tb_randomB_every_1;
      }
      ++num;
      if ((backing.DEF_WILL_FIRE_RL_tb_read) != DEF_WILL_FIRE_RL_tb_read)
      {
	vcd_write_val(sim_hdl, num, DEF_WILL_FIRE_RL_tb_read, 1u);
	backing.DEF_WILL_FIRE_RL_tb_read = DEF_WILL_FIRE_RL_tb_read;
      }
      ++num;
      if ((backing.DEF_dut_p__h2034) != DEF_dut_p__h2034)
      {
	vcd_write_val(sim_hdl, num, DEF_dut_p__h2034, 18u);
	backing.DEF_dut_p__h2034 = DEF_dut_p__h2034;
      }
      ++num;
      if ((backing.DEF_tb_randomA_zaz_whas____d33) != DEF_tb_randomA_zaz_whas____d33)
      {
	vcd_write_val(sim_hdl, num, DEF_tb_randomA_zaz_whas____d33, 1u);
	backing.DEF_tb_randomA_zaz_whas____d33 = DEF_tb_randomA_zaz_whas____d33;
      }
      ++num;
      if ((backing.DEF_tb_read_count_1_EQ_128___d72) != DEF_tb_read_count_1_EQ_128___d72)
      {
	vcd_write_val(sim_hdl, num, DEF_tb_read_count_1_EQ_128___d72, 1u);
	backing.DEF_tb_read_count_1_EQ_128___d72 = DEF_tb_read_count_1_EQ_128___d72;
      }
      ++num;
      if ((backing.DEF_v__h1262) != DEF_v__h1262)
      {
	vcd_write_val(sim_hdl, num, DEF_v__h1262, 32u);
	backing.DEF_v__h1262 = DEF_v__h1262;
      }
      ++num;
      if ((backing.DEF_v__h1335) != DEF_v__h1335)
      {
	vcd_write_val(sim_hdl, num, DEF_v__h1335, 8u);
	backing.DEF_v__h1335 = DEF_v__h1335;
      }
      ++num;
      if ((backing.DEF_v__h885) != DEF_v__h885)
      {
	vcd_write_val(sim_hdl, num, DEF_v__h885, 32u);
	backing.DEF_v__h885 = DEF_v__h885;
      }
      ++num;
      if ((backing.DEF_v__h959) != DEF_v__h959)
      {
	vcd_write_val(sim_hdl, num, DEF_v__h959, 8u);
	backing.DEF_v__h959 = DEF_v__h959;
      }
      ++num;
      if ((backing.DEF_x__h1932) != DEF_x__h1932)
      {
	vcd_write_val(sim_hdl, num, DEF_x__h1932, 32u);
	backing.DEF_x__h1932 = DEF_x__h1932;
      }
      ++num;
      if ((backing.DEF_x__h2488) != DEF_x__h2488)
      {
	vcd_write_val(sim_hdl, num, DEF_x__h2488, 32u);
	backing.DEF_x__h2488 = DEF_x__h2488;
      }
      ++num;
      if ((backing.DEF_x__h417) != DEF_x__h417)
      {
	vcd_write_val(sim_hdl, num, DEF_x__h417, 4u);
	backing.DEF_x__h417 = DEF_x__h417;
      }
      ++num;
      if ((backing.DEF_x_wget__h1205) != DEF_x_wget__h1205)
      {
	vcd_write_val(sim_hdl, num, DEF_x_wget__h1205, 8u);
	backing.DEF_x_wget__h1205 = DEF_x_wget__h1205;
      }
      ++num;
      if ((backing.DEF_x_wget__h828) != DEF_x_wget__h828)
      {
	vcd_write_val(sim_hdl, num, DEF_x_wget__h828, 8u);
	backing.DEF_x_wget__h828 = DEF_x_wget__h828;
      }
      ++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_dut_booth_step, 1u);
      backing.DEF_CAN_FIRE_RL_dut_booth_step = DEF_CAN_FIRE_RL_dut_booth_step;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_feed, 1u);
      backing.DEF_CAN_FIRE_RL_tb_feed = DEF_CAN_FIRE_RL_tb_feed;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_monitor_test, 1u);
      backing.DEF_CAN_FIRE_RL_tb_monitor_test = DEF_CAN_FIRE_RL_tb_monitor_test;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_randomA_every, 1u);
      backing.DEF_CAN_FIRE_RL_tb_randomA_every = DEF_CAN_FIRE_RL_tb_randomA_every;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_randomA_every_1, 1u);
      backing.DEF_CAN_FIRE_RL_tb_randomA_every_1 = DEF_CAN_FIRE_RL_tb_randomA_every_1;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_randomB_every, 1u);
      backing.DEF_CAN_FIRE_RL_tb_randomB_every = DEF_CAN_FIRE_RL_tb_randomB_every;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_randomB_every_1, 1u);
      backing.DEF_CAN_FIRE_RL_tb_randomB_every_1 = DEF_CAN_FIRE_RL_tb_randomB_every_1;
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_RL_tb_read, 1u);
      backing.DEF_CAN_FIRE_RL_tb_read = DEF_CAN_FIRE_RL_tb_read;
      vcd_write_val(sim_hdl, num++, DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44, 1u);
      backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44 = DEF_IF_tb_randomA_zaz_whas__3_THEN_IF_tb_randomA_z_ETC___d44;
      vcd_write_val(sim_hdl, num++, DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35, 8u);
      backing.DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35 = DEF_IF_tb_randomA_zaz_whas__3_THEN_tb_randomA_zaz__ETC___d35;
      vcd_write_val(sim_hdl, num++, DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45, 1u);
      backing.DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45 = DEF_IF_tb_randomB_zaz_whas__1_THEN_tb_randomB_zaz__ETC___d45;
      vcd_write_val(sim_hdl, num++, PORT_RST_N, 1u);
      backing.PORT_RST_N = PORT_RST_N;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_dut_booth_step, 1u);
      backing.DEF_WILL_FIRE_RL_dut_booth_step = DEF_WILL_FIRE_RL_dut_booth_step;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_feed, 1u);
      backing.DEF_WILL_FIRE_RL_tb_feed = DEF_WILL_FIRE_RL_tb_feed;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_monitor_test, 1u);
      backing.DEF_WILL_FIRE_RL_tb_monitor_test = DEF_WILL_FIRE_RL_tb_monitor_test;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_randomA_every, 1u);
      backing.DEF_WILL_FIRE_RL_tb_randomA_every = DEF_WILL_FIRE_RL_tb_randomA_every;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_randomA_every_1, 1u);
      backing.DEF_WILL_FIRE_RL_tb_randomA_every_1 = DEF_WILL_FIRE_RL_tb_randomA_every_1;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_randomB_every, 1u);
      backing.DEF_WILL_FIRE_RL_tb_randomB_every = DEF_WILL_FIRE_RL_tb_randomB_every;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_randomB_every_1, 1u);
      backing.DEF_WILL_FIRE_RL_tb_randomB_every_1 = DEF_WILL_FIRE_RL_tb_randomB_every_1;
      vcd_write_val(sim_hdl, num++, DEF_WILL_FIRE_RL_tb_read, 1u);
      backing.DEF_WILL_FIRE_RL_tb_read = DEF_WILL_FIRE_RL_tb_read;
      vcd_write_val(sim_hdl, num++, DEF_dut_p__h2034, 18u);
      backing.DEF_dut_p__h2034 = DEF_dut_p__h2034;
      vcd_write_val(sim_hdl, num++, DEF_tb_randomA_zaz_whas____d33, 1u);
      backing.DEF_tb_randomA_zaz_whas____d33 = DEF_tb_randomA_zaz_whas____d33;
      vcd_write_val(sim_hdl, num++, DEF_tb_read_count_1_EQ_128___d72, 1u);
      backing.DEF_tb_read_count_1_EQ_128___d72 = DEF_tb_read_count_1_EQ_128___d72;
      vcd_write_val(sim_hdl, num++, DEF_v__h1262, 32u);
      backing.DEF_v__h1262 = DEF_v__h1262;
      vcd_write_val(sim_hdl, num++, DEF_v__h1335, 8u);
      backing.DEF_v__h1335 = DEF_v__h1335;
      vcd_write_val(sim_hdl, num++, DEF_v__h885, 32u);
      backing.DEF_v__h885 = DEF_v__h885;
      vcd_write_val(sim_hdl, num++, DEF_v__h959, 8u);
      backing.DEF_v__h959 = DEF_v__h959;
      vcd_write_val(sim_hdl, num++, DEF_x__h1932, 32u);
      backing.DEF_x__h1932 = DEF_x__h1932;
      vcd_write_val(sim_hdl, num++, DEF_x__h2488, 32u);
      backing.DEF_x__h2488 = DEF_x__h2488;
      vcd_write_val(sim_hdl, num++, DEF_x__h417, 4u);
      backing.DEF_x__h417 = DEF_x__h417;
      vcd_write_val(sim_hdl, num++, DEF_x_wget__h1205, 8u);
      backing.DEF_x_wget__h1205 = DEF_x_wget__h1205;
      vcd_write_val(sim_hdl, num++, DEF_x_wget__h828, 8u);
      backing.DEF_x_wget__h828 = DEF_x_wget__h828;
    }
}

void MOD_mkTbEx9a::vcd_prims(tVCDDumpType dt, MOD_mkTbEx9a &backing)
{
  INST_dut_busy.dump_VCD(dt, backing.INST_dut_busy);
  INST_dut_i.dump_VCD(dt, backing.INST_dut_i);
  INST_dut_m_neg.dump_VCD(dt, backing.INST_dut_m_neg);
  INST_dut_m_pos.dump_VCD(dt, backing.INST_dut_m_pos);
  INST_dut_p.dump_VCD(dt, backing.INST_dut_p);
  INST_tb_cycle.dump_VCD(dt, backing.INST_tb_cycle);
  INST_tb_feed_count.dump_VCD(dt, backing.INST_tb_feed_count);
  INST_tb_operands_fifo.dump_VCD(dt, backing.INST_tb_operands_fifo);
  INST_tb_randomA_ignore.dump_VCD(dt, backing.INST_tb_randomA_ignore);
  INST_tb_randomA_initialized.dump_VCD(dt, backing.INST_tb_randomA_initialized);
  INST_tb_randomA_zaz.dump_VCD(dt, backing.INST_tb_randomA_zaz);
  INST_tb_randomB_ignore.dump_VCD(dt, backing.INST_tb_randomB_ignore);
  INST_tb_randomB_initialized.dump_VCD(dt, backing.INST_tb_randomB_initialized);
  INST_tb_randomB_zaz.dump_VCD(dt, backing.INST_tb_randomB_zaz);
  INST_tb_read_count.dump_VCD(dt, backing.INST_tb_read_count);
}