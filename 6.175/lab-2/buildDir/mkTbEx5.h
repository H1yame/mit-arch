/*
 * Generated by Bluespec Compiler, version 2023.01 (build 52adafa5)
 * 
 * On Sun Jan 28 09:02:40 UTC 2024
 * 
 */

/* Generation options: keep-fires */
#ifndef __mkTbEx5_h__
#define __mkTbEx5_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"


/* Class declaration for the mkTbEx5 module */
class MOD_mkTbEx5 : public Module {
 
 /* Clock handles */
 private:
  tClock __clk_handle_0;
 
 /* Clock gate handles */
 public:
  tUInt8 *clk_gate[0];
 
 /* Instantiation parameters */
 public:
 
 /* Module state */
 public:
  MOD_Reg<tUInt32> INST_dut_a_reg;
  MOD_Reg<tUInt8> INST_dut_b_reg;
  MOD_Reg<tUInt8> INST_dut_busy;
  MOD_Reg<tUInt8> INST_dut_i;
  MOD_Reg<tUInt32> INST_dut_product;
  MOD_Reg<tUInt32> INST_tb_cycle;
  MOD_Reg<tUInt32> INST_tb_feed_count;
  MOD_Fifo<tUInt32> INST_tb_operands_fifo;
  MOD_Wire<tUInt8> INST_tb_randomA_ignore;
  MOD_Reg<tUInt8> INST_tb_randomA_initialized;
  MOD_Wire<tUInt8> INST_tb_randomA_zaz;
  MOD_Wire<tUInt8> INST_tb_randomB_ignore;
  MOD_Reg<tUInt8> INST_tb_randomB_initialized;
  MOD_Wire<tUInt8> INST_tb_randomB_zaz;
  MOD_Reg<tUInt32> INST_tb_read_count;
 
 /* Constructor */
 public:
  MOD_mkTbEx5(tSimStateHdl simHdl, char const *name, Module *parent);
 
 /* Symbol init methods */
 private:
  void init_symbols_0();
 
 /* Reset signal definitions */
 private:
  tUInt8 PORT_RST_N;
 
 /* Port definitions */
 public:
 
 /* Publicly accessible definitions */
 public:
  tUInt8 DEF_WILL_FIRE_RL_tb_randomB_every_1;
  tUInt8 DEF_CAN_FIRE_RL_tb_randomB_every_1;
  tUInt8 DEF_WILL_FIRE_RL_tb_randomB_every;
  tUInt8 DEF_CAN_FIRE_RL_tb_randomB_every;
  tUInt8 DEF_WILL_FIRE_RL_tb_randomA_every_1;
  tUInt8 DEF_CAN_FIRE_RL_tb_randomA_every_1;
  tUInt8 DEF_WILL_FIRE_RL_tb_randomA_every;
  tUInt8 DEF_CAN_FIRE_RL_tb_randomA_every;
  tUInt8 DEF_WILL_FIRE_RL_tb_monitor_test;
  tUInt8 DEF_CAN_FIRE_RL_tb_monitor_test;
  tUInt8 DEF_WILL_FIRE_RL_tb_read;
  tUInt8 DEF_CAN_FIRE_RL_tb_read;
  tUInt8 DEF_WILL_FIRE_RL_tb_feed;
  tUInt8 DEF_CAN_FIRE_RL_tb_feed;
  tUInt8 DEF_WILL_FIRE_RL_dut_mul_step;
  tUInt8 DEF_CAN_FIRE_RL_dut_mul_step;
  tUInt32 DEF_x__h2521;
  tUInt32 DEF_x__h1668;
  tUInt8 DEF_x_wget__h1133;
  tUInt8 DEF_x_wget__h756;
  tUInt8 DEF_x__h278;
  tUInt8 DEF_v__h887;
  tUInt8 DEF_v__h1263;
  tUInt8 DEF_tb_read_count_8_EQ_128___d49;
  tUInt8 DEF_IF_tb_randomA_zaz_whas__7_THEN_tb_randomA_zaz__ETC___d27;
  tUInt8 DEF_IF_tb_randomB_zaz_whas__4_THEN_tb_randomB_zaz__ETC___d28;
 
 /* Local definitions */
 private:
  tUInt32 DEF_v__h1190;
  tUInt32 DEF_v__h813;
  tUInt32 DEF_v__h1712;
 
 /* Rules */
 public:
  void RL_dut_mul_step();
  void RL_tb_randomA_every();
  void RL_tb_randomA_every_1();
  void RL_tb_randomB_every();
  void RL_tb_randomB_every_1();
  void RL_tb_feed();
  void RL_tb_read();
  void RL_tb_monitor_test();
 
 /* Methods */
 public:
 
 /* Reset routines */
 public:
  void reset_RST_N(tUInt8 ARG_rst_in);
 
 /* Static handles to reset routines */
 public:
 
 /* Pointers to reset fns in parent module for asserting output resets */
 private:
 
 /* Functions for the parent module to register its reset fns */
 public:
 
 /* Functions to set the elaborated clock id */
 public:
  void set_clk_0(char const *s);
 
 /* State dumping routine */
 public:
  void dump_state(unsigned int indent);
 
 /* VCD dumping routines */
 public:
  unsigned int dump_VCD_defs(unsigned int levels);
  void dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_mkTbEx5 &backing);
  void vcd_defs(tVCDDumpType dt, MOD_mkTbEx5 &backing);
  void vcd_prims(tVCDDumpType dt, MOD_mkTbEx5 &backing);
};

#endif /* ifndef __mkTbEx5_h__ */