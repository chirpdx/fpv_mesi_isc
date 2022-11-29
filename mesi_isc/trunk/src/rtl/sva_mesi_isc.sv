`include "mesi_isc_define.v"

module controller_checker_sva(// Inputs
     clk,
     rst,
     mbus_cmd3_i,
     mbus_cmd2_i,
     mbus_cmd1_i,
     mbus_cmd0_i,
     mbus_addr3_i,
     mbus_addr2_i,
     mbus_addr1_i,
     mbus_addr0_i,
     cbus_ack3_i,
     cbus_ack2_i,
     cbus_ack1_i,
     cbus_ack0_i,
     // Outputs
     cbus_addr_o,
     cbus_cmd3_o,
     cbus_cmd2_o,
     cbus_cmd1_o,
     cbus_cmd0_o,
     mbus_ack3_o,
     mbus_ack2_o,
     mbus_ack1_o,
     mbus_ack0_o);

parameter
  CBUS_CMD_WIDTH           = 3,
  ADDR_WIDTH               = 32,
  BROAD_TYPE_WIDTH         = 2,
  BROAD_ID_WIDTH           = 5,  
  BROAD_REQ_FIFO_SIZE      = 4,
  BROAD_REQ_FIFO_SIZE_LOG2 = 2,
  MBUS_CMD_WIDTH           = 3,
  BREQ_FIFO_SIZE           = 2,
  BREQ_FIFO_SIZE_LOG2      = 1;

// Inputs
//================================
// System
input                   clk;          // System clock
input                   rst;          // Active high system reset
// Main buses
input [MBUS_CMD_WIDTH-1:0] mbus_cmd3_i; // Main bus3 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd2_i; // Main bus2 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd1_i; // Main bus1 command
input [MBUS_CMD_WIDTH-1:0] mbus_cmd0_i; // Main bus0 command
// Coherence buses
input [ADDR_WIDTH-1:0]  mbus_addr3_i;  // Coherence bus3 address
input [ADDR_WIDTH-1:0]  mbus_addr2_i;  // Coherence bus2 address
input [ADDR_WIDTH-1:0]  mbus_addr1_i;  // Coherence bus1 address
input [ADDR_WIDTH-1:0]  mbus_addr0_i;  // Coherence bus0 address
input                   cbus_ack3_i;  // Coherence bus3 acknowledge
input                   cbus_ack2_i;  // Coherence bus2 acknowledge
input                   cbus_ack1_i;  // Coherence bus1 acknowledge
input                   cbus_ack0_i;  // Coherence bus0 acknowledge
   
// Outputs
//================================

input [ADDR_WIDTH-1:0] cbus_addr_o;  // Coherence bus address. All busses have
                                      // the same address
input [CBUS_CMD_WIDTH-1:0] cbus_cmd3_o; // Coherence bus3 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd2_o; // Coherence bus2 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd1_o; // Coherence bus1 command
input [CBUS_CMD_WIDTH-1:0] cbus_cmd0_o; // Coherence bus0 command


input                  mbus_ack3_o;  // Main bus3 acknowledge
input                  mbus_ack2_o;  // Main bus2 acknowledge
input                  mbus_ack1_o;  // Main bus1 acknowledge
input                  mbus_ack0_o;  // Main bus0 acknowledge
   

default clocking c0 @(posedge clk); endclocking

//cover_f1: cover property (mbus_cmd3_i == 3'd2);
cover_figure4: cover property((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_WR_BROAD && mbus_addr0_i == 32'd1 ) ##1 ((cbus_cmd1_o == `MESI_ISC_CBUS_CMD_WR_SNOOP) && (cbus_cmd2_o == `MESI_ISC_CBUS_CMD_WR_SNOOP))##1 ((cbus_ack1_i == 1) && (cbus_ack2_i == 1)) ##1 (cbus_cmd0_o == `MESI_ISC_CBUS_CMD_EN_WR)##1((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_RD) && (cbus_addr_o==$past(mbus_addr0_i,4))));


//cover_figure4: cover property ((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_WR_BROAD) ##1 ((cbus_cmd1_o == `MESI_ISC_CBUS_CMD_WR_SNOOP) && (cbus_cmd2_o == `MESI_ISC_CBUS_CMD_WR_SNOOP))
 //                             ##1 ((cbus_ack1_i == 1) && (cbus_ack2_i == 1)) ##1 (cbus_cmd0_o == `MESI_ISC_CBUS_CMD_EN_WR) ##1 (mbus_cmd0_i == `MESI_ISC_MBUS_CMD_RD));
assume_m3 : assume property (mbus_cmd3_i == 0);

assert_no_write_Ms : assert property(!((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_WR) && (mbus_cmd1_i == `MESI_ISC_MBUS_CMD_WR)));

assume_no_write_Ms : assume property((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_WR)|-> (mbus_cmd1_i != mbus_cmd0_i));



//assume_no_write_Ms : assume property((mbus_cmd0_i == `MESI_ISC_MBUS_CMD_WR) && (mbus_cmd1_i == `MESI_ISC_MBUS_CMD_WR));
endmodule



