bind mesi_isc controller_checker_sva 
    #(.CBUS_CMD_WIDTH(CBUS_CMD_WIDTH),
      .ADDR_WIDTH(ADDR_WIDTH),
      .BROAD_TYPE_WIDTH(BROAD_TYPE_WIDTH),
      .BROAD_ID_WIDTH(BROAD_ID_WIDTH),  
      .BROAD_REQ_FIFO_SIZE(BROAD_REQ_FIFO_SIZE),
      .BROAD_REQ_FIFO_SIZE_LOG2(BROAD_REQ_FIFO_SIZE_LOG2),
      .MBUS_CMD_WIDTH(MBUS_CMD_WIDTH),
      .BREQ_FIFO_SIZE(BREQ_FIFO_SIZE),
      .BREQ_FIFO_SIZE_LOG2(BREQ_FIFO_SIZE_LOG2)) 
	check1(
     // Inputs
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
     mbus_ack0_o
   );