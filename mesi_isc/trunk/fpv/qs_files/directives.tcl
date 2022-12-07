# Define clocks
netlist clock clk -period 10 

# Constrain rst
#formal 
netlist constraint rst -after_init -value 1'b0

netlist blackbox instance mesi_isc.mesi_isc_breq_fifos.fifo_3