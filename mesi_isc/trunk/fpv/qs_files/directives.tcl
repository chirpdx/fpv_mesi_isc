# Define clocks
netlist clock clk -period 10 

# Constrain rst
#formal 
netlist constraint rst -after_init -value 1'b0
