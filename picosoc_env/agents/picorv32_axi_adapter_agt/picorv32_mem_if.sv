interface picorv32_mem_if(input logic clk,resetn);
    logic [31:0] mem_data;
    logic [7:0] mem_addr;
    logic [31:0] rd_data;
    logic wr_valid;
    logic rd_valid;
endinterface 
