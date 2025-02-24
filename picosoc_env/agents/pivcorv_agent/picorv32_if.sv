
// picorv32_if.sv
interface picorv32_if(
    input logic clk,
    input logic resetn,
    output logic trap,
    output logic mem_valid,
    output logic mem_instr,
    input logic mem_ready,
    output logic [31:0] mem_addr,
    output logic [31:0] mem_wdata,
    output logic [3:0] mem_wstrb,
    input logic [31:0] mem_rdata
);
    // Clocking block for synchronized stimulus and sampling
    clocking cb @(posedge clk);
        output resetn;
        input trap;
        output mem_valid;
        output mem_instr;
        input mem_ready;
        output mem_addr;
        output mem_wdata;
        output mem_wstrb;
        input mem_rdata;
    endclocking
endinterface
