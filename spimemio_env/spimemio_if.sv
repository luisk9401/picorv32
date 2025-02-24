// Interface for spimemio
interface spimemio_if(input logic clk, input logic resetn);
    logic [31:0] addr;
    logic [31:0] data;
    logic write_en;
endinterface
