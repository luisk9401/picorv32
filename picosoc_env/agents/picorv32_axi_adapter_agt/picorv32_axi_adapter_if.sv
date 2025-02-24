
interface picorv32_axi_adapter_if(input logic clk, resetn);
    // AXI4-lite master memory interface signals
    logic mem_axi_awvalid;
    logic mem_axi_awready;
    logic [31:0] mem_axi_awaddr;
    logic [2:0] mem_axi_awprot;
    logic mem_axi_wvalid;
    logic mem_axi_wready;
    logic [31:0] mem_axi_wdata;
    logic [3:0] mem_axi_wstrb;
    logic mem_axi_bvalid;
    logic mem_axi_bready;
    logic mem_axi_arvalid;
    logic mem_axi_arready;
    logic [31:0] mem_axi_araddr;
    logic [2:0] mem_axi_arprot;
    logic mem_axi_rvalid;
    logic mem_axi_rready;
    logic [31:0] mem_axi_rdata;

    // Native PicoRV32 memory interface signals
    logic mem_valid;
    logic mem_instr;
    logic mem_ready;
    logic [31:0] mem_addr;
    logic [31:0] mem_wdata;
    logic [3:0] mem_wstrb;
    logic [31:0] mem_rdata;

endinterface
