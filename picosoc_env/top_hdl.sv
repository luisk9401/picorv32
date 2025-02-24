module hdl_top();  
// Clock and reset
  reg clk;
  reg resetn;

  // Interface instance
  picorv32_axi_adapter_if axi_if(clk,resetn);
  picorv32_mem_if mem_if(clk,resetn);
  wire [31:0] memory_ref [0:255];
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz clock
  end

  // Reset generation
  initial begin
    resetn = 0;
    #200 resetn = 1; // Release reset after 50 ns
  end

  // DUT instantiation
  picorv32_axi_adapter dut (
    .clk(axi_if.clk),
    .resetn(axi_if.resetn),

    // AXI signals
    .mem_axi_awvalid(axi_if.mem_axi_awvalid),
    .mem_axi_awready(axi_if.mem_axi_awready),
    .mem_axi_awaddr(axi_if.mem_axi_awaddr),
    .mem_axi_awprot(axi_if.mem_axi_awprot),

    .mem_axi_wvalid(axi_if.mem_axi_wvalid),
    .mem_axi_wready(axi_if.mem_axi_wready),
    .mem_axi_wdata(axi_if.mem_axi_wdata),
    .mem_axi_wstrb(axi_if.mem_axi_wstrb),

    .mem_axi_bvalid(axi_if.mem_axi_bvalid),
    .mem_axi_bready(axi_if.mem_axi_bready),

    .mem_axi_arvalid(axi_if.mem_axi_arvalid),
    .mem_axi_arready(axi_if.mem_axi_arready),
    .mem_axi_araddr(axi_if.mem_axi_araddr),
    .mem_axi_arprot(axi_if.mem_axi_arprot),

    .mem_axi_rvalid(axi_if.mem_axi_rvalid),
    .mem_axi_rready(axi_if.mem_axi_rready),
    .mem_axi_rdata(axi_if.mem_axi_rdata),

    // PicoRV32 signals
    .mem_valid(axi_if.mem_valid),
    .mem_instr(axi_if.mem_instr),
    .mem_ready(axi_if.mem_ready),
    .mem_addr(axi_if.mem_addr),
    .mem_wdata(axi_if.mem_wdata),
    .mem_wstrb(axi_if.mem_wstrb),
    .mem_rdata(axi_if.mem_rdata)
  );

  formal_picorv32_axi_adapter_driver formal_driver(
    .clk(clk),
    .resetn(resetn),
    .vif(axi_if),
    .mem_vif(mem_if)
  );
  // AXI4-Lite Slave Emulator instantiation
  axi4lite_slave_emulator axi_slave (
    .clk(axi_if.clk),
    .resetn(axi_if.resetn),

    // AXI4-Lite Slave signals
    .awvalid(axi_if.mem_axi_awvalid),
    .awready(axi_if.mem_axi_awready),
    .awaddr(axi_if.mem_axi_awaddr),

    .wvalid(axi_if.mem_axi_wvalid),
    .wready(axi_if.mem_axi_wready),
    .wdata(axi_if.mem_axi_wdata),
    .wstrb(axi_if.mem_axi_wstrb),

    .bvalid(axi_if.mem_axi_bvalid),
    .bready(axi_if.mem_axi_bready),

    .arvalid(axi_if.mem_axi_arvalid),
    .arready(axi_if.mem_axi_arready),
    .araddr(axi_if.mem_axi_araddr),

    .rvalid(axi_if.mem_axi_rvalid),
    .rready(axi_if.mem_axi_rready),
    .rdata(axi_if.mem_axi_rdata),
    .memory(memory_ref)
  );
  picorv32_axi_adapter_reference ref_model (
        .clk(clk),
        .resetn(resetn),
        .mem_axi_awvalid(axi_if.mem_axi_awvalid),
        .mem_axi_awready(axi_if.mem_axi_awready),
        .mem_axi_awaddr(axi_if.mem_axi_awaddr),
        .mem_axi_wvalid(axi_if.mem_axi_wvalid),
        .mem_axi_wready(axi_if.mem_axi_wready),
        .mem_axi_wdata(axi_if.mem_axi_wdata),
        .mem_axi_wstrb(axi_if.mem_axi_wstrb),
        .mem_axi_bvalid(axi_if.mem_axi_bvalid),
        .mem_axi_bready(axi_if.mem_axi_bready),
        .mem_axi_arvalid(axi_if.mem_axi_arvalid),
        .mem_axi_arready(axi_if.mem_axi_arready),
        .mem_axi_araddr(axi_if.mem_axi_araddr),
        .mem_axi_rvalid(axi_if.mem_axi_rvalid),
        .mem_axi_rready(axi_if.mem_axi_rready),
        .mem_axi_rdata(axi_if.mem_axi_rdata),
        .mem_valid(axi_if.mem_valid),
        .mem_instr(axi_if.mem_instr),
        .mem_addr(axi_if.mem_addr),
        .mem_wdata(axi_if.mem_wdata),
        .mem_wstrb(axi_if.mem_wstrb),
        .mem_rdata(axi_if.mem_rdata),
        .mem_ready(axi_if.mem_ready),
        .external_memory_data(memory_ref),
        .mem_vif(mem_if)
     );
   
  endmodule
