
`timescale 1ns / 1ps

module tb_picorv32_axi_adapter;
  // Clock and Reset signals
  reg clk;
  reg resetn;

  // AXI4-Lite signals
  wire        mem_axi_awvalid;
  wire        mem_axi_awready;
  wire [31:0] mem_axi_awaddr;
  wire [2:0]  mem_axi_awprot;

  wire        mem_axi_wvalid;
  wire        mem_axi_wready;
  wire [31:0] mem_axi_wdata;
  wire [3:0]  mem_axi_wstrb;

  wire        mem_axi_bvalid;
  wire        mem_axi_bready;

  wire        mem_axi_arvalid;
  wire        mem_axi_arready;
  wire [31:0] mem_axi_araddr;
  wire [2:0]  mem_axi_arprot;

  wire        mem_axi_rvalid;
  wire        mem_axi_rready;
  wire [31:0] mem_axi_rdata;

  // PicoRV32 signals
  reg         mem_valid;
  reg         mem_instr;
  wire        mem_ready;
  reg [31:0]  mem_addr;
  reg [31:0]  mem_wdata;
  reg [3:0]   mem_wstrb;
  wire [31:0] mem_rdata;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz clock
  end

  // Reset generation
  initial begin
    resetn = 0;
    #20000 resetn = 1; // Release reset after 20 ns
  end

  // Instantiate the adapter
  picorv32_axi_adapter uut (
    .clk(clk),
    .resetn(resetn),
    .mem_axi_awvalid(mem_axi_awvalid),
    .mem_axi_awready(mem_axi_awready),
    .mem_axi_awaddr(mem_axi_awaddr),
    .mem_axi_awprot(mem_axi_awprot),
    .mem_axi_wvalid(mem_axi_wvalid),
    .mem_axi_wready(mem_axi_wready),
    .mem_axi_wdata(mem_axi_wdata),
    .mem_axi_wstrb(mem_axi_wstrb),
    .mem_axi_bvalid(mem_axi_bvalid),
    .mem_axi_bready(mem_axi_bready),
    .mem_axi_arvalid(mem_axi_arvalid),
    .mem_axi_arready(mem_axi_arready),
    .mem_axi_araddr(mem_axi_araddr),
    .mem_axi_arprot(mem_axi_arprot),
    .mem_axi_rvalid(mem_axi_rvalid),
    .mem_axi_rready(mem_axi_rready),
    .mem_axi_rdata(mem_axi_rdata),
    .mem_valid(mem_valid),
    .mem_instr(mem_instr),
    .mem_ready(mem_ready),
    .mem_addr(mem_addr),
    .mem_wdata(mem_wdata),
    .mem_wstrb(mem_wstrb),
    .mem_rdata(mem_rdata)
  );

  // AXI4-Lite Slave Emulator
  axi4lite_slave_emulator axi_slave (
    .clk(clk),
    .resetn(resetn),
    .awvalid(mem_axi_awvalid),
    .awready(mem_axi_awready),
    .awaddr(mem_axi_awaddr),
    .wvalid(mem_axi_wvalid),
    .wready(mem_axi_wready),
    .wdata(mem_axi_wdata),
    .wstrb(mem_axi_wstrb),
    .bvalid(mem_axi_bvalid),
    .bready(mem_axi_bready),
    .arvalid(mem_axi_arvalid),
    .arready(mem_axi_arready),
    .araddr(mem_axi_araddr),
    .rvalid(mem_axi_rvalid),
    .rready(mem_axi_rready),
    .rdata(mem_axi_rdata)
  );

  // Test scenario
  initial begin
    mem_valid = 0;
    mem_instr = 0;
    mem_addr = 0;
    mem_wdata = 0;
    mem_wstrb = 0;

    // Wait for reset
    @(posedge resetn);

    // Perform a write transaction
    @(posedge clk);
    mem_valid = 1;
    mem_addr = 32'h0000_000A;
    mem_wdata = 32'hdead_beef;
    mem_wstrb = 4'b1111;

    @(posedge clk);
    wait(mem_ready);
    mem_valid = 0;

    // Perform a read transaction
    @(posedge clk);
    mem_valid = 1;
    mem_addr = 32'h0000_000A;
    mem_wstrb = 4'b0000;

    @(posedge clk);
    wait(mem_ready);
    mem_valid = 0;

    // Finish simulation
    #100 $finish;
  end
endmodule

// AXI4-Lite Slave Emulator Module
module axi4lite_slave_emulator (
  input        clk,
  input        resetn,
  input        awvalid,
  output reg   awready,
  input [31:0] awaddr,
  input        wvalid,
  output reg   wready,
  input [31:0] wdata,
  input [3:0]  wstrb,
  output reg   bvalid,
  input        bready,
  input        arvalid,
  output reg   arready,
  input [31:0] araddr,
  output reg   rvalid,
  input        rready,
  output reg [31:0] rdata
);
  reg [31:0] memory [0:255]; // Simple memory for emulation

  always @(posedge clk or negedge resetn) begin
    if (!resetn) begin
      awready <= 0;
      wready <= 0;
      bvalid <= 0;
      arready <= 0;
      rvalid <= 0;
      rdata <= 0;
    end else begin
      // Write address handshake
      if (awvalid && !awready) awready <= 1;
      else awready <= 0;

      // Write data handshake
      if (wvalid && !wready) begin
        wready <= 1;
        memory[awaddr[31:2]] <= wdata; // Write data to memory
      end else begin
        wready <= 0;
      end

      // Write response
      if (wvalid && wready && !bvalid) bvalid <= 1;
      else if (bready) bvalid <= 0;

      // Read address handshake
      if (arvalid && !arready) begin
        arready <= 1;
        rdata <= memory[araddr[31:2]]; // Read data from memory
      end else begin
        arready <= 0;
      end

      // Read response
      if (arvalid && arready && !rvalid) rvalid <= 1;
      else if (rready) rvalid <= 0;
    end
  end
endmodule
