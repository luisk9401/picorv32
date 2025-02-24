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
  output reg [31:0] rdata,
  output reg [31:0] memory [0:255]
);
  reg [31:0] write_address;
  reg [31:0] read_address;

  always @(posedge clk or negedge resetn) begin
    if (!resetn) begin
      // Reset all control signals
      awready <= 0;
      wready <= 0;
      bvalid <= 0;
      arready <= 0;
      rvalid <= 0;
      rdata <= 0;
    end else begin
      // Write Address Handshake
      if (awvalid && !awready) begin
        awready <= 1;  // Accept address
        write_address <= awaddr;
      end else begin
        awready <= 0;  
      end

      if (wvalid && !wready) begin
        wready <= 1;  
        memory[write_address] <= wdata; 
      end else begin
        wready <= 0;  
      end

      // Write Response
      if (wvalid && wready && !bvalid) begin
        bvalid <= 1; 
      end else if (bready) begin
        bvalid <= 0; 
      end
      // Read response 
      if (arvalid && !arready) begin
        arready <= 1;  
        read_address <= araddr;
      end else begin
        arready <= 0;  
      end

      if (arvalid && arready && !rvalid) begin
        rvalid <= 1;    
        rdata <= memory[read_address]; 
      end else if (rready) begin
        rvalid <= 0; 
      end
    end
  end
endmodule
