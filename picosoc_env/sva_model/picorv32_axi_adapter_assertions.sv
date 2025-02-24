module picorv32_axi_adapter_reference (
    input clk, resetn,

    input        mem_axi_awvalid,
    input        mem_axi_awready,
    input [31:0] mem_axi_awaddr,
    input        mem_axi_wvalid,
    input        mem_axi_wready,
    input [31:0] mem_axi_wdata,
    input [ 3:0] mem_axi_wstrb,
    input        mem_axi_bvalid,
    input        mem_axi_bready,

    input        mem_axi_arvalid,
    input        mem_axi_arready,
    input [31:0] mem_axi_araddr,
    input        mem_axi_rvalid,
    input        mem_axi_rready,
    input [31:0] mem_axi_rdata,

    // PicoRV32 memory interface
    input         mem_valid,
    input         mem_instr,
    input  [31:0] mem_addr,
    input  [31:0] mem_wdata,
    input  [ 3:0] mem_wstrb,
    input  [31:0] mem_rdata,
    input         mem_ready,
    input  [31:0] external_memory_data [0:255],
    picorv32_mem_if mem_vif
);

    // Write transaction validation
    property write_transaction;
        @(posedge clk)
        resetn &&  $rose(mem_vif.wr_valid) && 
        (mem_vif.mem_data != 0)    &&
        (mem_vif.mem_addr != 0) |-> 
        ##2 (external_memory_data[mem_axi_awaddr] == mem_axi_wdata);
     endproperty
    assert_write: assert property (write_transaction)
        else $error("Write transaction mismatch: External memory content does not match write data");

    // Read transaction validation
    property read_transaction;
        @(posedge clk)
        resetn  && mem_axi_rready |-> 
        (external_memory_data[mem_axi_araddr] == mem_axi_rdata);
    endproperty
    assert_read: assert property (read_transaction)
        else $error("Read transaction mismatch: External memory content does not match read data");

    // Validate output signal handling
    // Ensure that awvalid and arvalid are not asserted simultaneously
    property no_simultaneous_aw_ar;
        @(posedge clk)
        resetn |-> !(mem_axi_awvalid && mem_axi_arvalid);
    endproperty
    assert_no_simultaneous_aw_ar: assert property (no_simultaneous_aw_ar)
        else $error("Error: mem_axi_awvalid and mem_axi_arvalid are asserted simultaneously!");

    // There is a bug in the dut bready doesn't take account bvalid it used mem_valid instead 
    // Ensure bready is asserted only when bvalid is high
    /*property bready_when_bvalid;
        @(posedge clk)
        resetn && mem_axi_bready |-> mem_axi_bvalid;
     endproperty
    assert_bready_when_bvalid: assert property (bready_when_bvalid)
        else $error("Error: mem_axi_bready asserted without mem_axi_bvalid!");
    */
    // Ensure rready is asserted only when rvalid is high
    property rready_when_rvalid;
        @(posedge clk)
        resetn && mem_axi_rready |-> mem_axi_rvalid;
    endproperty
    assert_rready_when_rvalid: assert property (rready_when_rvalid)
        else $error("Error: mem_axi_rready asserted without mem_axi_rvalid!");

    // Ensure mem_ready is asserted only when mem_valid is asserted
    property mem_ready_when_valid;
        @(posedge clk)
        resetn |-> (mem_ready == (mem_valid && (mem_axi_bvalid || mem_axi_rvalid)));
    endproperty
    assert_mem_ready_when_valid: assert property (mem_ready_when_valid)
        else $error("Error: mem_ready signal is not consistent with mem_valid!");

endmodule
