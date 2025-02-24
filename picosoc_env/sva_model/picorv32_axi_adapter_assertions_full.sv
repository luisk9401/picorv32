
module picorv32_axi_adapter_sva(
    input clk, 
    input resetn,
    
    // AXI4-lite master memory interface
    input        mem_axi_awvalid,
    input        mem_axi_awready,
    input [31:0] mem_axi_awaddr,
    input [ 2:0] mem_axi_awprot,

    input        mem_axi_wvalid,
    input        mem_axi_wready,
    input [31:0] mem_axi_wdata,
    input [ 3:0] mem_axi_wstrb,

    input        mem_axi_bvalid,
    input        mem_axi_bready,

    input        mem_axi_arvalid,
    input        mem_axi_arready,
    input [31:0] mem_axi_araddr,
    input [ 2:0] mem_axi_arprot,

    input        mem_axi_rvalid,
    input        mem_axi_rready,
    input [31:0] mem_axi_rdata,

    // Native PicoRV32 memory interface
    input        mem_valid,
    input        mem_instr,
    input        mem_ready,
    input [31:0] mem_addr,
    input [31:0] mem_wdata,
    input [ 3:0] mem_wstrb,
    input [31:0] mem_rdata
);

    //===============================================================
    // Functions for Readability
    //===============================================================

    // Function to check if a write transaction is active
    function automatic bit is_write_active();
        return (mem_axi_awvalid && mem_axi_awready && mem_axi_wvalid && mem_axi_wready);
    endfunction

    // Function to check if a read transaction is active
    function automatic bit is_read_active();
        return (mem_axi_arvalid && mem_axi_arready);
    endfunction

    // Function to check if a write transaction is complete
    function automatic bit is_write_complete();
        return (mem_axi_bvalid && mem_axi_bready);
    endfunction

    // Function to check if a read transaction is complete
    function automatic bit is_read_complete();
        return (mem_axi_rvalid && mem_axi_rready);
    endfunction

    // Function to check if both read and write are active
    function automatic bit is_read_write_active();
        return is_write_active() && is_read_active();
    endfunction

    //===============================================================
    // Write Address Channel Assertions
    //===============================================================
    // AWVALID must remain asserted until AWREADY is high
    property p_awvalid_hold;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_awvalid |-> ##[1:$] mem_axi_awready;
    endproperty
    assert property (p_awvalid_hold)
        else $error("AWVALID was deasserted before AWREADY was high.");

    // AWADDR and AWPROT should remain stable when AWVALID is high and AWREADY is low
    property p_awaddr_stable;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_awvalid && !mem_axi_awready |-> 
        $stable(mem_axi_awaddr) && $stable(mem_axi_awprot);
    endproperty
    assert property (p_awaddr_stable)
        else $error("AWADDR or AWPROT changed while AWVALID was asserted.");

    //===============================================================
    // Write Data Channel Assertions
    //===============================================================
    // WVALID must remain asserted until WREADY is high
    property p_wvalid_hold;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_wvalid |-> ##[1:$] mem_axi_wready;
    endproperty
    assert property (p_wvalid_hold)
        else $error("WVALID was deasserted before WREADY was high.");

    // WDATA and WSTRB should remain stable when WVALID is high and WREADY is low
    property p_wdata_stable;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_wvalid && !mem_axi_wready |-> 
        $stable(mem_axi_wdata) && $stable(mem_axi_wstrb);
    endproperty
    assert property (p_wdata_stable)
        else $error("WDATA or WSTRB changed while WVALID was asserted.");

    //===============================================================
    // Write Response Channel Assertions
    //===============================================================
    // BVALID implies BREADY in the same cycle or a future cycle
    property p_bvalid_bready;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_bvalid |-> ##[1:$] mem_axi_bready;
    endproperty
    assert property (p_bvalid_bready)
        else $error("BVALID was high without BREADY.");

    //===============================================================
    // Read Address Channel Assertions
    //===============================================================
    // ARVALID must remain asserted until ARREADY is high
    property p_arvalid_hold;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_arvalid |-> ##[1:$] mem_axi_arready;
    endproperty
    assert property (p_arvalid_hold)
        else $error("ARVALID was deasserted before ARREADY was high.");

    // ARADDR and ARPROT should remain stable when ARVALID is high and ARREADY is low
    property p_araddr_stable;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_arvalid && !mem_axi_arready |-> 
        $stable(mem_axi_araddr) && $stable(mem_axi_arprot);
    endproperty
    assert property (p_araddr_stable)
        else $error("ARADDR or ARPROT changed while ARVALID was asserted.");

    //===============================================================
    // Read Data Channel Assertions
    //===============================================================
    // RVALID implies RREADY in the same cycle or a future cycle
    property p_rvalid_rready;
        @(posedge clk)
        disable iff (!resetn)
        mem_axi_rvalid |-> ##[1:$] mem_axi_rready;
    endproperty
    assert property (p_rvalid_rready)
        else $error("RVALID was high without RREADY.");

    //===============================================================
    // Additional Cover Properties for Functional Coverage
    //===============================================================
    // Cover a complete write transaction
    cover property (@(posedge clk) is_write_complete());

    // Cover a complete read transaction
    cover property (@(posedge clk) is_read_complete());

    // Cover a simultaneous read and write transaction
    cover property (@(posedge clk) is_read_write_active());

    // Cover different write strobes
    cover property (@(posedge clk) mem_axi_wstrb == 4'b0001);
    cover property (@(posedge clk) mem_axi_wstrb == 4'b0011);
    cover property (@(posedge clk) mem_axi_wstrb == 4'b1111);

    // Cover write and read to the same address
    cover property (@(posedge clk) 
        (mem_axi_awvalid && mem_axi_awready && mem_axi_awaddr == mem_axi_araddr)
    );

    // Cover condition where both AWVALID and ARVALID are high in the same cycle
    cover property (@(posedge clk) mem_axi_awvalid && mem_axi_arvalid);

    // Cover all possible values of ARPROT
    cover property (@(posedge clk) mem_axi_arprot == 3'b000);
    cover property (@(posedge clk) mem_axi_arprot == 3'b001);
    cover property (@(posedge clk) mem_axi_arprot == 3'b100);

endmodule
