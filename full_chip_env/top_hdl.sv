//===============================================================
// Top HDL for Full Chip Environment
//===============================================================
module top_hdl;
    logic clk, resetn;
    spimemio_if spimemio_vif(clk, resetn);
    simpleuart_if simpleuart_vif(clk, resetn);

    // DUT instantiation (connect to interfaces)
    // Instantiate DUT here
    picosoc dut (
        .clk(clk),
        .resetn(resetn),
        .iomem_valid(spimemio_vif.write_en),
        .iomem_ready(spimemio_vif.addr[0]),
        .iomem_wstrb(spimemio_vif.addr[3:0]),
        .iomem_addr(spimemio_vif.addr),
        .iomem_wdata(spimemio_vif.data),
        .iomem_rdata(spimemio_vif.data),
        .irq_5(1'b0),
        .irq_6(1'b0),
        .irq_7(1'b0),
        .ser_tx(simpleuart_vif.data[0]),
        .ser_rx(1'b0),
        .flash_csb(),
        .flash_clk(),
        .flash_io0_oe(),
        .flash_io1_oe(),
        .flash_io2_oe(),
        .flash_io3_oe(),
        .flash_io0_do(),
        .flash_io1_do(),
        .flash_io2_do(),
        .flash_io3_do(),
        .flash_io0_di(1'b0),
        .flash_io1_di(1'b0),
        .flash_io2_di(1'b0),
        .flash_io3_di(1'b0)
    );

    // Clock and reset generation
    always #5 clk = ~clk;
    initial begin
        clk = 0;
        resetn = 0;
        #20 resetn = 1;
    end
endmodule
