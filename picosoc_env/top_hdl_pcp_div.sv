module top_hdl;
    reg clk;
    reg resetn;

    // Instantiate interface
    pcpi_div_if pcpi_if(.clk(clk), .resetn(resetn));

    // Instantiate DUT and connect it to the interface
    picorv32_pcpi_div dut (
        .clk(pcpi_if.clk),
        .resetn(pcpi_if.resetn),
        .pcpi_valid(pcpi_if.pcpi_valid),
        .pcpi_insn(pcpi_if.pcpi_insn),
        .pcpi_rs1(pcpi_if.pcpi_rs1),
        .pcpi_rs2(pcpi_if.pcpi_rs2),
        .pcpi_wr(pcpi_if.pcpi_wr),
        .pcpi_rd(pcpi_if.pcpi_rd),
        .pcpi_wait(pcpi_if.pcpi_wait),
        .pcpi_ready(pcpi_if.pcpi_ready)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Reset sequence
    initial begin
       resetn = 0;
       pcpi_if.pcpi_valid <= 0;
       pcpi_if.pcpi_insn <= 0;
       pcpi_if.pcpi_rs1 <= 0;
       pcpi_if.pcpi_rs2 <= 0;
      #20 resetn <= 1;

    end
    // Connecting the SVA model
    pcpi_div_sva sva_inst (.pcpi_if(pcpi_if));
endmodule
