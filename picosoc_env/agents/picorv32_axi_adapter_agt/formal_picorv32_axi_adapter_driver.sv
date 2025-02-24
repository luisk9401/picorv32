
module formal_picorv32_axi_adapter_driver (
    input logic clk,
    input logic resetn,
    picorv32_axi_adapter_if vif,
    picorv32_mem_if   mem_vif
);

    // Internal task to handle AXI Write Protocol
    
always @(posedge vif.clk or negedge resetn) begin
    if (!resetn) begin
        vif.mem_valid <= 0;
        vif.mem_addr <= 0;
        vif.mem_wstrb <= 0;
    end else begin
        fork
         axi_write_protocol();
         axi_read_protocol();
        join 
    end
end

   task axi_write_protocol(); 
      forever begin  
           @(posedge mem_vif.wr_valid);
            vif.mem_valid <= 1;
            vif.mem_addr <= mem_vif.mem_addr;
           //@(posedge vif.mem_axi_awready);
            vif.mem_wdata <= mem_vif.mem_data;
            vif.mem_wstrb <= 4'hF;

            // Wait for ready signal
            wait(vif.mem_ready);
            repeat (3) @(posedge vif.clk);
            vif.mem_addr <= 0;
            vif.mem_wdata <= 0;
            vif.mem_wstrb <= 4'h0;
            // Deassert signals after transfer
            vif.mem_valid <= 0;
      end 
    endtask

    // Task for AXI Read Protocol
    task axi_read_protocol();
     forever begin  
            @(posedge mem_vif.rd_valid);     
            vif.mem_valid <= 1;
            vif.mem_addr <= mem_vif.mem_addr;
            vif.mem_wstrb <= 4'b0000;

            // Wait for ready signal
            wait(vif.mem_ready);
            repeat (3) @(posedge vif.clk);
            // Capture read data
            mem_vif.rd_data <= vif.mem_rdata;

            // Deassert signals
            vif.mem_valid <= 0;
      end
    endtask

endmodule
