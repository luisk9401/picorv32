// top_hvl.sv
// Top-level HVL module for connecting UVM environment to DUT
module top_hvl;
    import uvm_pkg::*;

    // Instantiate Top HDL module
    top_hdl top_hdl_inst();
        // Run the UVM test
    initial begin
       uvm_config_db#(virtual pcpi_div_if)::set(null, "*", "pcpi_div_if", top_hdl_inst.pcpi_if); 
       run_test();
    end
endmodule
