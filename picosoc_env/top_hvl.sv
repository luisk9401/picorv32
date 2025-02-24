module hvl_top;
  // Virtual Interface
  virtual picorv32_axi_adapter_if vif;

  // Instantiate HDL top
  hdl_top hdl_inst();

  // Bind virtual interface
  initial begin
    //picorv32_mem_if mem_vif = hdl_inst.mem_if; // Bind the interface to the testbench
    uvm_config_db#(virtual picorv32_mem_if)::set(null, "*", "mem_vif", hdl_inst.mem_if);
    run_test(); // Start the UVM test
  end
endmodule

