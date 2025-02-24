
// picorv32_axi_adapter_pkg.sv
package picorv32_axi_adapter_pkg;

    // Import UVM package
    import uvm_pkg::*;
    import picorv32_axi_adapter_types::*;
    `include "uvm_macros.svh"
    // Include all files for the picorv32_axi_adapter components
    `include "picorv32_axi_adapter_transaction.sv"
    `include "picorv32_axi_adapter_driver.sv"
    //`include "picorv32_axi_adapter_monitor.sv"
    `include "picorv32_axi_adapter_sequencer.sv"
    `include "picorv32_axi_adapter_agent.sv"
    //`include "picorv32_axi_adapter_env.sv"
    //`include "picorv32_axi_adapter_sequence.sv"
    //`include "picorv32_axi_adapter_test.sv"

endpackage : picorv32_axi_adapter_pkg
