`include "uvm_macros.svh"
import uvm_pkg::*;
import picorv32_axi_adapter_pkg::*;

// picorv32_axi_adapter_env.sv
class picorv32_axi_adapter_env extends uvm_env;
    picorv32_axi_adapter_agent agent; // AXI adapter agent to handle interface interactions

    `uvm_component_utils(picorv32_axi_adapter_env)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Instantiate the agent and associate it with the environment
        agent = picorv32_axi_adapter_agent::type_id::create("agent", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // Connect the agent's monitor and driver with the sequencer
        if (agent != null) begin
            //agent.monitor.analysis_port.connect(this.analysis_export);
        end
    endfunction

    // Add any additional phases if needed for custom actions
    // Optionally, a reset_phase and configure_phase can be added here.

endclass
