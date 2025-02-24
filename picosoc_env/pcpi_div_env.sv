import uvm_pkg::*;
import pcpi_div_pkg::*;

class pcpi_div_env extends uvm_env;
    // Agent instance for driving and monitoring DUT signals
    `uvm_component_utils(pcpi_div_env)

    pcpi_div_agent agt;

    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Build phase to create agent
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agt = pcpi_div_agent::type_id::create("agt", this);
    endfunction
endclass
