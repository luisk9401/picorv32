import uvm_pkg::*;
`include "uvm_macros.svh"
import pcpi_div_pkg::*;
import pcpi_div_seq_pkg::*;

class pcpi_div_test extends uvm_test;
   `uvm_component_utils(pcpi_div_test) 
   // Environment instance
   
    pcpi_div_env env;
    pcpi_div_seq seq;
    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Build phase to create environment
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = pcpi_div_env::type_id::create("env", this);
    endfunction

    // Run phase to start the test
    task run_phase(uvm_phase phase);
        uvm_objection obj = phase.get_objection();
        obj.set_drain_time(this,200ns);
        phase.raise_objection(this);
        // Add sequence start here
        seq = pcpi_div_seq::type_id::create("seq",this);
        seq.start(env.agt.sqr);
        phase.drop_objection(this);

    endtask
endclass
