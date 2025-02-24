
// picorv32_axi_adapter_test.sv
`include "uvm_macros.svh"
import uvm_pkg::*;
import picorv32_axi_adapter_pkg::*;
import sequences_pkg::*;

class picorv32_axi_adapter_test extends uvm_test;
    `uvm_component_utils(picorv32_axi_adapter_test)

    // Declare the environment
    picorv32_axi_adapter_env env;
    basic_read_write_sequence basic_seq;

    function new(string name = "picorv32_axi_adapter_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Build the environment
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = picorv32_axi_adapter_env::type_id::create("env", this);
    endfunction


    virtual task run_phase(uvm_phase phase);
        //`uvm_info("TEST", "Starting picorv32_axi_adapter_test...", UVM_LOW)
        uvm_objection obj = phase.get_objection();
        obj.set_drain_time(this,200ns);
        phase.raise_objection(this);
        basic_seq = basic_read_write_sequence::type_id::create("basic_seq",this);
        // Basic read and write transactions
        basic_seq.start(env.agent.sequencer);

        // Simultaneous read/write transactions
       /* simultaneous_read_write_sequence sim_seq = simultaneous_read_write_sequence::type_id::create("sim_seq");
        sim_seq.start(env.sequencer);

        // Invalid state transactions
        invalid_state_sequence invalid_seq = invalid_state_sequence::type_id::create("invalid_seq");
        invalid_seq.start(env.sequencer);*/

        phase.drop_objection(this);
        
        uvm_report_info("TEST", "Finished picorv32_axi_adapter_test.", UVM_LOW);
   endtask
endclass
