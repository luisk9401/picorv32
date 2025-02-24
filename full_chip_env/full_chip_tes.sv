//===============================================================
// Full Chip Test Implementation
//===============================================================
class fullchip_basic_test extends fullchip_test;
    `uvm_component_utils(fullchip_basic_test)

    function new(string name = "fullchip_basic_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
        `uvm_info(get_type_name(), "Starting full chip basic test...", UVM_LOW)
        // Test sequence implementation
    endtask
endclass
