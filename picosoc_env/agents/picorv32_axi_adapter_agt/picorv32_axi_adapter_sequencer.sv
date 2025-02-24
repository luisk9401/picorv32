
class picorv32_axi_adapter_sequencer extends uvm_sequencer #(picorv32_axi_adapter_transaction);
    `uvm_component_utils(picorv32_axi_adapter_sequencer)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
