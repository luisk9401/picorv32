
// picorv32_axi_adapter_transaction.sv
class picorv32_axi_adapter_transaction extends uvm_sequence_item;
    
    rand bit [31:0] mem_addr;
    rand bit [31:0] mem_wdata;
    rand bit [3:0]  mem_wstrb;
    rand a_tran_type trans_type;
    bit [31:0] data_out; // Output data for read transactions

    `uvm_object_utils(picorv32_axi_adapter_transaction)

    function new(string name = "picorv32_axi_adapter_transaction");
        super.new(name);
    endfunction

endclass
