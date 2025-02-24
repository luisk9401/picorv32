
// invalid_state_sequence.sv
class invalid_state_sequence extends uvm_sequence#(picorv32_axi_adapter_transaction);
    `uvm_object_utils(invalid_state_sequence)

    task body();
        picorv32_axi_adapter_transaction trans;

        // Attempt a write transaction without providing data
        trans = picorv32_axi_adapter_transaction::type_id::create("invalid_write_trans");
        //trans.type = WRITE;
        trans.addr = 32'h0000_3000;
        // Skip setting trans.data for this invalid test
        start_item(trans);
        finish_item(trans);

        // Monitor should flag this as an error if it’s invalid
    endtask
endclass
