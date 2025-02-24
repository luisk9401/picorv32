
// simultaneous_read_write_sequence.sv
class simultaneous_read_write_sequence extends uvm_sequence#(picorv32_axi_adapter_transaction);
    `uvm_object_utils(simultaneous_read_write_sequence)

    task body();
        picorv32_axi_adapter_transaction write_trans, read_trans;

        // Issue a write transaction
        write_trans = picorv32_axi_adapter_transaction::type_id::create("write_trans");
        //write_trans.type = WRITE;
        write_trans.addr = 32'h0000_2000;
        write_trans.data = 32'hCAFEBABE;
        start_item(write_trans);
        finish_item(write_trans);

        // Simultaneously, issue a read transaction on a different address
        read_trans = picorv32_axi_adapter_transaction::type_id::create("read_trans");
        //read_trans.type = READ;
        read_trans.addr = 32'h0000_2004;
        start_item(read_trans);
        finish_item(read_trans);

        // Expect valid data if read address has been pre-initialized with known data
        if (read_trans.data_out === 32'hXXXXXXXX) begin
            `uvm_error("simultaneous_read_write_sequence", "Read transaction received invalid data!");
        end
    endtask
endclass
