import  picorv32_axi_adapter_types::*;

class basic_read_write_sequence extends uvm_sequence #(picorv32_axi_adapter_transaction);

    `uvm_object_utils(basic_read_write_sequence)
   
    function new(string name= "basic_read_write_sequence");
        super.new(name);
    endfunction
    
    task body();
        picorv32_axi_adapter_transaction reset_trans;
        picorv32_axi_adapter_transaction trans;
        picorv32_axi_adapter_transaction read_trans;
        read_trans = picorv32_axi_adapter_transaction::type_id::create("read_tran");
        trans = picorv32_axi_adapter_transaction::type_id::create("tran");
        reset_trans = picorv32_axi_adapter_transaction::type_id::create("reset_tran");
        reset_trans.trans_type = picorv32_axi_adapter_types::RESET;
        start_item(reset_trans);
        finish_item(reset_trans);
        trans.trans_type = picorv32_axi_adapter_types::WRITE;
        trans.mem_addr   = 32'h10;
        trans.mem_wdata  = 32'h12;
        start_item(trans);
        finish_item(trans);
        trans.trans_type = picorv32_axi_adapter_types::READ;
        trans.mem_addr   = 32'h10;
        start_item(trans);
        finish_item(trans);
    endtask

endclass
