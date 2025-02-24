class pcpi_div_seq extends uvm_sequence #(pcpi_div_txn);
    `uvm_object_utils(pcpi_div_seq)
    function new(string name = "pcpi_div_seq");
        super.new(name);
    endfunction
    virtual task body();
        pcpi_div_txn txn = pcpi_div_txn::type_id::create("txn");
        start_item(txn);
        assert(txn.randomize());
        finish_item(txn);
    endtask
endclass
