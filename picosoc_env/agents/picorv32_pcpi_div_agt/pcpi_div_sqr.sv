class pcpi_div_sqr extends uvm_sequencer #(pcpi_div_txn);
    `uvm_component_utils(pcpi_div_sqr)
    function new(string name = "pcpi_div_sqr", uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
