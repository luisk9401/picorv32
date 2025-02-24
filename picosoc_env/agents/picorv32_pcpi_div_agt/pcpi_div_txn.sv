class pcpi_div_txn extends uvm_sequence_item;
    rand bit        pcpi_valid;
    rand bit [31:0] pcpi_insn;
    rand bit [31:0] pcpi_rs1;
    rand bit [31:0] pcpi_rs2;
    bit        pcpi_wr;
    bit [31:0] pcpi_rd;
    bit        pcpi_wait;
    bit        pcpi_ready;
    `uvm_object_utils(pcpi_div_txn)
    function new(string name = "pcpi_div_txn");
        super.new(name);
    endfunction
endclass
