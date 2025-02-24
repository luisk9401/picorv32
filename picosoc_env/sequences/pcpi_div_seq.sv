`include "uvm_macros.svh"
package pcpi_div_seq_pkg;
    import uvm_pkg::*;
    import pcpi_div_pkg::*;
   
// pcpi_div_seq.sv
class pcpi_div_seq extends uvm_sequence#(pcpi_div_txn);

    `uvm_object_utils(pcpi_div_seq)

    // Constructor
    function new(string name = "pcpi_div_seq");
        super.new(name);
    endfunction

    // Sequence body
    virtual task body();
        pcpi_div_txn tx;

        repeat (10) begin
            tx = pcpi_div_txn::type_id::create("tx");

            // Randomize instruction type for multiple operations
            assert (tx.randomize() with {
                pcpi_valid == 1;
                pcpi_insn[6:0]  == 7'b0110011;
                pcpi_insn[31:25] == 7'b0000001;
                pcpi_insn[14:12] inside {3'b100, 3'b101, 3'b110, 3'b111}; // DIV, DIVU, REM, REMU
            });

            start_item(tx);
            finish_item(tx);

            // Display the type of operation for better debugging
            case (tx.pcpi_insn[14:12]) 
                3'b100: `uvm_info("SEQ", "DIV Operation", UVM_MEDIUM)
                3'b101: `uvm_info("SEQ", "DIVU Operation", UVM_MEDIUM)
                3'b110: `uvm_info("SEQ", "REM Operation", UVM_MEDIUM)
                3'b111: `uvm_info("SEQ", "REMU Operation", UVM_MEDIUM)
                default: `uvm_error("SEQ", "Unknown Operation")
             endcase
        end
    endtask
 endclass

 endpackage 

