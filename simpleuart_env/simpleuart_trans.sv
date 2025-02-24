//===============================================================
// Simple UART (simpleuart) UVM Verification Environment
//===============================================================

// Transaction for simpleuart
class simpleuart_trans extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(simpleuart_trans)
endclass
