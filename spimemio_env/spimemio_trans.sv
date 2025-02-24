// Transaction for spimemio
class spimemio_trans extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit write_en;
    `uvm_object_utils(spimemio_trans)
endclass
