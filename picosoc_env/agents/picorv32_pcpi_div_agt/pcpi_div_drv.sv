class pcpi_div_drv extends uvm_driver#(pcpi_div_txn);
    `uvm_component_utils(pcpi_div_drv)

    // Virtual interface handle for driving signals
    virtual pcpi_div_if vif;

    // Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // Build phase to get virtual interface
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual pcpi_div_if)::get(this, "", "pcpi_div_if", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for pcpi_div_driver")
        end
    endfunction

    // Main task to drive transactions
    task run_phase(uvm_phase phase);
        pcpi_div_txn txn;
        @(posedge vif.resetn);
        forever begin
            seq_item_port.get_next_item(txn);
            @(posedge vif.clk);
            // Drive the transaction to DUT
            vif.pcpi_valid = 1;
            vif.pcpi_insn = txn.pcpi_insn;
            vif.pcpi_rs1 = txn.pcpi_rs1;
            vif.pcpi_rs2 = txn.pcpi_rs2;
            wait(vif.pcpi_ready); // Wait for ready signal

            // Complete the transaction
            vif.pcpi_valid = 0;
            seq_item_port.item_done();
        end
    endtask
endclass

