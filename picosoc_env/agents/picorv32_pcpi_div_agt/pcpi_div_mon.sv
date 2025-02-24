class pcpi_div_mon extends uvm_monitor;
    `uvm_component_utils(pcpi_div_mon)
    virtual pcpi_div_if vif;
    uvm_analysis_port #(pcpi_div_txn) mon_ap;
    
    
 // Set the virtual interface
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual pcpi_div_if)::get(this, "", "pcpi_div_if", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set for monitor");
    endfunction
    
    function new(string name = "pcpi_div_mon", uvm_component parent);
        super.new(name, parent);
        mon_ap = new("mon_ap", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
        pcpi_div_txn txn;
        txn = pcpi_div_txn::type_id::create("txn");
        forever begin
            @(posedge vif.clk);
            txn.pcpi_valid = vif.pcpi_valid;
            txn.pcpi_insn  = vif.pcpi_insn;
            txn.pcpi_rs1   = vif.pcpi_rs1;
            txn.pcpi_rs2   = vif.pcpi_rs2;
            txn.pcpi_wr    = vif.pcpi_wr;
            txn.pcpi_rd    = vif.pcpi_rd;
            txn.pcpi_wait  = vif.pcpi_wait;
            txn.pcpi_ready = vif.pcpi_ready;
            mon_ap.write(txn);
        end
    endtask
endclass
