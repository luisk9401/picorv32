class pcpi_div_agent extends uvm_agent;
    `uvm_component_utils(pcpi_div_agent)
    pcpi_div_drv drv;
    pcpi_div_mon mon;
    pcpi_div_sqr sqr;
    function new(string name = "pcpi_div_agent", uvm_component parent);
        super.new(name, parent);
    endfunction
    virtual function void build_phase(uvm_phase phase);
        mon = pcpi_div_mon::type_id::create("mon", this);
        if (is_active == UVM_ACTIVE) begin
            drv = pcpi_div_drv::type_id::create("drv", this);
            sqr = pcpi_div_sqr::type_id::create("sqr", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        drv.seq_item_port.connect(sqr.seq_item_export);
        //monitor.ap.connect(uvm_test_top.env.scoreboard.analysis_export);
    endfunction

endclass
