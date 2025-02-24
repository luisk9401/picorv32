
// picorv32_axi_adapter_agent.sv
class picorv32_axi_adapter_agent extends uvm_agent;
    picorv32_axi_adapter_driver driver;
    //picorv32_axi_adapter_monitor monitor;
    picorv32_axi_adapter_sequencer sequencer;
    virtual picorv32_axi_adapter_if vif;

    `uvm_component_utils(picorv32_axi_adapter_agent)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        driver = picorv32_axi_adapter_driver::type_id::create("driver", this);
        //monitor = picorv32_axi_adapter_monitor::type_id::create("monitor", this);
        sequencer = picorv32_axi_adapter_sequencer::type_id::create("sequencer", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
        //monitor.ap.connect(uvm_test_top.env.scoreboard.analysis_export);
    endfunction
endclass
