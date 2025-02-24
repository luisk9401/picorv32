class picorv32_axi_adapter_driver extends uvm_driver#(picorv32_axi_adapter_transaction);
    `uvm_component_utils(picorv32_axi_adapter_driver)

    // Virtual interface to the DUT
   virtual picorv32_mem_if mem_vif;

    function new(string name = "picorv32_axi_adapter_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    // Set the virtual interface
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual picorv32_mem_if)::get(this, "", "mem_vif", mem_vif))
            `uvm_fatal("NOVIF", "Virtual interface not set for driver");
    endfunction
   
    task run_reset();
         @(posedge mem_vif.clk);
         mem_vif.wr_valid <= 0;
         mem_vif.mem_data <= 0;
         mem_vif.mem_addr <= 0;
         mem_vif.rd_valid <= 0; 
         @(posedge mem_vif.resetn);
         repeat(10) @(posedge mem_vif.clk);
         `uvm_info(get_type_name(),"OUT OF RESET",UVM_LOW);
    endtask

    task axi_write_protocol(picorv32_axi_adapter_transaction tx);
        `uvm_info(get_type_name(),"Driving data",UVM_LOW)
        mem_vif.wr_valid <= 1;
        mem_vif.mem_data <= tx.mem_wdata;
        mem_vif.mem_addr <= tx.mem_addr;
        @(posedge mem_vif.clk);
        mem_vif.wr_valid <= 0;
        repeat(20) @(posedge mem_vif.clk);
    endtask

    task axi_read_protocol(picorv32_axi_adapter_transaction tx);
        `uvm_info(get_type_name(),"Reading data",UVM_LOW)
        mem_vif.rd_valid <= 1;
        mem_vif.mem_addr <= tx.mem_addr;
        @(posedge mem_vif.clk);
        mem_vif.rd_valid <= 0; 
        repeat(20) @(posedge mem_vif.clk);
    endtask

    task run_phase(uvm_phase phase);
        picorv32_axi_adapter_transaction tx;

        forever begin
            seq_item_port.get_next_item(tx);

            // Handle transaction based on type
            case (tx.trans_type)
                picorv32_axi_adapter_types::WRITE : axi_write_protocol(tx);
                picorv32_axi_adapter_types::READ  :  axi_read_protocol(tx);
                picorv32_axi_adapter_types::RESET :  run_reset();
            endcase

            seq_item_port.item_done();
        end
    endtask
endclass

