// picorv32_axi_adapter_monitor.sv
class picorv32_axi_adapter_monitor extends uvm_monitor;
    `uvm_component_utils(picorv32_axi_adapter_monitor)

    // Analysis port for sending observed transactions
    uvm_analysis_port#(picorv32_axi_adapter_transaction) analysis_port;

    // Virtual interface to the DUT
    virtual picorv32_axi_adapter_if vif;

    function new(string name = "picorv32_axi_adapter_monitor", uvm_component parent = null);
        super.new(name, parent);
        analysis_port = new("analysis_port", this);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual picorv32_axi_adapter_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set for monitor");
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            picorv32_axi_adapter_transaction tr;

            // Observe AXI read transactions
            if (vif.mem_axi_arvalid && vif.mem_axi_arready) begin
                tr = picorv32_axi_adapter_transaction::type_id::create("read_transaction");
                tr.mem_axi_arvalid = 1;
                tr.mem_axi_araddr = vif.mem_axi_araddr;
                tr.mem_axi_arprot = vif.mem_axi_arprot; // Ensure to capture prot

                // Wait for read data
                @(posedge vif.clk);
                while (!vif.mem_axi_rvalid) @(posedge vif.clk);
                tr.data_out = vif.mem_axi_rdata;
                tr.mem_axi_rready = 1; // Indicate readiness to accept data

                // Send the transaction through the analysis port
                analysis_port.write(tr);

                // Check for valid data
                if (tr.data_out === 32'hXXXXXXXX) begin
                    `uvm_error("MONITOR", "Invalid data received in read transaction");
                end

                // Reset the rready flag for the next transaction
                tr.mem_axi_rready = 0;
            end

            // Observe AXI write transactions
            if (vif.mem_axi_awvalid && vif.mem_axi_awready) begin
                tr = picorv32_axi_adapter_transaction::type_id::create("write_transaction");
                tr.mem_axi_awvalid = 1;
                tr.mem_axi_awaddr = vif.mem_axi_awaddr;
                tr.mem_axi_awprot = vif.mem_axi_awprot; // Ensure to capture prot
                tr.mem_axi_wdata = vif.mem_axi_wdata;
                tr.mem_axi_wstrb = vif.mem_axi_wstrb;

                // Check if wstrb indicates data presence
                if (vif.mem_axi_wstrb !== 4'b1111) begin
                    `uvm_warning("MONITOR", "Write transaction with incomplete strobe bits detected.");
                end

                // Send the transaction through the analysis port
                analysis_port.write(tr);
            end

            // Adding a delay to prevent busy-waiting
            @(posedge vif.clk); // Wait for the next clock edge
        end
    endtask
endclass



