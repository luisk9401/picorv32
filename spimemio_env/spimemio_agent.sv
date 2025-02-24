// Agent for spimemio
class spimemio_agent extends uvm_agent;
    spimemio_if vif;
    // Instantiate driver, monitor, and sequencer here
    `uvm_component_utils(spimemio_agent)
endclass
