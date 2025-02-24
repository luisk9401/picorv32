// Agent for simpleuart
class simpleuart_agent extends uvm_agent;
    simpleuart_if vif;
    // Instantiate driver, monitor, and sequencer here
    `uvm_component_utils(simpleuart_agent)
endclass
