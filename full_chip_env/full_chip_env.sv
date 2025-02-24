
//===============================================================
// Full Chip Level Environment
//===============================================================

// Full Chip Environment integrating spimemio, simpleuart, and picorv32
class fullchip_env extends uvm_env;
    spimemio_env spimemio_subenv;
    simpleuart_env simpleuart_subenv;
    picorv32_env picorv32_subenv; 
    `uvm_component_utils(fullchip_env)
endclass
