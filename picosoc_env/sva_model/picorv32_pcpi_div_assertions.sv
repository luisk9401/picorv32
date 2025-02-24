
// Define las funciones reutilizables para assertions y cover properties
function automatic logic is_div_instruction(logic [31:0] insn);
    return (insn[6:0] == 7'b0110011) && (insn[31:25] == 7'b0000001);
endfunction

function automatic logic is_valid_op(logic [2:0] funct3);
    return (funct3 == 3'b100) || (funct3 == 3'b101) || (funct3 == 3'b110) || (funct3 == 3'b111);
endfunction

function automatic logic is_start_condition(logic pcpi_wait, pcpi_wait_q);
    return pcpi_wait && !pcpi_wait_q;
endfunction

// Propiedad: Detectar instrucción de división/remanente
property p_instr_detected;
    @(posedge clk) disable iff (!resetn)
    (pcpi_valid && !pcpi_ready && is_div_instruction(pcpi_insn)) |=> instr_any_div_rem;
endproperty

// Propiedad: Detectar inicio de la operación de división
property p_start_condition;
    @(posedge clk) disable iff (!resetn)
    is_start_condition(pcpi_wait, pcpi_wait_q) |=> running;
endproperty

// Propiedad: Comprobar que la operación termina correctamente
property p_complete_operation;
    @(posedge clk) disable iff (!resetn)
    running && !quotient_msk |=> ##1 (pcpi_ready && pcpi_wr);
endproperty

// Propiedad: Validar que el resultado no sea desconocido
property p_output_valid;
    @(posedge clk) disable iff (!resetn)
    (pcpi_ready && pcpi_wr) |-> $isunknown(pcpi_rd) == 0;
endproperty

// Cobertura para formal y simulación
cover property (@(posedge clk) disable iff (!resetn) pcpi_valid && !pcpi_ready);
cover property (@(posedge clk) disable iff (!resetn) is_start_condition(pcpi_wait, pcpi_wait_q));
cover property (@(posedge clk) disable iff (!resetn) pcpi_ready);
cover property (@(posedge clk) disable iff (!resetn) instr_div);
cover property (@(posedge clk) disable iff (!resetn) instr_divu);
cover property (@(posedge clk) disable iff (!resetn) instr_rem);
cover property (@(posedge clk) disable iff (!resetn) instr_remu);
