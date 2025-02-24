
// pcpi_div_sva.sv
// SVA Model with Enhanced Properties and Functions for pcpi_div_if
module pcpi_div_sva(
    pcpi_div_if pcpi_if
);

    // Function to check if the instruction is DIV
    function is_div();
        is_div = (pcpi_if.pcpi_insn[14:12] == 3'b100);
    endfunction

    // Function to check if the instruction is DIVU
    function is_divu();
        is_divu = (pcpi_if.pcpi_insn[14:12] == 3'b101);
    endfunction

    // Function to check if the instruction is REM
    function is_rem();
        is_rem = (pcpi_if.pcpi_insn[14:12] == 3'b110);
    endfunction

    // Function to check if the instruction is REMU
    function is_remu();
        is_remu = (pcpi_if.pcpi_insn[14:12] == 3'b111);
    endfunction

    // Property: Ready should follow Valid within 10 cycles
    /*property valid_then_ready_bounded;
        @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
        pcpi_if.pcpi_valid |-> ##[1:10] pcpi_if.pcpi_ready;
    endproperty
    assert_valid_then_ready_bounded: assert property (valid_then_ready_bounded) else $error("Valid not followed by Ready within 10 cycles");
   */
    // Property: pcpi_wr should be asserted only when pcpi_ready is high
    property write_when_ready;
        @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
        pcpi_if.pcpi_wr |-> pcpi_if.pcpi_ready;
    endproperty
    assert_write_when_ready: assert property (write_when_ready) else $error("Write asserted without Ready");

    // Property: Wait should be high during processing
    /*property wait_during_processing;
        @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
        (pcpi_if.pcpi_valid && !pcpi_if.pcpi_ready) |-> pcpi_if.pcpi_wait;
    endproperty
    assert_wait_during_processing: assert property (wait_during_processing) else $error("Wait not asserted during processing");*/

    // Property: Data integrity check
    property data_integrity;
        @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
        pcpi_if.pcpi_wr |-> (pcpi_if.pcpi_rd !== 'bx);
    endproperty
    assert_data_integrity: assert property (data_integrity) else $error("Invalid Data on pcpi_rd");

    // Cover properties to ensure all operations are exercised
    cover_div: cover property (@(posedge pcpi_if.clk) is_div());
    cover_divu: cover property (@(posedge pcpi_if.clk) is_divu());
    cover_rem: cover property (@(posedge pcpi_if.clk) is_rem());
    cover_remu: cover property (@(posedge pcpi_if.clk) is_remu());



// Function to normalize negative zero to positive zero
function automatic signed normalize_zero(input signed [31:0] value);
    normalize_zero = (value === -'sd0) ? 'sd0 : value;
endfunction

// Property: Calculate Result Based on Inputs with Negative Zero Handling
property calculate_result;
    @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
    (pcpi_if.pcpi_valid && pcpi_if.pcpi_ready && !pcpi_if.pcpi_wait) |->
    (pcpi_if.pcpi_rd == (is_div()  ? normalize_zero($signed(pcpi_if.pcpi_rs1) / $signed(pcpi_if.pcpi_rs2)) :
                         is_divu() ? (pcpi_if.pcpi_rs1 / pcpi_if.pcpi_rs2) :
                         is_rem()  ? normalize_zero($signed(pcpi_if.pcpi_rs1) % $signed(pcpi_if.pcpi_rs2)) :
                         is_remu() ? (pcpi_if.pcpi_rs1 % pcpi_if.pcpi_rs2) : 'bx));
endproperty
assert_calculate_result: assert property (calculate_result) else $error("Incorrect Result Calculation");


// Property: Assume Instruction Remains Constant Until Ready is High
property assume_instruction_constant;
    @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
    (pcpi_if.pcpi_valid && !pcpi_if.pcpi_ready) |-> 
    $stable(pcpi_if.pcpi_insn);
endproperty
assume_instruction_constant_only: assume property (assume_instruction_constant);

// Property: Assume rs1 and rs2 Remain Constant During Calculation
property assume_rs1_rs2_constant;
    @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
    (pcpi_if.pcpi_valid && !pcpi_if.pcpi_ready) |-> 
    (pcpi_if.pcpi_rs1 == $past(pcpi_if.pcpi_rs1) && pcpi_if.pcpi_rs2 == $past(pcpi_if.pcpi_rs2));
endproperty
assume_rs1_rs2_constant_only: assume property (assume_rs1_rs2_constant);

// Property: Assume Valid Goes Low Only After Ready is High
property assume_valid_then_ready;
    @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
    (pcpi_if.pcpi_valid && !$past(pcpi_if.pcpi_ready)) |-> $stable(pcpi_if.pcpi_valid);
endproperty
assume_valid_then_ready_only: assume property (assume_valid_then_ready);


    // Property: Assume Valid Instructions Only
    property assume_valid_instructions;
      @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
      pcpi_if.pcpi_valid |-> (is_div() || is_divu() || is_rem() || is_remu());
    endproperty
    assume_valid_instructions_only: assume property (assume_valid_instructions);

property assume_rs2_non_zero;
    @(posedge pcpi_if.clk) disable iff (!pcpi_if.resetn)
    pcpi_if.pcpi_valid && (is_div() || is_divu() || is_rem() || is_remu()) |-> (pcpi_if.pcpi_rs2 != 0);
endproperty
assume_rs2_non_zero_only: assume property (assume_rs2_non_zero);
endmodule
