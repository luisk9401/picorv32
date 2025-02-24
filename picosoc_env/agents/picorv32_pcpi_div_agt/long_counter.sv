module long_convergence_counter (
    input logic clk,
    input logic reset,
    input logic enable,
    output logic event_out
);
    logic [31:0] counter;

    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            counter <= 0;
        else if (enable)
            counter <= counter + 1;
    end

    assign event_out = (counter == 32'hFFFFFFFF);  // Event triggers at max count

   property long_convergence;
    @(posedge clk) disable iff (reset)
    enable |=> s_eventually (event_out); // Must eventually reach event_out
   endproperty
   assert property (long_convergence);

   // Coverage to track the assertion progress
   cover property (@(posedge clk) disable iff (reset) event_out);
   cover property (@(posedge clk) counter >= 32'h80000000);
endmodule
