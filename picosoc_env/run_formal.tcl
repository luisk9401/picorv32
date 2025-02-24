clear -all
analyze +define+FORMAL -sv -f vc_file top_hdl.sv
elaborate -top hdl_top
clock clk
reset  (resetn==0)

prove -all
