clear -all
analyze +define+FORMAL -sv -f vc_file_div top_hdl_pcp_div.sv pcpi_div.v
elaborate -top top_hdl
clock clk
reset  (resetn==0)

prove -all
