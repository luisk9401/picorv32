#----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2019.03
# platform  : Linux 3.10.0-1160.125.1.el7.x86_64
# version   : 2019.03p002 64 bits
# build date: 2019.06.01 18:04:02 PDT
#----------------------------------------
# started Sat Feb 22 13:10:03 UTC 2025
# hostname  : p1lg511249.dc01.its.hpecorp.net
# pid       : 28820
# arguments : '-label' 'session_0' '-console' 'p1lg511249:43546' '-style' 'windows' '-data' 'AQAAADx/////AAAAAAAAA3oBAAAAEABMAE0AUgBFAE0ATwBWAEU=' '-proj' '/v/288/ws3/moral/maestria/project_root/env/picosoc_env/jgproject/sessionLogs/session_0' '-init' '-hidden' '/v/288/ws3/moral/maestria/project_root/env/picosoc_env/jgproject/.tmp/.initCmds.tcl' 'run_formal_div.tcl'
clear -all
analyze +define+FORMAL -sv -f vc_file_div top_hdl_pcp_div.sv pcpi_div.v
elaborate -top hdl_top
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
visualize -violation -property <embedded>::top_hdl.sva_inst.assert_calculate_result -new_window
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
