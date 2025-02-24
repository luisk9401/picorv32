#----------------------------------------
# JasperGold Version Info
# tool      : JasperGold 2019.03
# platform  : Linux 3.10.0-1160.125.1.el7.x86_64
# version   : 2019.03p002 64 bits
# build date: 2019.06.01 18:04:02 PDT
#----------------------------------------
# started Sat Feb 22 13:02:42 UTC 2025
# hostname  : p1lg511249.dc01.its.hpecorp.net
# pid       : 28033
# arguments : '-label' 'session_0' '-console' 'p1lg511249:41175' '-style' 'windows' '-data' 'AQAAADx/////AAAAAAAAA3oBAAAAEABMAE0AUgBFAE0ATwBWAEU=' '-proj' '/v/288/ws3/moral/maestria/project_root/env/picosoc_env/jgproject/sessionLogs/session_0' '-init' '-hidden' '/v/288/ws3/moral/maestria/project_root/env/picosoc_env/jgproject/.tmp/.initCmds.tcl'
include /v/288/ws3/moral/maestria/project_root/env/picosoc_env/run_formal_div.tcl
set_capture_elaborated_design on
analyze -verilog {/v/288/ws3/moral/maestria/project_root/env/picosoc_env/pcpi_div.v} ; analyze -sv {/v/288/ws3/moral/maestria/project_root/env/picosoc_env/top_hdl_pcp_div.sv} ; 
elaborate -top {picorv32_pcpi_div}
elaborate -top {top_hdl}
set_elaborate_single_run_mode off

elaborate -top {top_hdl}
analyze -sv {/v/288/ws3/moral/maestria/project_root/env/picosoc_env/top_hdl_pcp_div.sv} ; 
elaborate -top {top_hdl}
