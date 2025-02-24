-access +rwc
-gui
# Specify the test to run
+UVM_TESTNAME=picorv32_axi_adapter_test

# Directories for includes
+incdir+/v/288/ws3/moral/maestria/picorv32/picorv32/
+incdir+/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt

# List of all files needed for Simulation
/v/288/ws3/moral/maestria/picorv32/picorv32/picorv32.v
picov_tb.sv
