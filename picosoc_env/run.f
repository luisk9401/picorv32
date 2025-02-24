
# Enable SystemVerilog and UVM

-64
-uvmhome $UVM_HOME
-timescale 1ns/1ns

-linedebug,
# Simulation settings
-access +rwc

# Specify the test to run
+UVM_TESTNAME=picorv32_axi_adapter_test

# Directories for includes
+incdir+/v/288/ws3/moral/maestria/picorv32/picorv32/
+incdir+/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt

# List of all files needed for Simulation
/v/288/ws3/moral/maestria/picorv32/picorv32/picorv32.v
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/axi4lite_slave_emulator.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt/picorv32_axi_adapter_types.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt/picorv32_axi_adapter_if.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt/picorv32_mem_if.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/sva_model/picorv32_axi_adapter_assertions.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt/formal_picorv32_axi_adapter_driver.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/agents/picorv32_axi_adapter_agt/picorv32_axi_adapter_pkg.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/sequences/sequences_pkg.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/picorv32_env.sv
/v/288/ws3/moral/maestria/project_root/env/picosoc_env/test/picorv32_axi_adapter_test.sv
top_hdl.sv
top_hvl.sv
