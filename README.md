# PicoRV32 Verification for Master's Thesis

This repository is part of a **Master’s Degree Thesis** that explores the **reuse of test components between formal verification and simulation** in a UVM-based verification environment. The research aims to develop a methodology that allows shared components, such as drivers and checkers, to be utilized effectively in both verification domains.

## Repository Structure

![image](https://github.com/user-attachments/assets/23a1af19-82c3-4e37-9753-7e821449468c)

```
📂 picorv32/
 ├── 📂 full_chip_env/      # Full-chip UVM environment integrating all submodules
 ├── 📂 picosoc_env/        # UVM environment for the PicoSoC module containts axidapter and div reutilzation module
 ├── 📂 simpleuart_env/     # UVM SKELENTON environment for the SimpleUART module
 ├── 📂 spimemio_env/       # UVM  SKELENTON environment for the SpiMemIO module
 ├── 📜 README.md           # This file
```

## Key Features of the Verification Approach

- **UVM-Based Verification:** Implements a structured test environment using Universal Verification Methodology.
- **Reusable Drivers:** Separates synthesizable drivers for formal verification and encapsulates them for reuse in simulation.
- **Assertions for Both Domains:** Develops SystemVerilog Assertions (SVA) that can be utilized in simulation and formal verification.
- **Testbench Structure:** The verification environment follows a modular structure as shown in the image:
![image](https://github.com/user-attachments/assets/0d339956-cba7-49b7-b2ec-dc8f3fec58fa)


  - **Tophvl (Testbench High-Level):** Contains the **TestCase**, sequences, and components for coverage collection and checking.
  - **Environment:** Organizes the UVM components, including agents and the scoreboard.
  - **Agent:** Includes **Monitor, Driver, and Sequencer**, interacting with the DUT through a **Virtual Interface**.
  - **Tophdl (Testbench Hardware-Level):** Contains the **DUT (Design Under Test)** and its interfaces.
  - **Formal Driver:** A synthesizable component for formal verification, ensuring compatibility across verification domains.
  - **Synthesizable vs Non-Synthesizable Components:**
    - *Synthesizable components* (orange) include the DUT, Virtual Interface, and Formal Driver.
    - *Non-synthesizable components* (green) include test cases, sequences, and standard UVM drivers.
    - *Coverage, assertions, and scoreboard* (red) track and validate functional correctness.

## Running the Verification

To run simulation-based verification:
```sh
run_simulation
```

To run formal verification:
```sh
 run_formal
```

## Thesis Contribution

This work proposes a novel approach to improving the efficiency and maintainability of verification environments by enabling **component reuse between formal and simulation domains**. The methodology applied here can be extended to other verification projects, reducing redundancy and increasing test effectiveness.

---
