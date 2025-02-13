# Following the guide to get your timing information (single clock) 

1. Put your code in ./source/dut

2. Change the clock period in ./constraint/timing_constrain.xdc

3. Open your vivado and change directory in command line to this directory

4. source project.tcl

5. Waiting for vivado to systhesis the project and reading the timing information to see if there is any setup problem