# 文件结构：
  -rtl文件夹： DUT设计相关的sv文件
  -tb文件夹 ： UVM验证平台与断言相关的sv文件
  -coverage_report.txt: 覆盖率报告
  -transcript：仿真输出


# For this design:

编译：
vlog +incdir+D:/questasim/questa_sim/verilog_src/uvm-1.2/src -cover sbceft C:/Users/Xypher/Desktop/master/SV/finalProject/my_design/tb/my_top.sv

仿真：
vsim -gui work.my_top -novopt -assertdebug -coverage -sv_lib D:/questasim/questa_sim/uvm-1.2/win64/uvm_dpi +UVM_TESTNAME=test0

输出覆盖率报告：
coverage report -output C:/Users/Xypher/Desktop/master/SV/finalProject/my_design/coverage_report.txt