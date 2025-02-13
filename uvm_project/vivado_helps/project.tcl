# 设置工程名称和路径
set project_name "project"
set project_dir "./project"

# 设置 FPGA 器件型号
set part_name "xc7k70tfbg484-1"

# 设置源文件和约束文件路径
set source_dir "./source"
set constrain_dir "./constraint"

# 创建工程
create_project $project_name $project_dir -part $part_name

# 递归添加源文件
proc add_sources_recursive {dir} {

    if {![file exists $dir]} {
        puts "Directory $dir does not exist. Skipping..."
        return
    }


    # 获取文件夹中所有文件和子文件夹
    set files [glob -nocomplain -directory $dir -types f *]
    set subdirs [glob -nocomplain -directory $dir -types d *]

    # 添加文件到工程
    foreach file $files {
        add_files $file
    }

    # 递归处理子文件夹
    foreach subdir $subdirs {
        add_sources_recursive $subdir
    }
}

# 递归添加约束文件
proc add_constraints_recursive {dir} {
    # 获取文件夹中所有文件和子文件夹
    set files [glob -nocomplain -directory $dir -types f *]
    set subdirs [glob -nocomplain -directory $dir -types d *]

    # 添加文件到约束文件集
    foreach file $files {
        add_files -fileset constrs_1 $file
    }

    # 递归处理子文件夹
    foreach subdir $subdirs {
        add_constraints_recursive $subdir
    }
}

# 调用递归函数，添加源文件和约束文件
add_sources_recursive $source_dir
add_constraints_recursive $constrain_dir

# 设置顶层模块（根据实际情况修改顶层模块名称）
set_property top synthesis_top [current_fileset]


# 输出工程创建完成的消息
puts "Vivado project created successfully in $project_dir"

# 更新编译顺序使得其可以编译
update_compile_order -fileset sources_1

# 开始综合
launch_runs synth_1 -jobs 20

# 等待综合
wait_on_run synth_1

# 打开综合报告
open_run synth_1 -name synth_1

# 获取综合的时序报告
report_timing_summary -delay_type min_max -report_unconstrained -check_timing_verbose -max_paths 10 -input_pins -routable_nets -name timing_1