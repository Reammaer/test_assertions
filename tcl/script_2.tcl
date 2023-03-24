

quit -sim

cd ../modelsim

vlib work

vlog -work work ../tb/tb_2.sv

vsim -novopt -t 1ns -sv_seed random -assertcover work.tb_2

add wave -divider "Top-level signals"
add wave -radix unsigned tb_2/*


run 10us