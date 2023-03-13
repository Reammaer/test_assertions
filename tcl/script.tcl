

quit -sim

cd ../modelsim

vlib work

vlog -work work ../tb/tb.sv

vsim -novopt -t 1ns work.tb

add wave -divider "Top-level signals"
add wave -radix unsigned tb/*

run 10us