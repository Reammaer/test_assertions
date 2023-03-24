

quit -sim

cd ../modelsim

vlib work

vlog -work work ../tb/tb_2.sv

vsim -novopt -t 1ns -sv_seed random -assertcover work.tb_2

add wave -divider "Top-level signals"
add wave -radix unsigned tb_2/*

## Asseerts
add wave tb_2/EN_READ_WRITE_THROUGHTOUT
add wave tb_2/EN_READ_WRITE_THROUGHTOUT_CV


run 3us