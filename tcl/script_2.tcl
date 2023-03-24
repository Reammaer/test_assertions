

quit -sim

cd ../modelsim

vlib work

vlog -work work ../tb/tb_2.sv

vsim -novopt -t 1ns -sv_seed random -assertcover work.tb_2

add wave -divider "Top-level signals"
add wave -radix unsigned tb_2/*

## Asseerts
add wave -divider "THROUGHTOUT"
add wave tb_2/EN_READ_WRITE_THROUGHTOUT
add wave tb_2/EN_READ_WRITE_THROUGHTOUT_CV

add wave -divider "GOTO 1"
add wave tb_2/REQ_DONE_READY
add wave tb_2/REQ_DONE_READY_CV

add wave -divider "GOTO 2"
# add wave tb_2/START_REQ_EN
# add wave tb_2/START_REQ_EN_CV
add wave tb_2/START_ENV
add wave tb_2/START_ENV_CV


run 3us