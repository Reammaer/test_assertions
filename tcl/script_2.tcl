

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
add wave tb_2/START_REQ_EN
add wave tb_2/START_REQ_EN_CV
add wave tb_2/START_ENV
add wave tb_2/START_ENV_CV

add wave -divider "Nonconsecutive Repetition"
add wave tb_2/clk
add wave tb_2/start_t
add wave tb_2/end_t
add wave tb_2/sent
add wave tb_2/START_END_SENT
add wave tb_2/START_END_SENT_CV

add wave -divider "Intersection"
add wave tb_2/clk
add wave tb_2/command;
add wave tb_2/write_complete;
add wave tb_2/read_complete;
add wave tb_2/INTERSECTION
add wave tb_2/INTERSECTION_CV

add wave -divider "Intersection ACK"
add wave tb_2/clk
add wave tb_2/req3;
add wave tb_2/ack;
add wave tb_2/ready3;
add wave tb_2/INTERSECTION_ACK
add wave tb_2/INTERSECTION_ACK_CV

run 3us