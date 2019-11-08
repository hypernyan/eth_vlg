
onerror {resume}
quietly WaveActivateNextPane {} 0

add wave -noupdate -divider -height 40 {TESTBENCH INTERFACE}

if [regexp {mem_arb_tb/rst} [find signals mem_arb_tb/rst]]                     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/rst}
if [regexp {mem_arb_tb/clk} [find signals mem_arb_tb/clk]]                     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/clk}


add wave -noupdate -divider -height 40 {ARBITER INTERFACE}

if [regexp {mem_arb_tb/dut/fifo_v}  [find signals mem_arb_tb/dut/fifo_v]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_v}
if [regexp {mem_arb_tb/dut/fifo_i}  [find signals mem_arb_tb/dut/fifo_i]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_i}
if [regexp {mem_arb_tb/dut/fifo_r}  [find signals mem_arb_tb/dut/fifo_r]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_r}
if [regexp {mem_arb_tb/dut/fifo_o}  [find signals mem_arb_tb/dut/fifo_o]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_o}
if [regexp {mem_arb_tb/dut/fifo_f}  [find signals mem_arb_tb/dut/fifo_f]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_f}
if [regexp {mem_arb_tb/dut/fifo_e}  [find signals mem_arb_tb/dut/fifo_e]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/fifo_e}
if [regexp {mem_arb_tb/dut/act_dl}  [find signals mem_arb_tb/dut/act_dl]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/act_dl}
if [regexp {mem_arb_tb/dut/act}     [find signals mem_arb_tb/dut/act]]     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/act}
if [regexp {mem_arb_tb/dut/act_ms}  [find signals mem_arb_tb/dut/act_ms]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/act_ms}
if [regexp {mem_arb_tb/dut/req_v}   [find signals mem_arb_tb/dut/req_v]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/req_v}
if [regexp {mem_arb_tb/dut/emp_v}   [find signals mem_arb_tb/dut/emp_v]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/emp_v}
if [regexp {mem_arb_tb/dut/ind_dl}  [find signals mem_arb_tb/dut/ind_dl]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/ind_dl}
if [regexp {mem_arb_tb/dut/ind}     [find signals mem_arb_tb/dut/ind]]     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/ind}
if [regexp {mem_arb_tb/dut/cur}     [find signals mem_arb_tb/dut/cur]]     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/cur}
if [regexp {mem_arb_tb/dut/cur_v}     [find signals mem_arb_tb/dut/cur_v]]     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/cur_v}
if [regexp {mem_arb_tb/dut/rdy}     [find signals mem_arb_tb/dut/rdy]]     {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/rdy}

add wave -noupdate -divider -height 40 {MEMORY ARBITER INTERFACE}

if [regexp {mem_arb_tb/dut/r_nw}   [find signals mem_arb_tb/dut/r_nw]]  {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/r_nw}
if [regexp {mem_arb_tb/dut/v_i}    [find signals mem_arb_tb/dut/v_i]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/v_i}
if [regexp {mem_arb_tb/dut/a_i}    [find signals mem_arb_tb/dut/a_i]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/a_i}
if [regexp {mem_arb_tb/dut/d_i}    [find signals mem_arb_tb/dut/d_i]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/d_i}
if [regexp {mem_arb_tb/dut/v_o}    [find signals mem_arb_tb/dut/v_o]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/v_o}
if [regexp {mem_arb_tb/dut/a_o}    [find signals mem_arb_tb/dut/a_o]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/a_o}
if [regexp {mem_arb_tb/dut/d_o}    [find signals mem_arb_tb/dut/d_o]]   {add wave -noupdate -format Logic -radix hexadecimal mem_arb_tb/dut/d_o}

TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
configure wave -namecolwidth 201
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
update
WaveRestoreZoom {0 ps} {20 us}
