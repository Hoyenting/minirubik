.text
main:
    li t0, 0x10000000
    li t1, 0x00010000      # 64 KiB

write_loop:
    sb zero, 0(t0)
    addi t0, t0, 1
    addi t1, t1, -1
    bnez t1, write_loop

hold:
    j hold