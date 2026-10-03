.text
main:
    li t0, 100000

loop:
    addi t1, t1, 1
    addi t2, t2, 1
    addi t3, t3, 1
    addi t0, t0, -1
    bnez t0, loop

    li a7, 10
    ecall