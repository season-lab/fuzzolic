.globl adcq

adcq:
    add $1, %rdi
    movq $0xFFFFFFFFFFFFFFFF, %rax
    adc $0, %rax
    jc overflow
    movq $0, %rax
    ret
overflow:
    movq $1, %rax
    ret
