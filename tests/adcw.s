.globl adcw

adcw:
    add $1, %di
    movw $0xFFFF, %ax
    adc $0, %ax
    jc overflow
    movq $0, %rax
    ret
overflow:
    movq $1, %rax
    ret
