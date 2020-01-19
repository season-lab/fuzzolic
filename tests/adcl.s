.globl adcl

adcl:
    add $1, %edi
    movl $0xFFFFFFFF, %eax
    adc $0, %eax
    jc overflow
    movq $0, %rax
    ret
overflow:
    movq $1, %rax
    ret
