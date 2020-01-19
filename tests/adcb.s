.globl adcb

adcb:
    movl %edi, %eax
    add $1, %al
    movb $0xFF, %al
    adc $0, %al
    jc overflow
    movq $0, %rax
    ret
overflow:
    movq $1, %rax
    ret
