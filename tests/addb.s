.globl addb

addb:
    movl %edi, %eax
    addb $1, %al
    js jzero
jzero:
    jne zero
    movq $1, %rax
    ret
zero:
    movq $0, %rax
    ret
