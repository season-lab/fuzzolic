.globl addl

addl:
    addl $1, %edi
    js jzero
jzero:
    jne zero
    movq $1, %rax
    ret
zero:
    movq $0, %rax
    ret
