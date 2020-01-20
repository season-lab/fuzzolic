.globl addq

addq:
    addq $1, %rdi
    js jzero
jzero:
    jne zero
    movq $1, %rax
    ret
zero:
    movq $0, %rax
    ret
