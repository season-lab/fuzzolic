.globl addw

addw:
    addw $1, %di
    js jzero
jzero:
    jne zero
    movq $1, %rax
    ret
zero:
    movq $0, %rax
    ret
