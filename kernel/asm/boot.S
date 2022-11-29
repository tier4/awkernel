#include "device/raspi.S"

.global save_context

save_context:
    stp     x2,  x3,  [x0, #16 * 1]
    stp     x4,  x5,  [x0, #16 * 2]
    stp     x6,  x7,  [x0, #16 * 3]
    stp     x8,  x9,  [x0, #16 * 4]
    stp     x10, x11, [x0, #16 * 5]
    stp     x12, x13, [x0, #16 * 6]
    stp     x14, x15, [x0, #16 * 7]
    stp     x16, x17, [x0, #16 * 8]
    stp     x18, x19, [x0, #16 * 9]
    stp     x20, x21, [x0, #16 * 10]
    stp     x22, x23, [x0, #16 * 11]
    stp     x24, x25, [x0, #16 * 12]
    stp     x26, x27, [x0, #16 * 13]
    stp     x28, x29, [x0, #16 * 14]

    mrs     x2, elr_el1
    mrs     x3, spsr_el1

    stp     lr,  x2,  [x0, #16 * 15]
    str     w3,       [x0, #16 * 16]

    mov     x2,  sp
    str     x2,       [x0, #16 * 16 + 8]

    mov     x2,  x0
    mov     x0,  #1
    stp     x0,  x1,  [x2, #16 * 0]

    mov     x0, #0 // return 0
    ret

#include "exception.S"
