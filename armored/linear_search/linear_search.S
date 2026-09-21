// Armored Corp AArch64 linear search: unsigned 64-bit, first match.
//
// Interface:
//   x0 = address of the first uint64_t element of the array
//   x1 = number of elements (length)
//   x2 = target value
//
// Returns (in x0):
//   the index of the FIRST element equal to the target
//   UINT64_MAX if no element matches (including length == 0)
//
// Notes:
//   - scans from index 0 upward
//   - only reads array memory, never writes it
//   - unsigned bounds logic: loop while index < length (b.hs = unsigned ">= ")
//   - deliberately simple and unoptimized

    .section .text
    .globl linear_search
    .type linear_search, %function
linear_search:
    mov     x3, xzr                 // index = 0
loop:
    cmp     x3, x1                  // index - length (unsigned)
    b.hs    not_found               // index >= length  ->  return UINT64_MAX
    ldr     x4, [x0, x3, lsl #3]   // x4 = array[index]
    cmp     x4, x2                  // element - target
    b.eq    found                   // element == target  ->  return index
    add     x3, x3, #1              // index++
    b       loop                    // goto loop
not_found:
    mvn     x0, xzr                 // x0 = UINT64_MAX = 0xffffffffffffffff
    ret
found:
    mov     x0, x3                  // x0 = index
    ret
    .size linear_search, .-linear_search