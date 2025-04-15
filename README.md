# Custom Malloc Implementation

A custom memory allocator implementing `malloc`, `free`, `calloc`, and `realloc` in C.



## Introduction

This project is a custom dynamic memory allocator based on a **segregated explicit free list**. It is optimized for performance on trace files supplied by lecturer.

## Design

### Allocation Algorithm

- **Segregated Explicit Free List**: Free blocks are divided into different size classes ("buckets").
- **Placement Policy**: LIFO (Last-In-First-Out) 
- **Search Policy**: Best-fit/First-fit within the selected bucket (best-fit results in lower fragmentation)

### Buckets

- Bucket sizes start from `MINBLOCK` and increase by a factor of 2.
- This allows for logarithmic bucket class search, and best-fit approximation.



## Block Structure

### Allocated Block

```
[ Header (size | used) ][ Payload ][ Padding ][ Footer (size | used) ]
```

### Free Block 

```
[ Header ][ Prev Pointer ][ Next Pointer ][ Payload ][ Footer ]
```



### Minimum Free Block Size: 32 bytes  
  - Header: 4 bytes  
  - Footer: 4 bytes  
  - Prev pointer: 8 bytes  
  - Next pointer: 8 bytes  
  - Alignment to 16 bytes

# Sources
- *Computer Systems: A Programmer's Perspective (CSAPP)*
- [CS351 Malloc Slides (IIT)](https://moss.cs.iit.edu/cs351/slides/slides-malloc.pdf)
- [Doug Lea’s Malloc](https://gee.cs.oswego.edu/dl/html/malloc.html)


# Notes

All files except `mm.c` were supplied by lecturer.

**Run Tests:**
```bash
make grade
```
