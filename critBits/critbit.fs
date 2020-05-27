namespace CritBits
// Implements a critical bit tree, aka PATRICIA tree
// Heavily inspired by these implementations:
// C: https://www.imperialviolet.org/binary/critbit.pdf
// Nim: https://github.com/nim-lang/Nim/blob/version-1-2/lib/pure/collections/critbits.nim
// C: https://github.com/blynn/blt/blob/master/blt.c

// Main differences from the paper:
// - This code uses optimizations mentioned in Lynn, B. (2014).
//    In particular, we use their SWAR technique, and skip certain checks
//    when walking down the tree.
//    See blt.c for more details.
// - In the spirit of type safety, the code uses a discriminated union
//   instead of void * with LSB bit tag to model the domain.
//   A Node is now either a Leaf node,
//   or an Intermediate Node. This does lead to additional pointer chasing,
//   which harms the efficiency slightly.

// A few notes for the reader:
// - 1uy means treat 1 as an 8-bit unsigned integer:
//   in effect, one byte on the CLR
// - pt. n means Point number n in the paper,
//   e.g. pt. 5 refers to "Searching the Tree"
// - Recall that in .NET, strings are UTF-16.
//   So, we must cast the string to a byte array, using
//   some sort of decoding logic.
//   For simplicity, this library assumes a UTF-8 encoded string.
//   If necessary, you can change the encoding in the Add() function.

[<NoEquality>]
[<NoComparison>]
type Node =
    | Leaf of key: string
    | Intermediate of NodeDatum
and
    NodeDatum =
    { byte: int; // the byte that differs
     otherBits: byte; // a single byte where every bit except the critical bit is true
     mutable left: Node;
     mutable right: Node; }

open System.Text
open System.Numerics

module private Helpers =
    // Computes whether c has a 0 or a 1 in the crit bit position
    // marked out by otherBits
    // otherBits is a 8-bit byte which is all 1s except at one position
    // demarkating the critical bit.
    // e.g. otherBits = 11101111, c = 10110010
    // in this case, otherBits ||| c = 1111111
    // so the function returns false
    // e.g. otherBits = 01111111, c = 01110010
    // otherBits ||| c = 01111111
    // so, the function returns true
    let inline goLeft (otherBits: byte) (c: byte) =
        ((1 + int (otherBits ||| c)) >>> 8) = 0

    // finds the differing byte between strings: u and p
    // recall that p is the existing best match string,
    // and u is the string we are trying to match.
    // pt. 11
    let inline findDifferingByte (uBytes: byte[]) (pBytes: byte[]): struct (int * byte) voption =
        let rec helper newByte =
            if newByte >= Array.length uBytes then
                if Array.length pBytes = Array.length uBytes
                then ValueNone // no differing bits; arrays are identical
                else ValueSome struct (newByte, pBytes.[newByte]) // next available byte
            elif newByte >= Array.length pBytes then
                assert (Array.length uBytes > Array.length pBytes)
                ValueSome struct (newByte, uBytes.[newByte])
            else
                let p = pBytes.[newByte]
                let u = uBytes.[newByte]
                if p <> u
                then ValueSome struct (newByte, (p ^^^ u)) // found differing bit!
                else helper (newByte + 1) // loop()
        helper 0

    // Credit to Lynn
    // Given as input a byte,
    // returns a byte with every bit except one
    // which is the most significant differing bit
    // e.g. given as input 00101011
    // returns 11011111 (the opposite of 00100000)
    // pt. 12 (partial)
    let inline findDifferingBit (b: byte) =
        // SWAR trick that sets every bit after the leading bit to 1.
        let b = b ||| (b >>> 1)
        let b = b ||| (b >>> 2)
        let b = b ||| (b >>> 4)
        // Zero all the bits after the leading bit
        let z = b &&& ~~~(b >>> 1)
        ~~~z // invert --> somehow, this isn't done by Lynn's code. He must have found another hack.

    // experimental approach to calculating the bit mask
    let findDifferingBit2 (b: byte): byte =
        let leadingBit = BitOperations.Log2 (uint32 b)
        1uy <<< leadingBit

    let inline constructNode byte otherBits left right =
        Intermediate {byte=byte; otherBits=otherBits; left=left; right=right}

    // Optimization credited to Lynn
    // instead of doing two comparisons, this calcualtes
    // a total order of the pair (int, byte)
    // by shifting int by 8 then adding the byte, then doing
    // a regular integer comparison.
    // Less branches === happier branch predictor!
    //    Note: arguments not passed in as tuple for efficiency
    //    Tuple creation involves additional allocations, but this
    //    function is meant to be inlined.
    let inline compareNodes (a: int) (x: byte) (b: int) (y: byte): bool =
        (a <<< 8) + (int x) < (b <<< 8) + (int y)

open Helpers

// Implementation of a critical bit tree
// that can only store strings.
type CritBitTree() =
    let mutable root: Node option = None

    // Walks the tree, to find the leaf node
    // that has the closest match to uBytes
    // pt. 5 and 6
    let rec walkTree (uBytes: byte[]) (node: Node): string =
        match node with
        | Leaf key -> key
        | Intermediate n ->
            // Calculate direction
            let c =
                let nodeByte = n.byte
                if nodeByte < Array.length uBytes
                then uBytes.[nodeByte]
                else 0uy
            let isLeft = goLeft n.otherBits c
            let nextNode = if isLeft then n.left else n.right
            walkTree uBytes nextNode

    member val Count = 0 with get, set

    member _.Clear() =
        root <- None  // ahh... the good thing about having a GC...

    // pt. 3 Searching the tree
    member _.Contains(str: string): bool =
        match root with
        | None -> false  // pt. 4
        | Some n ->
            let uBytes = Encoding.UTF8.GetBytes str
            let key = walkTree uBytes n
            key = str   // pt. 7

    // Returns true if the add was successful
    // Returns false if the string is already in the tree
    // pt.8 Inserting into the Tree
    member this.Add(str: string): bool =
        match root with
        | None -> // pt. 9 (empty tree)
            root <- Some (Leaf str)
            this.Count <- 1
            true
        | Some rootNode ->
            let uBytes = Encoding.UTF8.GetBytes str
            let bestMatch = walkTree uBytes rootNode
            let pBytes = Encoding.UTF8.GetBytes bestMatch
            match findDifferingByte uBytes pBytes with
            | ValueNone -> false // insert has no effect if key exists
            | ValueSome (newByte, newOtherBits) ->
                // pt. 12 (partial)
                let newOtherBits = findDifferingBit newOtherBits
                let isStrGoesToRightChild =
                    if newByte >= Array.length pBytes
                    then goLeft newOtherBits 0uy
                    else goLeft newOtherBits pBytes.[newByte]
                // pt. 14 (Alloc new node)
                let inline makeNewNode oldNode =
                    if isStrGoesToRightChild
                    then constructNode newByte newOtherBits oldNode (Leaf str)
                    else constructNode newByte newOtherBits (Leaf str) oldNode
                // pt. 15 (Insert new node)
                match rootNode with
                | Leaf _ ->
                    // unfortunately, need to special case
                    // when the root node is a leaf, since we cannot take
                    // arbitrary pointers
                    root <- Some (makeNewNode rootNode)
                | Intermediate q when
                    compareNodes newByte newOtherBits q.byte q.otherBits ->
                    // If the root node's byte is smaller than newByte,
                    // we will have to replace root node with another
                    // intermediate. Unfortunately, another special case.
                    // This is because we can't modify random pointers in F#
                    root <- Some (makeNewNode rootNode)
                | Intermediate q ->
                    let rec updateParentForNewNode (q: NodeDatum) =
                        let c =
                            if q.byte < Array.length uBytes
                            then uBytes.[q.byte]
                            else 0uy
                        let isLeft = goLeft q.otherBits c
                        let nextNode = if isLeft then q.left else q.right
                        // helper function called in two places below
                        let inline updateParentNode() =
                            let newNode = makeNewNode nextNode
                            // update parent node
                            if isLeft
                            then q.left <- newNode
                            else q.right <- newNode
                        match nextNode with
                        | Leaf _ -> updateParentNode()
                        | Intermediate x when
                            compareNodes newByte newOtherBits x.byte x.otherBits ->
                            updateParentNode()
                        | Intermediate x ->
                            updateParentForNewNode x // loop()
                    updateParentForNewNode q
                // In all 3 Leaf and Intermediate cases, inc count
                this.Count <- this.Count + 1
                true