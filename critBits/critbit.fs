namespace CritBits
// Implements a critical bit tree, aka PATRICIA tree
// Heavily inspired by these implementations:
// C: https://www.imperialviolet.org/binary/critbit.pdf
// Nim: https://github.com/nim-lang/Nim/blob/version-1-2/lib/pure/collections/critbits.nim
// C: https://github.com/blynn/blt/blob/master/blt.c

// Main differences from the paper:
// - The mask (called otherBits in the paper) is now just a regular bit mask
//   with 0s everywhere except a 1 in the crit bit position. Now just called mask.
//   Langley used his reverse-mask technique so as to be able
//   to compute the direction as an integer (0 or 1) with no branching.
//   However, since we explicitly encode the left and right pointers, and
//   we need a boolean to decide between them, the reverse-mask technique
//   is not needed.
// - Due to the above point, any comparison of otherBits is reversed.
//   See the function: compareNodes

// - This code uses optimizations mentioned in Lynn, B. (2014).
//    In particular, we use their SWAR technique, and tuple comparison checks
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
    {byte: int; // the byte that differs
     mask: byte; // 8bit mask with a 1 at the critical position.
     mutable left: Node;
     mutable right: Node; }

open System.Text
open System.Numerics

module private Helpers =
    // Computes whether c has a 0 or a 1 in the crit bit position
    // marked out by mask
    // mask is a 8-bit byte which has a 1 at exactly the critical bit
    // e.g. mask = 00010000, c = 10110010 -> true
    //      mask = 10000000, c = 01110010 -> false
    let inline goLeft (mask: byte) (c: byte) =
        (mask &&& c) = 0uy

    // TODO: optimize this! This is just crying out for SIMD
    // finds the differing byte between strings: u and p
    // recall that p is the existing best match string,
    // and u is the string we are trying to match.
    // pt. 11
    let inline findDifferingByte (uBytes: byte[]) (pBytes: byte[]): struct (int * byte) voption =
        let rec helper newByte =
            // The first two if checks are handling edge cases
            // when the loop counter (newByte) goes off the end of
            // either the uBytes or pBytes array.
            if newByte >= Array.length uBytes then
                if Array.length pBytes = Array.length uBytes
                then ValueNone // no differing bits; arrays are identical
                else ValueSome struct (newByte, pBytes.[newByte]) // next available byte
            elif newByte >= Array.length pBytes then
                assert (Array.length uBytes > Array.length pBytes)
                ValueSome struct (newByte, uBytes.[newByte])
            else // this is the meat of the code!
                let p = pBytes.[newByte]
                let u = uBytes.[newByte]
                if p <> u
                then ValueSome struct (newByte, (p ^^^ u)) // found differing bit!
                else helper (newByte + 1) // loop()
        helper 0

    // Credit to Lynn
    // Given as input a byte,
    // returns a mask with a 1 in the position of the leading bit of b
    // e.g. given as input 00101011
    // returns 00100000
    // pt. 12 (partial)
    let inline findDifferingBit (b: byte) =
        assert (b <> 0uy)
        // SWAR trick that sets every bit after the leading bit to 1.
        let b = b ||| (b >>> 1)
        let b = b ||| (b >>> 2)
        let b = b ||| (b >>> 4)
        // Zero all the bits after the leading bit
        b &&& ~~~(b >>> 1)

    // experimental approach to calculating the bit mask
    // uses hardware intrinsics exposed by .NET
    // to calculate the leading bit (called a binary log)
    let inline findDifferingBitv2 (b: byte): byte =
        assert (b <> 0uy)
        let leadingBit = BitOperations.Log2 (uint32 b)
        1uy <<< leadingBit

    let inline constructNode byte mask left right =
        Intermediate {byte=byte; mask=mask; left=left; right=right}

    // Optimization credited to Lynn
    // instead of doing two comparisons, this calcualtes
    // a total order of the pair (int, byte)
    // by shifting int by 8 then adding the byte, then doing
    // a regular integer comparison.
    // Less branches === happier branch predictor!
    // HOWEVER: if a = b and x < y,
    //     this means that y's leading bit comes FIRST
    //     so we want to stop if a = b and x > y
    //     This is a big deviation from the paper.
    //    Note: arguments not passed in as tuple for efficiency
    //    Tuple creation involves additional allocations, but this
    //    function is meant to be inlined.
    let inline compareNodes (a: int) (x: byte) (b: int) (y: byte): bool =
        (a <<< 8) + (int y) < (b <<< 8) + (int x)

    // Walks the tree, to find the leaf node
    // that has the closest match to uBytes
    // pt. 5 and 6
    let rec walkTree (uBytes: byte[]) (node: Node): string =
        match node with
        | Leaf key -> key
        | Intermediate n ->
            // If the differing byte (n.byte) is beyond the string
            // e.g. byte = 2 and uBytes is "to"
            // then the only possibility of finding a matching string
            // is to look leftwards! e.g., we might have a tree like:
            //           2
            //         /   \
            //      "to"   "towards"
            // Thus, we always go leftward in that case.
            let isLeft =
                let nodeByte = n.byte
                if nodeByte >= Array.length uBytes then true
                else goLeft n.mask uBytes.[nodeByte]
            let nextNode = if isLeft then n.left else n.right
            walkTree uBytes nextNode

    // prints the leaves under a specific node
    let leaves (node: Node): string list =
        let rec helper n =
            match n with
            | Leaf key -> [key]
            | Intermediate n ->
                List.append (helper n.left) (helper n.right)
        helper node

open Helpers

// Implementation of a critical bit tree
// that can only store strings.
type CritBitTree() =
    let mutable root: Node option = None

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
            key  = str // pt 7.

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
            | ValueNone -> false // insert has no effect if key exists.
            | ValueSome (newByte, newOtherBits) ->
                // pt. 12 (partial)
                let newMask = findDifferingBitv2 newOtherBits
                // If the differing byte (newByte) is beyond the original string
                // e.g. pBytes is "to", and uBytes is "too", newBytes = 3,
                // then the old Node must always go to left child, by construction.
                let isOldNodeGoesToLeftChild =
                    if newByte >= Array.length pBytes then true
                    else goLeft newMask pBytes.[newByte]
                // pt. 14 (Alloc new node)
                let inline makeNewNode oldNode =
                    if isOldNodeGoesToLeftChild
                    then constructNode newByte newMask oldNode (Leaf str)
                    else constructNode newByte newMask (Leaf str) oldNode
                // pt. 15 (Insert new node)
                match rootNode with
                | Leaf _ ->
                    // unfortunately, need to special case
                    // when the root node is a leaf, since we cannot take
                    // arbitrary pointers
                    root <- Some (makeNewNode rootNode)
                | Intermediate q when
                    compareNodes newByte newMask q.byte q.mask ->
                    // If the root node's byte is smaller than newByte,
                    // we will have to replace root node with another
                    // intermediate. Unfortunately, another special case.
                    // This is because we can't modify random pointers in F#
                    root <- Some (makeNewNode rootNode)
                | Intermediate q ->
                    let rec updateParentForNewNode (q: NodeDatum) =
                        assert (q.byte < Array.length uBytes) // unsure if this assertion holds?
                        let c =
                            if q.byte < Array.length uBytes
                            then uBytes.[q.byte]
                            else 0uy
                        let isLeft = goLeft q.mask c
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
                            compareNodes newByte newMask x.byte x.mask ->
                            updateParentNode()
                        | Intermediate x ->
                            updateParentForNewNode x // loop()
                    updateParentForNewNode q
                // In all 3 Leaf and Intermediate cases, inc count
                this.Count <- this.Count + 1
                true

    override _.ToString() =
        match root with
        | None -> "{}"
        | Some node ->
            let s =
                leaves node
                |> String.concat ","
            "{" + s + "}"