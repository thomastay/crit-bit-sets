namespace CritBits
// Implements a critical bit tree, aka PATRICIA tree
// Heavily inspired by these implementations:
// C: https://www.imperialviolet.org/binary/critbit.pdf
// Nim: https://github.com/nim-lang/Nim/blob/version-1-2/lib/pure/collections/critbits.nim

// A few notes for the reader:
// 1uy means treat 1 as an 8-bit unsigned integer:
//   in effect, one byte on any modern machine
// pt. n means Point number n in the paper
// e.g. pt. 5 refers to "Searching the Tree"

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

open System.Text;

module private Helpers =
    let inline goLeft (otherBits: byte) (c: byte) =
        ((1 + int (otherBits ||| c)) >>> 8) = 0

    // finds the differing byte between strings: str and u
    // Recall that in .NET, strings are UTF-16!
    // So, we must cast the string to a byte array, using
    // some sort of decoding logic
    // For simplicity, this library assumes a UTF-8 encoded string
    // If necessary, you can change the encoding in the Add() function
    // pt. 11
    let inline findDifferingByte (uBytes: byte[]) (pBytes: byte[]): struct (int * byte) voption =
        assert (Array.length pBytes >= Array.length uBytes)
        let rec helper newByte =
            if newByte >= Array.length uBytes
            then
                if Array.length pBytes = Array.length uBytes
                then ValueNone // no differing bits; arrays are identical
                else ValueSome struct (newByte, pBytes.[newByte]) // next available byte
            else
                let p = pBytes.[newByte]
                let u = uBytes.[newByte]
                if p <> u
                then ValueSome struct (newByte, (p ^^^ u)) // found differing bit!
                else helper (newByte + 1) // loop()
        helper 0

    // Given as input a byte,
    // returns a byte with only one bit set
    // which is the most significant differing bit
    // pt. 12 (partial)
    let rec findDifferingBit (newOtherBits: byte) =
        let a = newOtherBits &&& (newOtherBits - 1uy)
        if a = 0uy
        then newOtherBits
        else findDifferingBit a

    let inline constructNode byte otherBits left right =
        Intermediate {byte=byte; otherBits=otherBits; left=left; right=right}

open Helpers

// Implementation of a critical bit tree
// that can only store strings.
type CritBitTree() =
    let mutable root: Node option = None

    // Walks the tree, to find the leaf node
    // that has the closest match to uBytes
    // pt. 5
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
    member _.Add(str: string): bool =
        match root with
        | None -> // pt. 9 (empty tree)
            root <- Some (Leaf str)
            true
        | Some rootNode ->
            let uBytes = Encoding.UTF8.GetBytes str
            let bestMatch = walkTree uBytes rootNode
            let pBytes = Encoding.UTF8.GetBytes bestMatch
            match findDifferingByte uBytes pBytes with
            | ValueNone -> false // insert has no effect if key exists
            | ValueSome (newByte, newOtherBits) ->
                // pt. 12 (partial)
                let newOtherBits = (findDifferingBit newOtherBits) ^^^ 255uy
                let isStrGoesToRightChild = goLeft newOtherBits pBytes.[newByte]
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
                            (x.byte > newByte) ||
                                (x.byte = newByte && x.otherBits > newOtherBits) ->
                            updateParentNode()
                        | Intermediate x ->
                            updateParentForNewNode x // loop()
                    updateParentForNewNode q
                // In both Leaf and Intermediate cases, return true
                true