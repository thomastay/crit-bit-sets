namespace CritBits
// Implements a critical bit tree, aka PATRICIA tree
// Heavily inspired by these implementations:
// C: https://www.imperialviolet.org/binary/critbit.pdf
// Nim: https://github.com/nim-lang/Nim/blob/version-1-2/lib/pure/collections/critbits.nim

// A few notes for the reader:
// 1uy means treat 1 as an 8-bit unsigned integer:
//   in effect, one byte on any modern machine

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

    // Note: always returns a leaf node.
    // this is not encoded in the type system to match
    // the paper
    let rec walkTree (str: string) (node: Node): string =
        match node with
        | Leaf key -> key
        | Intermediate n ->
            // Calculate direction
            let (c: byte) =
                let nodeByte = n.byte
                if nodeByte < (String.length str)
                then byte str.[nodeByte]
                else 0uy
            let goLeft = goLeft n.otherBits c
            let nextNode =
                if goLeft then n.left else n.right
            walkTree str nextNode

    member val Count = 0 with get, set

    member _.Clear() =
        root <- None  // ahh... the good thing about having a GC...

    member _.Contains(str: string): bool =
        match root with
        | None -> false
        | Some n ->
            let key = walkTree str n
            key = str

    member _.Add(str: string): bool =
        match root with
        | None -> // empty tree
            root <- Some (Leaf str)
            true  // adding to empty tree succeeds
        | Some rootNode ->
            let bestMatch = walkTree str rootNode
            let uBytes = Encoding.UTF8.GetBytes str
            let pBytes = Encoding.UTF8.GetBytes bestMatch
            match findDifferingByte uBytes pBytes with
            | ValueNone -> false // insert has no effect if key exists
            | ValueSome (newByte, newOtherBits) ->
                let newOtherBits = (findDifferingBit newOtherBits) ^^^ 255uy
                let isStrGoesToRightChild = goLeft newOtherBits pBytes.[newByte]
                match rootNode with
                | Leaf _ ->
                    // unfortunately, need to special case
                    // the root node leaf case
                    let newNode =
                        if isStrGoesToRightChild
                        then constructNode newByte newOtherBits rootNode (Leaf str)
                        else constructNode newByte newOtherBits (Leaf str) rootNode
                    root <- Some newNode
                    true
                | Intermediate _ ->
                let rec updateParentForNewNode (q: NodeDatum): unit =
                    let c =
                        if q.byte < Array.length uBytes
                        then uBytes.[q.byte]
                        else 0uy
                    let direction = goLeft q.otherBits c
                    let nextNode =
                        if direction then q.left else q.right
                    match nextNode with
                    | Leaf _ ->
                        let newNode =
                            if isStrGoesToRightChild
                            then constructNode newByte newOtherBits nextNode (Leaf str)
                            else constructNode newByte newOtherBits (Leaf str) nextNode
                        // update parent node
                        if direction
                        then q.left <- newNode
                        else q.right <- newNode
                    | Intermediate x when
                        (x.byte > newByte) ||
                            (x.byte = newByte && x.otherBits > newOtherBits) ->
                        let newNode =
                            if isStrGoesToRightChild
                            then constructNode newByte newOtherBits nextNode (Leaf str)
                            else constructNode newByte newOtherBits (Leaf str) nextNode
                        // update parent node
                        if direction
                        then q.left <- newNode
                        else q.right <- newNode
                    | Intermediate x ->
                        updateParentForNewNode x
                true