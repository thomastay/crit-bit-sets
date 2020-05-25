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
[<Struct>]
type NodeDatum =
    | Intermediate of left: Node option * right: Node option
    | Leaf of key: string
and
    [<NoEquality>]
    [<NoComparison>]
    Node =
    { byte: int32; // the byte that differs
     otherBits: byte; // a single byte where every bit except the critical bit is true
     data: NodeDatum; }

module private Helpers =
    let inline goLeft (otherBits: byte) (c: byte) =
        ((1 + int (otherBits ||| c)) >>> 8) = 0

    open System.Text;
    // finds the differing byte between strings: str and u
    // Recall that in .NET, strings are UTF-16!
    // So, we must cast the string to a byte array, using
    // some sort of decoding logic
    // For simplicity, this library assumes a UTF-8 encoded string
    // If necessary, you can change the encoding here.
    let inline findDifferingByte (str: string) (bestMatch: string) =
        let uBytes = Encoding.UTF8.GetBytes str // u, p to match the paper
        let pBytes = Encoding.UTF8.GetBytes bestMatch
        assert (Array.length pBytes >= Array.length uBytes)
        let rec helper newByte =
            if newByte >= Array.length uBytes
            then
                if Array.length pBytes = Array.length uBytes
                then ValueNone // no differing bits; arrays are identical
                else ValueSome pBytes.[newByte] // next available byte
            else
                let p = pBytes.[newByte]
                let u = uBytes.[newByte]
                if p <> u
                then ValueSome (p ^^^ u) // found differing bit!
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

open Helpers

// Implementation of a critical bit tree
// that can only store strings.
type CritBitTree() =
    let mutable root: Node option = None

    // Note: always returns a leaf node.
    // this is not encoded in the type system to match
    // the paper
    let rec walkTree (str: string) (n: Node): Node =
        match n.data with
        | Leaf key -> n
        | Intermediate (l, r) ->
            // Calculate direction
            let (c: byte) =
                let nodeByte = n.byte
                if nodeByte < (String.length str)
                then byte str.[nodeByte]
                else 0uy
            let goLeft = goLeft n.otherBits c
            let nextNode =
                if goLeft then l else r
                |> Option.get // if this fails, it is an error
            walkTree str nextNode

    member val Count = 0 with get, set

    member _.Contains(str: string): bool =
        match root with
        | None -> false
        | Some n ->
            let n = walkTree str n
            match n.data with
            | Leaf key -> key = str
            | Intermediate(_, _) -> failwith "walkTree always returns a leaf node"

    member _.Insert(str: string) =
        match root with
        | None -> // empty tree
            root <- Some {byte=0; otherBits=0uy; data= Leaf str;}
        | Some root ->
            let n = walkTree str root
            match n.data with
            | Leaf bestMatch ->
                match findDifferingByte str bestMatch with
                | ValueNone -> () // insert has no effect if key exists
                | ValueSome newByte ->
                    let newOtherBits = findDifferingBit newByte
                    let newOtherBits = newOtherBits ^^^ 255uy
                    let c = bestMatch.[newByte]
                    let direction = goLeft newOtherBits c
                    // allocate new node
                    let newNode: Node =
                        {byte = newByte;
                        otherbits = newOtherBits;
                        }
            | Intermediate(_, _) -> failwith "walkTree always returns a leaf node"