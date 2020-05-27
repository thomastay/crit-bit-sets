namespace critBits.Test

open Microsoft.VisualStudio.TestTools.UnitTesting
open System
open System.Collections.Generic
open CritBits

[<TestClass>]
type TestClass () =
    // credits to Laurent, from fssnippets
    // http://www.fssnip.net/L/title/Array-shuffle
    let rand = new Random()

    let swap (a: _[]) x y =
        let tmp = a.[x]
        a.[x] <- a.[y]
        a.[y] <- tmp

    // shuffle an array (in-place)
    let shuffle a =
        Array.iteri (fun i _ -> swap a i (rand.Next(i, Array.length a))) a

    [<TestMethod>]
    member _.TestEmpty () =
        let s = CritBitTree()
        Assert.IsTrue(s.Count = 0)
        Assert.IsFalse(s.Contains("potato"))

    [<TestMethod>]
    member _.TestSingle () =
        let s = CritBitTree()
        Assert.IsTrue(s.Add("a"))
        Assert.IsTrue(s.Count = 1)
        Assert.IsTrue(s.Contains("a"))

    [<TestMethod>]
    member _.``TestMultiple using single chars`` () =
        let s = CritBitTree()
        Assert.IsTrue(s.Add("a"))
        Assert.IsTrue(s.Add("b"))
        Assert.IsTrue(s.Add("c"))
        Assert.IsTrue(s.Count = 3)
        Assert.IsTrue(s.Contains("a"))
        Assert.IsTrue(s.Contains("b"))
        Assert.IsTrue(s.Contains("c"))

    [<TestMethod>]
    member _.``TestMultiple using multiple chars`` () =
        let s = CritBitTree()
        Assert.IsTrue(s.Add("iamapotato"))
        Assert.IsTrue(s.Add("bssd"))
        Assert.IsTrue(s.Add("!acc//''c"))
        Assert.IsTrue(s.Count = 3)
        Assert.IsFalse(s.Contains("a"))
        Assert.IsFalse(s.Contains("iamapotatv"))
        Assert.IsTrue(s.Contains("iamapotato"))
        Assert.IsTrue(s.Contains("bssd"))
        Assert.IsTrue(s.Contains("!acc//''c"))

    [<TestMethod>]
    member _.``Test rebalance root - from paper`` () =
        let s = CritBitTree()
        Assert.IsTrue(s.Add("\0"))
        Assert.IsTrue(s.Add("\1"))
        Assert.IsTrue(s.Add("\5"))
        Assert.IsTrue(s.Count = 3)

    [<TestMethod>]
    member _.``Test that walkTree supports prefixes`` () =
        let s = CritBitTree()
        Assert.IsTrue(s.Add("to"))
        Assert.IsTrue(s.Add("towards"))
        Assert.IsTrue(s.Contains("to"))
        Assert.IsFalse(s.Add("to"))

    [<TestMethod>]
    member _.``Test lots of inserts`` () =
        // data taken from the paper: Go, F# and Erlang by Jarleberg and Nilsson, 2012
        // Link: https://www.csc.kth.se/utbildning/kth/kurser/DD143X/dkand12/Group6Alexander/anders_jarleberg_kim_nilsson.rapport.pdf
        let data = "of each other and the only form of communication that can exist between twoor more processes is by sending each other messages.[10]Since different processes do not share memory with each other programmersdo not have to worry about dead-locks and race conditions when it comes tomaking programs run efficient on multi-core CPUs. This is what often makesErlang a good match for problems that are of a parallel nature. Another im-portant feature of Erlang is that it is possible to hot-swap code during runtime.This can be crucial for server applications that require a high uptime.The interest in Erlang has grown lately.[11] The reason for this is probablydue to its message passing style and how it simplifies concurrent programming.Erlang is not very common in the industry but can be seen occasionally, es-pecially when it comes to networking hardware such as routers. For example,a very successful ATM switch from Ericsson runs Erlang and as a proof of itsstability it has an uptime of 99.999999999 (nine nines).[12"
        let dataArr = data.Split()
        let s = CritBitTree()
        let hSet = HashSet()
        for word in dataArr do
            s.Add(word) |> ignore
            hSet.Add(word) |> ignore
        Assert.IsTrue(s.Count = hSet.Count)
        for word in dataArr do
            Assert.IsTrue(s.Contains(word))
        for word in hSet do
            Assert.IsTrue(s.Contains(word))

    [<TestMethod>]
    member _.``Test random 0-255`` () =
        for i in 1..255 do
            let bytes =
                [|0..i|]
                |> Array.map (fun i -> [|(char i)|] |> String)
            let s = CritBitTree()
            shuffle bytes
            bytes
            |> Array.iter (fun word -> s.Add(word) |> ignore)
            Assert.IsTrue(s.Count = i+1)
            [0..i]
            |> List.map (fun i -> [|char i|] |> String)
            |> List.iter (fun word -> Assert.IsTrue(s.Contains(word)))