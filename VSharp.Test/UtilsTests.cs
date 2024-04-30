using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Reflection.Metadata;
using System.Text;
using System.Timers;
using FSharpx.Collections;
using MessagePack.Internal;
using Microsoft.FSharp.Collections;
using Microsoft.FSharp.Core;
using NUnit.Framework;
using VSharp.CSharpUtils;
using VSharp;
using VSharp.Core;

namespace UnitTests
{
    [TestFixture]
    public sealed class UtilsTests
    {
        [Test]
        public void IdGeneratorTest1()
        {
            IdGenerator.reset();
            string v1 = IdGenerator.newId();
            string v2 = IdGenerator.newId();
            string f1 = IdGenerator.startingWith("Foo");
            string v3 = IdGenerator.startingWith("");
            string f2 = IdGenerator.startingWith("Foo");
            // Collision Foo11 should not happen!
            string f3 = IdGenerator.startingWith("Foo1");
            Assert.AreEqual(v1, "v#!1");
            Assert.AreEqual(v2, "v#!2");
            Assert.AreEqual(v3, "v#!3");
            Assert.AreEqual(f1, "Foo1");
            Assert.AreEqual(f2, "Foo2");
            Assert.AreEqual(f3, "Foo1!!1");
        }

        [Test]
        public void IdGeneratorTest2()
        {
            string v4 = IdGenerator.newId();
            string v5 = IdGenerator.newId();
            string f3 = IdGenerator.startingWith("Foo");

            IdGenerator.reset();
            string v1 = IdGenerator.startingWith("");
            string f1 = IdGenerator.startingWith("Foo");
            string f2 = IdGenerator.startingWith("Foo");
            Assert.AreEqual(v4, "v#!4");
            Assert.AreEqual(v5, "v#!5");
            Assert.AreEqual(f3, "Foo3");
            Assert.AreEqual(v1, "v#!1");
            Assert.AreEqual(f1, "Foo1");
            Assert.AreEqual(f2, "Foo2");

            IdGenerator.restore();
            string v6 = IdGenerator.startingWith("");
            string f4 = IdGenerator.startingWith("Foo");
            string f5 = IdGenerator.startingWith("Foo");
            Assert.AreEqual(v6, "v#!6");
            Assert.AreEqual(f4, "Foo4");
            Assert.AreEqual(f5, "Foo5");
        }

        private static heapArrayKey currentKey;
        private static FSharpFunc<heapArrayKey, bool> isDefault1 = FuncConvert.FromFunc<heapArrayKey, bool>(_ => false);
        [Test]
        public void SplittingBenchmark1()
        {
            var memory = new Memory.Memory();
            var spReading =
                FuncConvert.FromFunc<heapArrayKey, updateTreeKey<heapArrayKey, term>, term>((key, utKey) => memory.SpecializedReading(key, utKey));
            var inst = FuncConvert
                .FromFunc<Type,
                    memoryRegion<heapArrayKey,
                        productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>>, term>(MakeSymbolic);
            var region =
                new memoryRegion<heapArrayKey, productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>>(
                    typ: typeof(string),
                    nextUpdateTime: VectorTime.zero,
                    explicitAddresses: PersistentSet.empty<FSharpList<int>>(),
                    defaultValue: FSharpOption<term>.None,
                    updates: RegionTree
                        .empty<updateTreeKey<heapArrayKey, term>,
                            productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>>()
                );

            var symbolicValue = Terms.HeapRef(Terms.Constant("-1", new emptySource("123"), typeof(string)), typeof(string));
            
            var n = 50;
            
            var concreteKeys = new heapArrayKey[n];
            var symbolicKeys = new heapArrayKey[n];
            var address = Terms.Concrete(ListModule.OfSeq(new List<int>() {1}), TypeUtils.addressType);
            for (int i = 0; i < concreteKeys.Length; i++)
            {
                var z = i;
                concreteKeys[i] = heapArrayKey.NewOneArrayIndexKey(address, ListModule.OfSeq(new List<term>() {Terms.Concrete(z, typeof(int))}));
                symbolicKeys[i] = heapArrayKey.NewOneArrayIndexKey(address, ListModule.OfSeq(new List<term>() {Terms.Constant(z.ToString(), new emptySource("123"), typeof(int))}));
            }

            var currRegion = region;
            var timer = new Timer();
            var logs = new StringBuilder();
            var readsCount = 0;
            var writesCount = 0;
            var stopWatch = new Stopwatch();
            timer.Interval = 1000;
            timer.Elapsed += (sender, args) =>
            {
                logs.AppendLine(
                    $"{readsCount} {writesCount} {currRegion.nextUpdateTime.Head}");
                readsCount = 0;
                writesCount = 0;
            };
            timer.Enabled = true;
            stopWatch.Start();
            var k = 0;
            var runningTime = 30;
            while (stopWatch.Elapsed.Seconds < runningTime)
            {
                for (int j = 0; j < n; j++)
                {
                    if (stopWatch.Elapsed.Seconds > runningTime) break;
                    var read1 = MemoryRegion.read(currRegion, concreteKeys[j], isDefault1, inst, spReading);
                    readsCount++;
                    currentKey = symbolicKeys[j];
                    currRegion = MemoryRegion.write(currRegion, FSharpOption<term>.None, symbolicKeys[j], symbolicValue);
                    writesCount++;
                    var read2 = MemoryRegion.read(currRegion, concreteKeys[j], isDefault1, inst, spReading);
                    readsCount++;
                    currentKey = concreteKeys[j];
                    currRegion = MemoryRegion.write(currRegion, FSharpOption<term>.None, concreteKeys[j],
                        Terms.HeapRef(Terms.Concrete(VectorTime.zero, TypeUtils.addressType), typeof(string)));
                    writesCount++;
                    var read3 = MemoryRegion.read(currRegion, symbolicKeys[j], isDefault1, inst, spReading);
                    readsCount++;
                }

                k++;
            }

            timer.Enabled = false;
            using var writer = new StreamWriter("/home/overnight/study/read.txt", false);
            writer.Write(logs);
        }

        private FSharpFunc<heapArrayKey, string> mkName = FuncConvert.FromFunc<heapArrayKey, string>(_ => "asd");

        private FSharpFunc<state, FSharpFunc<heapArrayKey, bool>> isDeafult2 =
            FuncConvert.FromFunc<state, FSharpFunc<heapArrayKey, bool>>(state =>
                isDefault1);
        private term MakeSymbolic(Type typ,
            memoryRegion<heapArrayKey, productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>> mr)
        {
            Func<state,  memoryRegion<heapArrayKey, productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>>> e = state => mr;
            var extractor = FuncConvert.FromFunc(e);
            var arrayType = new arrayType(isVector: false, elemType: typeof(string), dimension: 1);
            var picker =
                new Memory.regionPicker<heapArrayKey,
                    productRegion<intervals<FSharpList<int>>, listProductRegion<points<int>>>>(
                    sort: regionSort.NewArrayIndexSort(arrayType), extract: extractor, mkName: mkName,
                    isDefaultRegion: true, isDefaultKey: isDeafult2);
            var source = new Memory.arrayReading(time: VectorTime.zero, key: currentKey, memoryObject: mr,
                picker: picker);
            return Terms.Constant("asd", source, typ);
        }

        public interface INothing {}
        public class Nothing : INothing {}
        

        public class GenericParametersKeeper<A, B, C, D, E, F, G, H, I, J>
            where A : B
            where B : J
            where C : struct
            where D : E, F
            where E : I
            where F : J, new()
            where G : H
            where H : Nothing
            where I : class
            where J : INothing
        {}

        private static Type[] GetGenericArguments()
        {
            var constructedType = typeof(GenericParametersKeeper<Nothing, Nothing, int, Nothing, object, Nothing, Nothing, Nothing, object, Nothing>);
            return constructedType.GetGenericTypeDefinition().GetGenericArguments();
        }

        [Test]
        public void IsReferenceTypeParameterTest()
        {
            // Testing "IsReferenceTypeParameter" function
            var genericArguments = GetGenericArguments();
            Assert.AreEqual(false, TypeUtils.isReferenceTypeParameter(genericArguments[0]));
            Assert.AreEqual(false, TypeUtils.isReferenceTypeParameter(genericArguments[1]));
            Assert.AreEqual(false, TypeUtils.isReferenceTypeParameter(genericArguments[2]));
            Assert.AreEqual(true, TypeUtils.isReferenceTypeParameter(genericArguments[3]));
            Assert.AreEqual(true, TypeUtils.isReferenceTypeParameter(genericArguments[4]));
            Assert.AreEqual(false, TypeUtils.isReferenceTypeParameter(genericArguments[5]));
            Assert.AreEqual(true, TypeUtils.isReferenceTypeParameter(genericArguments[6]));
            Assert.AreEqual(true, TypeUtils.isReferenceTypeParameter(genericArguments[7]));
            Assert.AreEqual(true, TypeUtils.isReferenceTypeParameter(genericArguments[8]));
            Assert.AreEqual(false, TypeUtils.isReferenceTypeParameter(genericArguments[9]));
        }

        [Test]
        public void IsValueTypeParameterTest()
        {
            // Testing "IsValueTypeParameter" function
            var genericArguments = GetGenericArguments();
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[0]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[1]));
            Assert.AreEqual(true, TypeUtils.isValueTypeParameter(genericArguments[2]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[3]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[4]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[5]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[6]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[7]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[8]));
            Assert.AreEqual(false, TypeUtils.isValueTypeParameter(genericArguments[9]));
        }

        private class Program
        {
            public static T G<T>(T x)
            {
                return x;
            }

            public static T F<T>(T x)
            {
                return x;
            }
        }

        [Test]
        public void TestGenericHashes()
        {
            var ts = typeof(Program).GetMethods();
            var f = ts[0].ReturnType;
            var g = ts[1].ReturnType;
            Assert.AreNotEqual(f, g);
            Assert.AreNotEqual(f.GetDeterministicHashCode(), g.GetDeterministicHashCode());
        }

        [TestFixture]
        public sealed class TypeSolverUtilsTests
        {
            private static FSharpList<T> ToFSharpList<T>(IEnumerable<T> collection)
            {
                var list = FSharpList<T>.Empty;
                foreach (var e in collection)
                {
                    list = FSharpList<T>.Cons(e, list);
                }

                return ListModule.Reverse(list);
            }

            private static typeConstraints ConstraintsFrom(
                IEnumerable<Type> supertypes,
                IEnumerable<Type> subtypes,
                IEnumerable<Type> notSupertypes,
                IEnumerable<Type> notSubtypes)
            {
                var empty = FSharpList<Type>.Empty;
                var supertypesFs = ToFSharpList(supertypes);
                var subtypesFs = ToFSharpList(subtypes);
                var notSupertypesFs = ToFSharpList(notSupertypes);
                var notSubtypesFs = ToFSharpList(notSubtypes);
                return typeConstraints.Create(empty, supertypesFs, subtypesFs, empty, notSupertypesFs, notSubtypesFs);
            }

            private static typeConstraints ConstraintsFrom(IEnumerable<Type> supertypes, IEnumerable<Type> subtypes)
            {
                var empty = FSharpList<Type>.Empty;
                return ConstraintsFrom(supertypes, subtypes, empty, empty);
            }

            private static typeConstraints ConstraintsFrom(IEnumerable<Type> supertypes)
            {
                var empty = FSharpList<Type>.Empty;
                return ConstraintsFrom(supertypes, empty);
            }

            [Test]
            public void IsContradictingGenericTest1()
            {
                Type[] supertypes = { typeof(object), typeof(List<int>).GetGenericTypeDefinition() };
                Type[] subtypes = { typeof(object) };
                var constraints = ConstraintsFrom(supertypes, subtypes);

                Assert.IsTrue(constraints.IsContradicting());
            }

            [Test]
            public void IsContradictingGenericTest2()
            {
                Type[] supertypes = { typeof(object), typeof(IEnumerable<int>).GetGenericTypeDefinition() };
                Type[] subtypes = { typeof(object) };
                var constraints = ConstraintsFrom(supertypes, subtypes);

                Assert.IsTrue(constraints.IsContradicting());
            }

            [Test]
            public void IsContradictingGenericTest3()
            {
                Type[] supertypes = { typeof(IEnumerable<int>).GetGenericTypeDefinition() };
                Type[] subtypes = { typeof(List<int>).GetGenericTypeDefinition() };
                var constraints = ConstraintsFrom(supertypes, subtypes);

                Assert.IsFalse(constraints.IsContradicting());
            }

            [Test]
            public void IsContradictingGenericTest4()
            {
                Type[] supertypes = { typeof(List<int>).GetGenericTypeDefinition() };
                Type[] subtypes = { typeof(IEnumerable<int>).GetGenericTypeDefinition() };
                var constraints = ConstraintsFrom(supertypes, subtypes);

                Assert.IsTrue(constraints.IsContradicting());
            }

            [Test]
            public void IsContradictingSpecialConstraintsTest1()
            {
                Type[] supertypes = { typeof(List<int>).GetGenericTypeDefinition() };
                var constraints = ConstraintsFrom(supertypes);
                var parameter = GetGenericArguments()[2]; // C
                var parameterConstraints = new typeParameterConstraints(parameter, constraints);

                Assert.IsTrue(parameterConstraints.IsContradicting());
            }

            [Test]
            public void IsContradictingSpecialConstraintsTest2()
            {
                Type[] supertypes = { typeof(IEnumerable<int>).GetGenericTypeDefinition() };
                var constraints = ConstraintsFrom(supertypes);
                var parameter = GetGenericArguments()[2]; // C
                var parameterConstraints = new typeParameterConstraints(parameter, constraints);

                Assert.IsFalse(parameterConstraints.IsContradicting());
            }

            [Test]
            public void IsContradictingSpecialConstraintsTest3()
            {
                Type[] supertypes = { typeof(int) };
                var constraints = ConstraintsFrom(supertypes);
                var parameter = GetGenericArguments()[8]; // I
                var parameterConstraints = new typeParameterConstraints(parameter, constraints);

                Assert.IsTrue(parameterConstraints.IsContradicting());
            }
        }
    }
}
