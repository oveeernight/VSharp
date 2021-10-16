﻿using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Runtime.Serialization;
using System.Reflection;
using System.Linq;

namespace VSharp.TestRunner
{
    public static class Program
    {

        private static IEnumerable<string> _extraAssemblyLoadDirs;

        private static Assembly TryLoadAssemblyFrom(object sender, ResolveEventArgs args)
        {
            var existingInstance = AppDomain.CurrentDomain.GetAssemblies().FirstOrDefault(assembly => assembly.FullName == args.Name);
            if (existingInstance != null)
            {
                return existingInstance;
            }
            foreach (string path in _extraAssemblyLoadDirs)
            {
                string assemblyPath = Path.Combine(path, new AssemblyName(args.Name).Name + ".dll");
                if (!File.Exists(assemblyPath))
                    return null;
                Assembly assembly = Assembly.LoadFrom(assemblyPath);
                return assembly;
            }

            return null;
        }

        private static bool StructurallyEqual(object expected, object got)
        {
            Debug.Assert(expected != null && got != null && expected.GetType() == got.GetType());
            var flags = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance;
            var fields = expected.GetType().GetFields(flags);
            foreach (var field in fields)
            {
                if (!CompareObjects(field.GetValue(expected), field.GetValue(got)))
                {
                    return false;
                }
            }

            return true;
        }

        private static bool ContentwiseEqual(Array expected, Array got)
        {
            Debug.Assert(expected != null && got != null && expected.GetType() == got.GetType());
            if (expected.Rank != got.Rank)
                return false;
            for (int i = 0; i < expected.Rank; ++i)
                if (expected.GetLength(i) != got.GetLength(i) || expected.GetLowerBound(i) != got.GetLowerBound(i))
                    return false;
            var enum1 = expected.GetEnumerator();
            var enum2 = got.GetEnumerator();
            while (enum1.MoveNext() && enum2.MoveNext())
            {
                if (!CompareObjects(enum1.Current, enum2.Current))
                    return false;
            }
            return true;
        }

        private static bool CompareObjects(object expected, object got)
        {
            if (expected == null)
                return got == null;
            if (got == null)
                return false;
            var type = expected.GetType();
            if (type != got.GetType())
                return false;
            if (type.IsPrimitive || expected is string || type.IsEnum)
            {
                // TODO: compare double with epsilon?
                return got.Equals(expected);
            }

            if (expected is Array array)
                return ContentwiseEqual(array, got as Array);
            return StructurallyEqual(expected, got);
        }

        private static int ShowUsage()
        {
            Console.Error.WriteLine("V# test runner tool. Accepts unit test in *.vst format, runs the target executable with the specified input data.\n" +
                                    "\n" +
                                    "Usage: {0} <test directory or *.vst file>", AppDomain.CurrentDomain.FriendlyName);
            return 2;
        }

        public static int Main(string[] args)
        {
            if (args.Length != 1)
            {
                return ShowUsage();
            }

            string path = args[0];
            IEnumerable<FileInfo> tests;
            var runExactTest = false;
            if (Directory.Exists(path))
            {
                var dir = new DirectoryInfo(path);

                tests = dir.EnumerateFiles("*.vst");
            }
            else if (File.Exists(path))
            {
                var fi = new FileInfo(path);
                tests = new List<FileInfo> {fi};
                runExactTest = true;
            }
            else
            {
                return ShowUsage();
            }

            AppDomain.CurrentDomain.AssemblyResolve += TryLoadAssemblyFrom;

        bool atLeastOneTestFound = false;
            foreach (FileInfo fi in tests)
            {
                atLeastOneTestFound = true;
                try
                {
                    using (FileStream stream = new FileStream(fi.FullName, FileMode.Open, FileAccess.Read))
                    {
                        UnitTest test = UnitTest.Deserialize(stream);
                        _extraAssemblyLoadDirs = test.ExtraAssemblyLoadDirs;

                        var method = test.Method;
                        // TODO: support generic arguments?
                        bool hasThis = method.CallingConvention.HasFlag(CallingConventions.HasThis);

                        // TODO: support virtual methods by passing explicit declaring type?
                        object thisObj = hasThis && method.DeclaringType != null
                            ? FormatterServices.GetUninitializedObject(method.DeclaringType)
                            : null;
                        object[] parameters = test.Args ?? method.GetParameters()
                            .Select(t => FormatterServices.GetUninitializedObject(t.ParameterType)).ToArray();
                        var ex = test.Exception;
                        try
                        {
                            object result = null;
                            if (!test.IsError || runExactTest)
                                result = method.Invoke(thisObj, parameters);
                            if (ex != null)
                            {
                                Console.Error.WriteLine("Test {0} failed! Expected exception {1} was not thrown",
                                    fi.Name, ex);
                                return 6;
                            }
                            if (!CompareObjects(test.Expected, result))
                            {
                                // TODO: use NUnit?
                                Console.Error.WriteLine("Test {0} failed! Expected {1}, but got {2}", fi.Name,
                                    test.Expected ?? "null",
                                    result ?? "null");
                                return 5;
                            }
                        }
                        catch (TargetInvocationException e)
                        {
                            if (e.InnerException != null && e.InnerException.GetType() == ex)
                                Console.WriteLine("Test {0} throws expected error!", fi.Name);
                            else if (e.InnerException != null) throw e.InnerException;
                            else throw;
                        }
                    }
                }
                catch (Exception e)
                {
                    Console.Error.WriteLine("Error ({0}): {1}", fi.Name, e);
                    return 2;
                }

                Console.WriteLine("{0} passed!", fi.Name);
            }

            if (!atLeastOneTestFound)
            {
                Console.Error.WriteLine("No *.vst tests found in {0}", path);
            }

            return 0;
        }
    }
}
