using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PermTracking
{
    class Point
    {
        public int x;
        public int y;
    }

    class Program
    {
        static void Main(string[] args)
        {
            IsolateTest("Test1", Test1);
        }

        static void IsolateTest(string name, Action test)
        {
            Console.WriteLine("TEST: " + name);
            PermTracking.TrackEnterScope();
            test();
            PermTracking.TrackLeaveScope();
            Console.WriteLine();
        }

        static void Test1()
        {
            Point p;
            p = new Point();
            PermTracking.TrackAlloc(p);

            p.x = 1;
            p.y = 2;

            Console.WriteLine("acc(p.x) = " + PermTracking.HavePerm(p, "x"));
            Console.WriteLine("acc(p.y) = " + PermTracking.HavePerm(p, "y"));

            Console.WriteLine("release acc(p.x);");
            PermTracking.TrackRelease(p, "x");

            Console.WriteLine("acc(p.x) = " + PermTracking.HavePerm(p, "x"));
            Console.WriteLine("acc(p.y) = " + PermTracking.HavePerm(p, "y"));
        }
    }
}
