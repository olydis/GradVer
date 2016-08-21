using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace PermTracking
{
    struct Acc
    {
        private WeakReference o;
        private string f;
        private int hash;

        public Acc(object o, string f)
        {
            this.o = new WeakReference(o);
            this.f = f;
            this.hash = o.GetHashCode() + f.GetHashCode();
        }

        public override bool Equals(object obj)
        {
            if (obj is Acc)
            {
                Acc other = (Acc)obj;
                if (other.f != f)
                    return false;
                if (other.o.Target != o.Target)
                    return false;
                return true;
            }
            return false;
        }
        public override int GetHashCode()
        {
            return hash;
        }
    }
    static class PermTracking
    {
        [ThreadStatic]
        static Stack<HashSet<Acc>> permStack;

        static void Init()
        {
            if (permStack == null)
            {
                permStack = new Stack<HashSet<Acc>>();
                permStack.Push(new HashSet<Acc>());
            }
        }

        public static void TrackAlloc(object o)
        {
            Init();
            var addTo = permStack.Peek();
            foreach (var field in o.GetType().GetFields())
                if (!addTo.Add(new Acc(o, field.Name)))
                    throw new InvalidOperationException("duplicate access");
        }
        public static void TrackRelease(Acc a)
        {
            Init();
            var remFrom = permStack.Peek();
            if (!remFrom.Remove(a))
                throw new InvalidOperationException("unknown access");
        }
        public static void TrackRelease(object o, string f)
        {
            TrackRelease(new Acc(o, f));
        }

        public static bool HavePerm(Acc a)
        {
            Init();
            return permStack.Peek().Contains(a);
        }
        public static bool HavePerm(object o, string f)
        {
            return HavePerm(new Acc(o, f));
        }

        public static void TrackEnterScope(params Acc[] a)
        {
            Init();
            var remFrom = permStack.Peek();
            var addTo = new HashSet<Acc>();
            permStack.Push(addTo);

            foreach (var acc in a)
            {
                if (!remFrom.Remove(acc))
                    throw new InvalidOperationException("unknown access");
                if (!addTo.Add(acc))
                    throw new InvalidOperationException("duplicate access");
            }
        }

        public static void TrackLeaveScope()
        {
            Init();
            var remFrom = permStack.Pop();
            var addTo = permStack.Peek();
            foreach (var acc in remFrom)
                if (!addTo.Add(acc))
                    throw new InvalidOperationException("duplicate access");
        }
    }
}
