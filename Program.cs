using System;
using System.Collections.Generic;
using System.Linq;
using Google.OrTools.LinearSolver;
using Google.OrTools.Sat;

namespace cuttingStockProblem
{
    class Program
    {
        public static List<List<int>> rolls(
            int nb, 
            List<List<int>> x, 
            List<(int quantity, int width)> demands
        ){
            var consumed_big_rolls = new List<List<int>>{};
            int num_orders = x.Count;

            for(int j = 0; j < x[0].Count; j++){
               var RR = new List<int> {};

               for(int i = 0; i < num_orders; i++){
                    if(x[i][j] > 0)
                        RR.AddRange(Enumerable.Repeat<int>(demands[i].width, x[i][j]));
               }

                consumed_big_rolls.Add(RR);
            }

            return consumed_big_rolls;
        }

        public static int SolVal(CpSolver solver, dynamic x){
            if(x is null) return 0;
            else{
                if(x is (int, float)) return x;
                else return Convert.ToInt32(solver.Value(x));
            }
        }

        public static List<int> SolValList(CpSolver solver, List<IntVar> x){
            var result = new List<int>{};

            x.ForEach(i => result.Add(SolVal(solver, i)));

            return result;
        }

        public static ((int, int) k, List<int> b) bounds(
            List<(int quantity, int width)> demands,
            int parent_width
        ){
            int num_orders = demands.Count;
            List<int> b = new List<int>{};
            int T = 0;
            var k = (0, 1);
            int TT = 0;
            int i = 0;
            while(i < num_orders){
                int quantity = demands[i].quantity;
                int width = demands[i].width;
                b.Add(Math.Min(quantity, parent_width/width));
                if(T + (quantity * width) <= parent_width){
                    T += (quantity * width);
                    TT += (quantity * width);
                }
                else {
                    while(quantity > 0){
                        if(T + width <= parent_width){
                            T += width;
                            TT += width;
                            quantity--;
                        }
                        else{
                            k.Item2++;
                            T = 0;
                        }
                    }
                }
                i++;
            }

            k.Item1 = (int)(Math.Ceiling((double)TT/(double)parent_width));

            return (k: k, b: b);
            
        }

        public static List<dynamic> SolveModel(
            List<(int quantity, int width)> demands,
            int parent_width,
            int constraintModel
        ){
            int num_orders = demands.Count;

            int minWidth = parent_width;
            demands.ForEach((item) => {
                if(item.width < minWidth) minWidth = item.width;
            });

            int maxWidth = 0;
            demands.ForEach((item) => {
                if(item.width > maxWidth) maxWidth = item.width;
            });

            var model = new CpModel();

            var kb = bounds(demands, parent_width);
            (int, int) k = kb.k; // (min, max) num of rolls that can be used
            List<int> b = kb.b;

            if(model is null) Console.WriteLine("IT IS NULL");
            var y = new List<IntVar> {};

            for(int i = 0; i < k.Item2; i++)
                y.Add(model.NewIntVar(0, 1, $"y_{i}"));

            var x = new List<List<IntVar>> {};
            for(int i = 0; i<num_orders; i++){

                var subList = new List<IntVar>{};

                for(int j = 0; j<k.Item2; j++)
                    subList.Add(model.NewIntVar(0, b[i], $"x_{i}_{j}"));

                x.Add(subList);

            }
            

            var unused_widths = new List<IntVar>{};
            for(int i = 0; i < k.Item2; i++)
                unused_widths.Add(model.NewIntVar(0, parent_width, $"w_{i}"));


            var nb = model.NewIntVar(k.Item1, k.Item2, "nb");

            

            for(int i = 0; i < num_orders; i++){
                var sum = x[0][0] * 0;
                x[i].ForEach((item) => sum += item);
                model.Add(sum == demands[i].quantity);
            }


            var boolVars = new List<BoolVar>{};

            // var diff = x[0][0] * 0;
            for(int j = 0; j < k.Item2; j++){

                var sum = x[0][0] * 0;
                for(int i = 0; i < num_orders; i++){
                    sum += demands[i].width * x[i][j];
                }
                // Console.WriteLine(sum.ToString());

                model.Add(sum <= parent_width*y[j]); 
                // Console.WriteLine((sum <= parent_width*y[j]).ToString());

                model.Add((parent_width*y[j] - sum) == unused_widths[j]);

                // var orBool = model.NewBoolVar("or");
                var currVar = model.NewBoolVar($"boolVar_{j}");
                
                switch(constraintModel){
                    case 1:
                        model.Add(unused_widths[j] < (maxWidth - minWidth)).OnlyEnforceIf(currVar);

                        model.Add(unused_widths[j] >= (maxWidth + minWidth)).OnlyEnforceIf(currVar.Not());
                        break;
                    
                    case 2:
                        model.Add(unused_widths[j] < (maxWidth - minWidth)).OnlyEnforceIf(currVar);

                        model.Add(unused_widths[j] >= maxWidth).OnlyEnforceIf(currVar.Not());
                        break;

                    case 3:
                        model.Add(unused_widths[j] < maxWidth).OnlyEnforceIf(currVar);

                        model.Add(unused_widths[j] >= maxWidth).OnlyEnforceIf(currVar.Not());
                        break;
                }


                boolVars.Add(currVar);
                // var or = solver.MakeIntVar(0, 1, "or");

                if(j < k.Item2 - 1){
                    var xSum1 = x[0][0] * 0;
                    for(int i = 0; i < num_orders; i++)
                        xSum1 += x[i][j];

                    var xSum2 = x[0][0] * 0;
                    for(int i = 0; i < num_orders; i++)
                        xSum2 += x[i][j + 1];

                    model.Add(xSum1 >= xSum2);
                }
            }

            var rollsSum = x[0][0] * 0;
            y.ForEach(i => rollsSum += i);

            model.Add(nb == rollsSum);

            var Cost = x[0][0] * 0;
            for(int i = 0; i < k.Item2; i++)
                Cost += (i+1)*y[i];

            
            model.Minimize(Cost);

            // solver.Maximize(diff);

            var solver = new CpSolver();

            var status = solver.Solve(model);

            

            var numRollsUsed = SolVal(solver, nb);

            var solved_x = new List<List<int>>{};
            x.ForEach(i => solved_x.Add(SolValList(solver, i)));


            return new List<dynamic>{
                status, // int
                numRollsUsed, // int
                rolls(numRollsUsed, solved_x, demands), // List<List<int>>
                SolValList(solver, unused_widths), // List<int>
                solver.WallTime() // long
            };
            // return new List<dynamic>{};
        }

        // public static List<dynamic> SolveModel(
        //     List<(int quantity, int width)> demands,
        //     int parent_width
        // ){
        //     int num_orders = demands.Count;

        //     int minWidth = parent_width;
        //     demands.ForEach((item) => {
        //         if(item.width < minWidth) minWidth = item.width;
        //     });

        //     int maxWidth = 0;
        //     demands.ForEach((item) => {
        //         if(item.width > maxWidth) maxWidth = item.width;
        //     });

        //     Solver solver = Solver.CreateSolver("SCIP");

        //     var kb = bounds(demands, parent_width);
        //     (int, int) k = kb.k; // (min, max) num of rolls that can be used
        //     List<int> b = kb.b;

        //     if(solver is null) Console.WriteLine("IT IS NULL");
        //     var y = new List<Variable> {};

        //     for(int i = 0; i < k.Item2; i++)
        //         y.Add(solver.MakeIntVar(0, 1, $"y_{i}"));

        //     var x = new List<List<Variable>> {};
        //     for(int i = 0; i<num_orders; i++){

        //         var subList = new List<Variable>{};

        //         for(int j = 0; j<k.Item2; j++)
        //             subList.Add(solver.MakeIntVar(0, b[i], $"x_{i}_{j}"));

        //         x.Add(subList);

        //     }
            

        //     var unused_widths = new List<Variable>{};
        //     for(int i = 0; i < k.Item2; i++)
        //         unused_widths.Add(solver.MakeNumVar(0, parent_width, $"w_{i}"));


        //     var nb = solver.MakeIntVar(k.Item1, k.Item2, "nb");

        //     for(int i = 0; i < num_orders; i++)
        //         solver.Add(x[i].ToArray().Sum() == demands[i].quantity);

        //     // var diff = x[0][0] * 0;
        //     for(int j = 0; j < k.Item2; j++){

        //         var sum = x[0][0] * 0;
        //         for(int i = 0; i < num_orders; i++){
        //             sum += demands[i].width * x[i][j];
        //         }
        //         // Console.WriteLine(sum.ToString());

        //         solver.Add(sum <= parent_width*y[j]); 
        //         // Console.WriteLine((sum <= parent_width*y[j]).ToString());

        //         solver.Add((parent_width*y[j] - sum) == unused_widths[j]);


        //         // var or = solver.MakeIntVar(0, 1, "or");

        //         if(j < k.Item2 - 1){
        //             var xSum1 = x[0][0] * 0;
        //             for(int i = 0; i < num_orders; i++)
        //                 xSum1 += x[i][j];

        //             var xSum2 = x[0][0] * 0;
        //             for(int i = 0; i < num_orders; i++)
        //                 xSum2 += x[i][j + 1];

        //             solver.Add(xSum1 >= xSum2);
        //         }
        //     }

        //     var rollsSum = x[0][0] * 0;
        //     y.ForEach(i => rollsSum += i);

        //     solver.Add(nb == rollsSum);

        //     var Cost = x[0][0] * 0;
        //     for(int i = 0; i < k.Item2; i++)
        //         Cost += (i+1)*y[i];

            
        //     solver.Minimize(Cost);

        //     // solver.Maximize(diff);

        //     var status = solver.Solve();

        //     var numRollsUsed = SolVal(nb);

        //     var solved_x = new List<List<int>>{};
        //     x.ForEach(i => solved_x.Add(SolValList(i)));


        //     return new List<dynamic>{
        //         status, // int
        //         numRollsUsed, // int
        //         rolls(numRollsUsed, solved_x, demands), // List<List<int>>
        //         SolValList(unused_widths), // List<int>
        //         solver.WallTime() // long
        //     };
        // }

        static void Main(string[] args)
        {
            string demandsString = Console.ReadLine();

            int totalLength = Convert.ToInt32(Console.ReadLine());

            string[] qv = demandsString.Split(" ");
            var demands = new List<(int quantity, int width)> {};
            for (int i = 0; i < qv.Length; i+=2)
            {
               demands.Add(
                    (
                        quantity: Convert.ToInt32(qv[i]), 
                        width: Convert.ToInt32(qv[i+1])
                    )
                );
            }

            var results = new List<dynamic>{};
            try{
                results = SolveModel(demands, totalLength, 1);
            }catch{
                try{
                    results = SolveModel(demands, totalLength, 2);
                }catch{
                    try{
                        results = SolveModel(demands, totalLength, 3);
                    }catch{
                        results = SolveModel(demands, totalLength, 4);
                    }
                }
            }
            
            Console.WriteLine($"Status: {results[0]}");
            Console.WriteLine();
            Console.WriteLine($"Number of Rolls Used: {results[1]}");
            Console.WriteLine();

            for(int i = 0; i < results[2].Count; i++)
            {
                if(results[2][i].Count == 0) continue;
                foreach (var num in results[2][i])
                {
                    Console.Write($" {num} ");
                }
                Console.Write($"   Waste: {results[3][i]}");
                Console.WriteLine();
            }
            Console.WriteLine();

        }
    }
public class SolutionPrinter : CpSolverSolutionCallback
{
    private IntVar[] v;
    SolutionPrinter(IntVar[] v){
        this.v = v;
    }

    public void VarArraySolutionPrinter(IntVar[] v){
        this.v = v;
    } 
    public override void OnSolutionCallback() {
        foreach (var item in v)
        {
           Console.WriteLine($"{item.Name()}: {Value(item)}") ;
        }
        // Console.WriteLine($"t1: {Value(v[0])}, t2: {Value(v[1])}");
    } 
}
}


// 10 12 4 14 20 35
// 60