using System;
using System.Collections.Generic;
using System.Linq;
using Google.OrTools.LinearSolver;

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

        public static int SolVal(dynamic x){
            if(x is null) return 0;
            else{
                if(x is (int, float)) return x;
                else return Convert.ToInt32(x.SolutionValue());
            }
        }

        public static List<int> SolValList(List<Variable> x){
            var result = new List<int>{};

            x.ForEach(i => result.Add(SolVal(i)));

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
            int parent_width
        ){
            int num_orders = demands.Count;

            Solver solver = Solver.CreateSolver("SCIP");

            var kb = bounds(demands, parent_width);
            (int, int) k = kb.k; // (min, max) num of rolls that can be used
            List<int> b = kb.b;

            if(solver is null) Console.WriteLine("IT IS NULL");
            var y = new List<Variable> {};

            for(int i = 0; i<k.Item2; i++)
                y.Add(solver.MakeIntVar(0, 1, $"y_{i}"));

            var x = new List<List<Variable>> {};
            for(int i = 0; i<num_orders; i++){

                var subList = new List<Variable>{};

                for(int j = 0; j<k.Item2; j++)
                    subList.Add(solver.MakeIntVar(0, b[i], $"x_{i}_{j}"));

                x.Add(subList);

            }
            
            var unused_widths = new List<Variable>{};
            for(int i = 0; i < k.Item2; i++)
                unused_widths.Add(solver.MakeNumVar(0, parent_width, $"w_{i}"));


            var nb = solver.MakeIntVar(k.Item1, k.Item2, "nb");

            for(int i = 0; i < num_orders; i++)
                solver.Add(x[i].ToArray().Sum() == demands[i].quantity);

            for(int j = 0; j < k.Item2; j++){

                var sum = x[0][0] * 0;

                for(int i = 0; i < num_orders; i++){
                    sum += demands[i].width * x[i][j];
                }
                // Console.WriteLine(sum.ToString());

                solver.Add(sum <= parent_width*y[j]); 
                // Console.WriteLine((sum <= parent_width*y[j]).ToString());

                solver.Add((parent_width*y[j] - sum) == unused_widths[j]);

                if(j < k.Item2 - 1){
                    var xSum1 = x[0][0] * 0;
                    for(int i = 0; i < num_orders; i++)
                        xSum1 += x[i][j];

                    var xSum2 = x[0][0] * 0;
                    for(int i = 0; i < num_orders; i++)
                        xSum2 += x[i][j + 1];

                    solver.Add(xSum1 >= xSum2);
                }
            }

            var rollsSum = x[0][0] * 0;
            y.ForEach(i => rollsSum += i);

            solver.Add(nb == rollsSum);

            var Cost = x[0][0] * 0;
            for(int i = 0; i < k.Item2; i++)
                Cost += (i+1)*y[i];
            
            solver.Minimize(Cost);

            var status = solver.Solve();

            var numRollsUsed = SolVal(nb);

            var solved_x = new List<List<int>>{};
            x.ForEach(i => solved_x.Add(SolValList(i)));


            return new List<dynamic>{
                status, // int
                numRollsUsed, // int
                rolls(numRollsUsed, solved_x, demands), // List<List<int>>
                SolValList(unused_widths), // List<int>
                solver.WallTime() // long
            };
        }

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

            var results = SolveModel(demands, totalLength);
            
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
}


// 10 12 4 14 20 35
// 60