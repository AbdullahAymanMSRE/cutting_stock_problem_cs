using System;
using System.Collections.Generic;
using System.Linq;
using Google.OrTools.LinearSolver;
using Google.OrTools.Sat;
namespace cuttingStockProblem
{
    public class Program
    {
        static List<List<int>> rolls(
            int nb, 
            List<List<int>> x, 
            List<(int quantity, int length)> demands
        ){
            var consumed_big_rolls = new List<List<int>>{};
            int num_orders = x.Count;

            for(int j = 0; j < x[0].Count; j++){
               var RR = new List<int> {};

               for(int i = 0; i < num_orders; i++){
                    if(x[i][j] > 0)
                        RR.AddRange(Enumerable.Repeat<int>(demands[i].length, x[i][j]));
               }

                consumed_big_rolls.Add(RR);
            }

            return consumed_big_rolls;
        }

        static int SolVal(CpSolver solver, dynamic x){
            if(x is null) return 0;
            else{
                if(x is (int, float)) return x;
                else return Convert.ToInt32(solver.Value(x));
            }
        }

        static List<int> SolValList(CpSolver solver, List<IntVar> x){
            var result = new List<int>{};

            x.ForEach(i => result.Add(SolVal(solver, i)));

            return result;
        }

        static ((int, int) k, List<int> b) bounds(
            List<(int quantity, int length)> demands,
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
                int length = demands[i].length;
                b.Add(Math.Min(quantity, parent_width/length));
                if(T + (quantity * length) <= parent_width){
                    T += (quantity * length);
                    TT += (quantity * length);
                }
                else {
                    while(quantity > 0){
                        if(T + length <= parent_width){
                            T += length;
                            TT += length;
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

        public static (
            string status,
            int numRollsUsed,
            List<List<int>> rolls,
            List<int> waste
            ) SolveModel(
            List<(int quantity, int length)> demands,
            int parent_width,
            int constraintModel
        ){
            int num_orders = demands.Count;

            int minWidth = parent_width;
            demands.ForEach((item) => {
                if(item.length < minWidth) minWidth = item.length;
            });

            int maxWidth = 0;
            demands.ForEach((item) => {
                if(item.length > maxWidth) maxWidth = item.length;
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
                    sum += demands[i].length * x[i][j];
                }
                // Console.WriteLine(sum.ToString());

                model.Add(sum <= parent_width*y[j]); 
                // Console.WriteLine((sum <= parent_width*y[j]).ToString());

                model.Add((parent_width*y[j] - sum) == unused_widths[j]);

                // var currVar = model.NewBoolVar($"boolVar_{j}");
                
                // switch(constraintModel){
                //     case 1:
                //         model.Add(unused_widths[j] < (maxWidth - minWidth)).OnlyEnforceIf(currVar);

                //         model.Add(unused_widths[j] >= (maxWidth + minWidth)).OnlyEnforceIf(currVar.Not());
                //         break;
                    
                //     case 2:
                //         model.Add(unused_widths[j] < (maxWidth - minWidth)).OnlyEnforceIf(currVar);

                //         model.Add(unused_widths[j] >= maxWidth).OnlyEnforceIf(currVar.Not());
                //         break;

                //     case 3:
                //         model.Add(unused_widths[j] < maxWidth).OnlyEnforceIf(currVar);

                //         model.Add(unused_widths[j] >= maxWidth).OnlyEnforceIf(currVar.Not());
                //         break;
                // }


                // boolVars.Add(currVar);

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

            var sumDiffs = x[0][0] * 0;
            for(int a = 0 ; a < (unused_widths.Count - 1); a++){
                sumDiffs += unused_widths[a] + unused_widths[a+1];
            }

            model.Maximize(sumDiffs);
            model.Minimize(Cost);

            // solver.Maximize(diff);

            var solver = new CpSolver();

            var status = solver.Solve(model);

            var numRollsUsed = SolVal(solver, nb);

            var solved_x = new List<List<int>>{};
            x.ForEach(i => solved_x.Add(SolValList(solver, i)));

            return (
                status: $"{status}", // string
                numRollsUsed: numRollsUsed, // int
                rolls: rolls(numRollsUsed, solved_x, demands), // List<List<int>>
                waste: SolValList(solver, unused_widths)
            );
        }
        public static (
            string status,
            int numRollsUsed,
            List<List<int>> rolls,
            List<int> waste
            ) CutRolls(
            List<(int quantity, int length)> demands,
            int parent_width
        ){
            (string status,int numRollsUsed,List<List<int>> rolls,List<int> waste) results;  

                try{
                    results = SolveModel(demands, parent_width, 1);
                }catch{
                    try{
                        results = SolveModel(demands, parent_width, 2);
                    }catch{
                        try{
                            results = SolveModel(demands, parent_width, 3);
                        }catch{
                            results = SolveModel(demands, parent_width, 4);
                        }
                    }
                }

            return results;
        }

        static void Main(string[] args)
        {
            // input format
            // <demands in from <quantity> <length>>
            // <length of roll>
            string demandsString = Console.ReadLine();

            int totalLength = Convert.ToInt32(Console.ReadLine());

            string[] qv = demandsString.Split(" ");
            var demands = new List<(int quantity, int length)> {};
            for (int i = 0; i < qv.Length; i+=2)
            {
                int quantity = Convert.ToInt32(qv[i]);
                int length = Convert.ToInt32(qv[i+1]);

                if(length > totalLength){
                    int q = length/totalLength;
                    length = length % totalLength;

                    demands.Add(
                        (
                            quantity: q * quantity,
                            length: totalLength
                        )
                    );
                }

                if(length != 0)
                    demands.Add(
                            (
                                quantity: quantity, 
                                length: length
                            )
                        );
            }
            foreach(var demand in demands){
                Console.WriteLine($"qu: {demand.quantity} , le: {demand.length}");
            }
            var results = CutRolls(demands, totalLength);
            
            Console.WriteLine($"Status: {results.status}");
            Console.WriteLine();
            Console.WriteLine($"Number of Rolls Used: {results.numRollsUsed}");
            Console.WriteLine();

            for(int i = 0; i < results.rolls.Count; i++)
            { if(results.rolls[i].Count == 0) continue;
                foreach (var num in results.rolls[i])
                {
                    Console.Write($" {num} ");
                }
                Console.Write($"   Waste: {results.waste[i]}");
                Console.WriteLine();
            }
            Console.WriteLine();

        }

    }
}