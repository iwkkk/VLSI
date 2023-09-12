include "globals.mzn";


%---------------------- parameters ---------------------------------
int: w;   %  width of the rectangle
int: n;   %  number of rectangles
set of int:Rectangle=1..n;
array[Rectangle] of 0..w :width;  %  the width of every rectangle
array[Rectangle] of  int :height;  %  the height of every rectangle
int:maxHeight = sum(height); % sum of height
array[Rectangle] of var 0..w-min(width) :x; %  Rectangle's X on the coordinate
array[Rectangle] of var 0..maxHeight-min(height) :y; %  Rectangle's Y on the coordinate
var max(height)..maxHeight: h;

function int: biggest() = arg_max([height[i] | i in Rectangle]);
%----------------------- constraints --------------------------------
%width and height constraints
% maximum width
constraint max([x[i] + width[i] | i in Rectangle]) <= w;
% maximum heigth
constraint max([y[i] + height[i] | i in Rectangle]) = h;

constraint cumulative(y, height, width, w);
constraint cumulative(x, width, height, h);
%no overlap
constraint diffn(x, y, width, height); 


%symmetry breaking constraint
constraint symmetry_breaking_constraint(
  x[biggest()] == 0 /\ y[biggest()] == 0
);


% symmetry breaking for circuit with same width and height
constraint forall(r in Rectangle)(let {array[int] of int: R = [i | i in Rectangle where width[i]=width[r]
            /\ height[i]=height[r]]} 
            in if length(R)>1 /\ min(R)=r then 
            forall(i in index_set(R) where i>1)(
             lex_less([y[R[i-1]],x[R[i-1]]], [y[R[i]],x[R[i]]])
            )
            else true endif
);




solve 
::int_search(y, input_order, indomain_random,complete)
::int_search(x, input_order, indomain_random,complete)
::int_search([h], input_order, indomain_random, complete)
%::restart_geometric(1.5,100)
minimize h;



