include "globals.mzn";
%------------- parameters -------------------
int: w;   %  width of the silicon plate
int: n;   %  number of necessary rectangle
set of int:Rectangle=1..n;
array[Rectangle] of 0..w:width;  %  the width of every rectangle
array[Rectangle] of int:height;  %  the height of every rectangle
int:maxHeight = sum(i in Rectangle)(max(width[i],height[i])); % max height in rotation
array[Rectangle] of var 0..w:x; %  rectangle's X on the coordinate
array[Rectangle] of var 0..maxHeight:y; %  rectangle's Y on the coordinate
array[Rectangle] of var bool: rotation;
% if rotate, rectangle's width will be height
array[Rectangle] of var 0..w: width_r = [if rotation[i] then height[i] else width[i] endif | i in Rectangle];
array[Rectangle] of var int: height_r = [if rotation[i] then width[i] else height[i] endif | i in Rectangle];


var 0..maxHeight: h;
function int: biggest() = arg_max([height[i] | i in Rectangle]);
%-------- consraints -----------------
%width and height constraints
% maximum width
constraint max([x[i] + width_r[i] | i in Rectangle]) <= w;
% maximum heigth
constraint max([y[i] + height_r[i] | i in Rectangle]) = h;
% a rectangle cannot be rotated if its height is greater than w
constraint forall(i in Rectangle)(height[i] > w -> rotation[i]==false);
% a rectangle with same width and height should not be rotated
constraint forall (i in Rectangle) (width[i] = height[i] -> rotation[i]==false);

constraint cumulative(y, height_r, width_r, w);
constraint cumulative(x, width_r, height_r, h);
%no overlap
constraint diffn(x, y, width_r, height_r); 


%Remove the gap
constraint
forall(r in Rectangle)(
member([0] ++ [x[i] + width_r[i] | i in Rectangle where i != r], x[r]) /\
member([0] ++ [y[i] + height_r[i] | i in Rectangle where i != r], y[r]));

%symmetry breaking constraint
constraint symmetry_breaking_constraint(
  x[biggest()] == 0 /\ y[biggest()] == 0
);

% symmetry breaking
constraint forall(r in Rectangle)(let {array[int] of int: R = [i | i in Rectangle where (width[i]=width[r]
            /\ height[i]=height[r]) \/ (width[i]=height[r] /\ height[i]=width[r])]} 
            in if length(R)>1 /\ min(R)=r then 
            forall(i in index_set(R) where i>1)(
             lex_less([y[R[i-1]],x[R[i-1]]], [y[R[i]],x[R[i]]])
            )
            else true endif
);

%----------- solve ---------------------
solve 
::int_search(y, input_order, indomain_min,complete)
::int_search(x, input_order, indomain_min,complete)
::int_search([h], input_order, indomain_min, complete)
minimize h;




