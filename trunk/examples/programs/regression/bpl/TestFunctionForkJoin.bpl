//#Safe
/*
 * Author: lars.nitzke@outlook.com
 * Date: 24.04.2018
 */


function myFunc(in: int) returns (res : bool);

procedure proc();

implementation proc()
{
  var x: int;
  x := 7;
  fork x myFunc (7);
  join x;
}





  
