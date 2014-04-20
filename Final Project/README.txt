What the zip file includes:

Code:
version1.clp -- code of part1
version2.clp -- code of part2

Data Sets:
dataset1.clp -- Data set 1
dataset2.clp -- Data set 2
dataset3.clp -- Data set 3

Outputs:
V1_DS1.txt -- output of data set 1 running version1
V1_DS2.txt -- output of data set 2 running version1
V1_DS3.txt -- output of data set 3 running version1
V2_DS1.txt -- output of data set 1 running version2
V2_DS2.txt -- output of data set 2 running version2
V2_DS3.txt -- output of data set 3 running version2

How to execute:
(load "version1.clp")
(load "dataset1.clp")
(reset)
(run)
Shows the output same as V1_DS1.txt

(load "version1.clp")
(load "dataset2.clp")
(reset)
(run)
Shows the output same as V1_DS2.txt

(load "version1.clp")
(load "dataset3.clp")
(reset)
(run)
Shows the output same as V1_DS3.txt

(load "version2.clp")
(load "dataset1.clp")
(reset)
(run)
Shows the output same as V2_DS1.txt

(load "version2.clp")
(load "dataset2.clp")
(reset)
(run)
Shows the output same as V2_DS2.txt

(load "version2.clp")
(load "dataset3.clp")
(reset)
(run)
Shows the output same as V2_DS3.txt

About data files:
Within each dataset clip file, the information of packages and trucks are encoding using deffacts with the original forms. Maps' data are precomputed as the form like (city CITY_A to CITY_B dist1 CITY_C dist2 CITY_D dist3 ...). I set all the trucks start at Orlando.


