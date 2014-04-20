(deffacts packages 
"package no. DepartCity DeliveryCity Size OrderArrivalTime ExpectedDeliveryTime"
(package 50 Orlando KeyWest 5 1 5)
(package 49 Tampa Tallahassee 3 2 4)
(package 48 WestPalm Ft.Myers 5 3 18)
(package 47 Tallahassee LakeCity 5 4 9)
(package 46 KeyWest St.Augustine 15 5 10)
(package 45 Miami Orlando 8 5 15)
(package 44 Ft.Myers KeyWest 6 6 15)
(package 43 Tampa Jacksonville 14 7 17)
(package 42 St.Augustine KeyWest 6 9 25)
(package 41 Tallahassee KeyWest 14 10 32)
(package 40 LakeCity Tallahassee 3 12 19)
(package 39 Tallahassee LakeCity 15 13 18)
(package 38 Miami Tallahassee 7 15 30)
(package 37 St.Augustine Tallahassee 18 15 31)
(package 36 Gainesville Orlando 2 15 23)
(package 35 Miami Ocala 5 16 30)
(package 34 St.Augustine Ft.Myers 14 17 34)
(package 33 Miami KeyWest 4 20 25)
(package 32 Tampa Tallahassee 12 25 40)
(package 31 Miami Gainesville 3 30 45)
(package 30 Orlando LakeCity 15 35 40)
(package 29 WestPalm Ft.Myers 4 35 43)
(package 28 Miami Orlando 15 37 47)
(package 27 Ocala Orlando 4 40 50)
(package 26 Jacksonville KeyWest 11 40 55)
(package 25 St.Augustine Ft.Myers 5 45 58)
(package 24 Tallahassee Gainesville 4 50 60)
(package 23 Jacksonville Tallahassee 3 50 57)
(package 22 Jacksonville KeyWest 11 55 75)
(package 21 KeyWest St.Augustine 3 55 67)
(package 20 WestPalm St.Augustine 5 55 67)
(package 19 Gainesville Tallahassee 12 60 70)
(package 18 St.Augustine Ft.Myers 14 60 75)
(package 17 Tampa Tallahassee 13 62 75)
(package 16 Gainesville Orlando 1 65 75)
(package 15 Miami Ocala 3 70 80)
(package 14 WestPalm Miami 12 70 80)
(package 13 Orlando KeyWest 9 75 85)
(package 12 Ft.Myers KeyWest 5 75 90)
(package 11 Jacksonville Miami 17 77 85)
(package 10 Jacksonville Orlando 4 78 85)
(package 9 Miami Tallahassee 13 78 95)
(package 8 Miami Gainesville 6 87 110)
(package 7 Gainesville Tallahassee 10 90 100)
(package 6 KeyWest St.Augustine 5 94 105)
(package 5 WestPalm St.Augustine 14 94 100)
(package 4 Jacksonville KeyWest 5 95 110)
(package 3 St.Augustine Ft.Myers 12 95 117)
(package 2 Gainesville Jacksonville 4 100 120)
(package 1 Orlando Jacksonville 12 100 120)
)

(deffacts trucks
"truck no. currentLoc Destination AvailSpace CurrentTime Action Package"
(truck 1 Orlando none 5 0 idle none)
(truck 2 Orlando none 5 0 idle none)
(truck 3 Orlando none 10 0 idle none)
(truck 4 Orlando none 10 0 idle none)
(truck 5 Orlando none 15 0 idle none)
(truck 6 Orlando none 15 0 idle none)
(truck 7 Orlando none 20 0 idle none)
)

(deffacts citytable2
(city Tallahassee to Tallahassee 0 LakeCity 2 Jacksonville 3 Gainesville 3 St.Augustine 4 Orlando 5 WestPalm 7 Ocala 4 Tampa 6 Ft.Myers 8 Miami 9 KeyWest 12)
(city LakeCity to Tallahassee 2 LakeCity 0 Jacksonville 1 Gainesville 1 St.Augustine 2 Orlando 3 WestPalm 5 Ocala 2 Tampa 4 Ft.Myers 6 Miami 7 KeyWest 10)
(city Jacksonville to Tallahassee 3 LakeCity 1 Jacksonville 0 Gainesville 2 St.Augustine 1 Orlando 3 WestPalm 4 Ocala 3 Tampa 4 Ft.Myers 6 Miami 6 KeyWest 9)
(city Gainesville to Tallahassee 3 LakeCity 1 Jacksonville 2 Gainesville 0 St.Augustine 1 Orlando 2 WestPalm 4 Ocala 1 Tampa 3 Ft.Myers 5 Miami 6 KeyWest 10)
(city St.Augustine to Tallahassee 4 LakeCity 2 Jacksonville 1 Gainesville 1 St.Augustine 0 Orlando 2 WestPalm 3 Ocala 2 Tampa 3 Ft.Myers 5 Miami 5 KeyWest 8)
(city Orlando to Tallahassee 5 LakeCity 3 Jacksonville 3 Gainesville 2 St.Augustine 2 Orlando 0 WestPalm 3 Ocala 1 Tampa 1 Ft.Myers 3 Miami 5 KeyWest 8)
(city WestPalm to Tallahassee 7 LakeCity 5 Jacksonville 4 Gainesville 4 St.Augustine 3 Orlando 3 WestPalm 0 Ocala 4 Tampa 4 Ft.Myers 3 Miami 2 KeyWest 5)
(city Ocala to Tallahassee 4 LakeCity 2 Jacksonville 3 Gainesville 1 St.Augustine 2 Orlando 1 WestPalm 4 Ocala 0 Tampa 2 Ft.Myers 4 Miami 6 KeyWest 9)
(city Tampa to Tallahassee 6 LakeCity 4 Jacksonville 4 Gainesville 3 St.Augustine 3 Orlando 1 WestPalm 4 Ocala 2 Tampa 0 Ft.Myers 2 Miami 6 KeyWest 9)
(city Ft.Myers to Tallahassee 8 LakeCity 6 Jacksonville 6 Gainesville 5 St.Augustine 5 Orlando 3 WestPalm 3 Ocala 4 Tampa 2 Ft.Myers 0 Miami 5 KeyWest 8)
(city Miami to Tallahassee 9 LakeCity 7 Jacksonville 6 Gainesville 6 St.Augustine 5 Orlando 5 WestPalm 2 Ocala 6 Tampa 6 Ft.Myers 5 Miami 0 KeyWest 3)
(city KeyWest to Tallahassee 12 LakeCity 10 Jacksonville 9 Gainesville 10 St.Augustine 8 Orlando 8 WestPalm 5 Ocala 9 Tampa 9 Ft.Myers 8 Miami 3 KeyWest 0)
)
