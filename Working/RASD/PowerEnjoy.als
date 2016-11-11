module PowerEnjoy


/* ************************* SIGNATURES ************************ */


/** PEOPLE **/
abstract sig Person{}
sig Passenger extends Person{}
sig User extends Person{
	status : one UserStatus,
}

abstract sig UserStatus{}
sig ActiveUser extends UserStatus{}
sig InactiveUser extends UserStatus{}
sig SearchingUser extends UserStatus{}

/** COMPANY **/

sig Car{
	status:one CarStatus,
	seats : one Int
}

abstract sig CarStatus{}
sig CarAvailable extends CarStatus{}
sig CarBooked extends CarStatus{}
sig CarCharging extends CarStatus{}


sig ChargingStation{
	plugs : set Plug
}

sig Plug{
	connectedCar : lone Car
}

/**RIDE**/

sig Ride{
	driver: one User,
	car : one Car,
	passengers: set Passenger
}{#passengers >=0}

sig Search{
	user : one User,
	availableCars : set Car
}{#availableCars >=0}


/* ************************ FACTS ************************ */

// A car is involved in only max ride
fact carHasOneRide{
	all c:Car | lone r:Ride | c in r.car
}
// User can drive max one car at the time
fact userHasOneRide{
	all u:User | lone r:Ride | u in r.driver
}
//An active user is in a Ride
fact userInRideIsActive{
	all u:User | isUserActive[u] iff isUserInRide[u]
}
fact SearchingUser{
	all u : User | isUserSearching[u] iff !(isUserActive[u] or isUserInactive[u])
}
// A booked car in a Ride
fact carInRideIsBooked{
	all c:Car | isCarUsed[c] iff isCarInRide[c]
}

//A chargingCar is in some ChargingStation
fact chargingCarInStation{
	all c:Car | isCarCharging[c] iff isCarInStation[c]
}
// Number of plug constraints
fact minNumOfPlugs{
	all c:ChargingStation| #c.plugs >=1 and #c.plugs <=5
}

// Enough seats for all people in the car
fact enoughSpace{
	all r:Ride | peopleInCar[r] =< r.car.seats
}

// A car is available if it is not booked nor charging
fact availableCar{
	all c:Car | isCarAvailable[c] iff (!(isCarCharging[c] or isCarUsed[c]))
}
// Checks if the car's number of seats is within the limit
fact numberOfSeats{
	all c:Car |  carSeatsNumberAccettable[c.seats]
}

// A charging car is plugged into one plug
fact chargingCarIsPluggedIn{
	all c:Car | isCarCharging[c] iff isPlugConnected[c]
}

//A plug belongs to one station
fact plugHasOneStation{
	all p:Plug | one s:ChargingStation | p in s.plugs
}

/* ************************* PREDICATES ************************ */


pred isUserActive[u:User]{
	some s:ActiveUser | u.status in s
}

pred isUserInactive[u:User]{
	some  s:InactiveUser | u.status in s
}

pred isUserSearching[u:User]{
	some s:SearchingUser | u.status in s
}

pred isUserInRide[u:User]{
	some r:Ride | u in r.driver
}

pred isCarUsed [ c:Car]{
	some s:CarBooked | c.status in s
}
pred isCarAvailable[c:Car]{
	some s:CarAvailable | c.status in s
}
pred isCarCharging[c:Car]{
	some s:CarCharging | c.status in s
}

pred isCarInRide[c:Car]{
	some r:Ride | c in r.car
}

pred isCarInStation[c:Car]{
	some s:ChargingStation | c in s.plugs.connectedCar
}
// We considered only cars with 4 or 5 seats.
pred carSeatsNumberAccettable[n:Int]{
	n >3 and n<6
}
 
pred isPlugConnected[c:Car]{
	some p:Plug | c in p.connectedCar
}


pred isSharedRide[r:Ride]{
	#r.passengers >1
}


//bookingrequest

/* ************************* FUNCTIONS ************************ */

fun peopleInCar[r:Ride]: Int {
	r.passengers + 1
}

fun carInCharge[c:ChargingStation]:Int{
	#c.plugs.connectedCar
}


pred showGeneral{
	#ChargingStation =2
	#Car = 3
	#Ride =2
	#User =3


}
run showGeneral
