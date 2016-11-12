module PowerEnjoy

/* ************************* SIGNATURES ************************ */

/** PEOPLE **/
abstract sig Person{}
	sig Passenger extends Person{}
	sig User extends Person{
		status : one UserStatus,	
	}

abstract sig UserStatus{}
	lone sig ActiveUser extends UserStatus{}
	lone sig InactiveUser extends UserStatus{}
	lone sig SearchingUser extends UserStatus{}


/** COMPANY **/
sig Car{
	status:one CarStatus,
	seats : 5
}

abstract sig CarStatus{}
	lone sig CarAvailable extends CarStatus{}
	lone sig CarBooked extends CarStatus{}
	lone sig CarCharging extends CarStatus{}


sig ChargingStation{
	plugs : set Plug
}{#plugs >=1}

sig Plug{
	connectedCar : lone Car
}

/**RIDE**/
sig Ride{
	driver: one User,
	car : one Car,
	passengers: set Passenger
}{#passengers >=0}


sig RideController{
	ride : one Ride,
	fee : one Int,
	discount: lone DiscountType,
}{ fee >=1}

abstract sig DiscountType{}
	lone sig MSODiscount extends DiscountType{}


/** SEARCH **/

sig Search{
	user : one User,
	availableCars : set Car
}


/* ************************ FACTS ************************ */


//An inactive user cannot search nor be active
fact userInactive{
	all u:User | isUserInactive[u] iff not(isUserActive[u] or isUserSearching[u])
}

// A car is involved in maximum one ride
fact carHasOneRide{
	all c:Car | lone r:Ride | c in r.car
}

//Enough seats for all users
fact enoughSpace{
	all r:Ride | peopleInCar[r] =< r.car.seats
}

// User can drive max one car at the time
fact userHasOneRide{
	all u:User | lone r:Ride | u in r.driver
}
//An active user is in a Ride
fact userInRideIsActive{
	all u:User | isUserActive[u] iff isUserInRide[u] 
}

// If an user has searching status he is doing a search
fact searchingUserIsInSomeSearch{
	all u:User | isUserSearching[u] iff isUserInSearch[u]
}

//A user can do only one search
fact oneSearchPerUser{
	no disjoint s1,s2 :Search | s1.user = s2.user
}

// All cars that are available must be displayed in searches
fact carsInSearchAreAvailable{
	all c:Car | all s:Search | isCarAvailable[c] iff c in s.availableCars
}

// A booked car in a Ride must have booked status
fact carInRideIsBooked{
	all c:Car | isCarUsed[c] iff isCarInRide[c]
}

//A chargingCar is in some ChargingStation
fact chargingCarInStation{
	all c:Car | isCarCharging[c] iff isCarInStation[c]
}


// A charging car is plugged into one plug
fact chargingCarIsPluggedIn{
	all c:Car | isCarCharging[c] iff isPlugConnected[c]
}

//A plug belongs to one station
fact plugHasOneStation{
	all p:Plug | one s:ChargingStation | p in s.plugs
}

// A car cannot be plugged into two plugs
fact carHasOnePlug{
	no disjoint p1,p2:Plug | p1.connectedCar = p2.connectedCar
}

//A passenger is in only one car
fact passengerIsAtMostInOneCar{
	no disjoint r1,r2: Ride |some p:Passenger | p in r1.passengers and p in r2.passengers 
}

//All passenger belong to one car
fact allPassenger{
	all p:Passenger | one r:Ride | p in r.passengers
}

//Every ride has exactly one ride controller
fact rideHasController{
	all r:Ride | one c:RideController | r in c.ride
}

//If MSO instance exists than it must be part of at least one ride controller
fact MSOMustBePartOfRideController{
	no m:MSODiscount | some r:RideController | m not in r.discount
}

/* ************************* PREDICATES ************************ */

// Check if the user has active status
pred isUserActive[u:User]{
	some s:ActiveUser | u.status in s
}
// Check if the user has inactive status
pred isUserInactive[u:User]{
	some  s:InactiveUser | u.status in s
}
// Check if the user has searching status
pred isUserSearching[u:User]{
	some s:SearchingUser | u.status in s
}
// Check if the user is the drive of a ride
pred isUserInRide[u:User]{
	some r:Ride | u in r.driver
}
// Check if the user is the one doing a search
pred isUserInSearch[u:User]{
	some s:Search | u in s.user
}
//Checks if the car has booked status
pred isCarUsed [ c:Car]{
	some s:CarBooked | c.status in s
}
//Checks if the car has available status
pred isCarAvailable[c:Car]{
	some s:CarAvailable | c.status in s
}
//Checks if the car has charging status
pred isCarCharging[c:Car]{
	some s:CarCharging | c.status in s
}

//Checks if the car is involved in a ride
pred isCarInRide[c:Car]{
	some r:Ride | c in r.car
}
//Checks if the car is in a charging station
pred isCarInStation[c:Car]{
	some s:ChargingStation | c in s.plugs.connectedCar
}
//Checks if the car is conncted to a plug
pred isPlugConnected[c:Car]{
	some p:Plug | c in p.connectedCar
}

/* ************************* FUNCTIONS ************************ */
//Return the number of people in the car
fun peopleInCar[r:Ride]: Int {
	#r.passengers + 1
}

//Return the number of cars in charge
fun carInCharge[c:ChargingStation]:Int{
	#c.plugs.connectedCar
}

pred showGeneral{
	
	#ChargingStation =2
	#Car = 6
	#Ride =2
	#User =5
	#Search = 1
	#Passenger=3
}
run showGeneral for 10
