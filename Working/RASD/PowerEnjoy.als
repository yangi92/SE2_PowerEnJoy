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
	seats : one Int
}

abstract sig CarStatus{}
lone sig CarAvailable extends CarStatus{}
lone sig CarBooked extends CarStatus{}
lone sig CarCharging extends CarStatus{}


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

sig RideController{
	ride : one Ride,
	fee : one Int,
	discount: lone DiscountType,
	penalty: lone Penalty
}

abstract sig DiscountType{}
lone sig MSODiscount extends DiscountType{}
lone sig batteryDiscount extends DiscountType{}

abstract sig Penalty{}
lone sig distancePenalty extends Penalty{}

/** SEARCH **/
sig Search{
	user : one User,
	availableCars : set Car
}


/* ************************ FACTS ************************ */

// Checks if the car's number of seats is within the limit
fact numberOfSeatsIsFine{
	all c:Car |  carSeatsNumberAccettable[c.seats]
}

// A car is involved in only max ride
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

// If an user has searching status he is doing one search
fact searchingUserIsInSomeSearch{
	all u:User | isUserSearching[u] iff isUserInSearch[u]
}

//A user can do only one search
fact oneSearchPerUser{
	no disjoint s1,s2 :Search | s1.user = s2.user
}

//An inactive user cannot search nor be active
fact userInactive{
	all u:User | isUserInactive[u] iff not(isUserActive[u] or isUserSearching[u])
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

// Number of plug constraints
fact minNumOfPlugs{
	all c:ChargingStation| #c.plugs >=1 and #c.plugs <=5
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

fact rideHasController{
	all r:Ride | one c:RideController | r in c.ride
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
pred isUserInSearch[u:User]{
	some s:Search | u in s.user
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


//BOOKINREQUEST  IMP
// TOGLIERE RIDE MANAGER?
// TOGLIERE BATTERY LEVEL

/* ************************* FUNCTIONS ************************ */

fun peopleInCar[r:Ride]: Int {
	r.passengers + 1
}

fun carInCharge[c:ChargingStation]:Int{
	#c.plugs.connectedCar
}


pred showGeneral{
	
	#ChargingStation =2
	#Car = 5
	#Ride =2
	#User =5
	#Search = 1
	#Passenger=3
}
run showGeneral for 8
